# pip install ezdxf shapely
import math
from collections import defaultdict
import os
import random
import threading
import traceback
import tkinter as tk
import functools
from tkinter import filedialog, messagebox, ttk

import ezdxf
from shapely.geometry import Polygon, box
from shapely.affinity import translate, rotate
from shapely.prepared import prep
from shapely.strtree import STRtree

# ---------------- Settings ----------------
EXCLUDE_LAYER_KEYWORDS = ("DIM", "TEXT", "CONSTRUCTION")
TOL = 0.01  # mm snap tolerance for stitching loose LINE/ARC loops
CURVE_MAX_SEG_MM = 2.0  # mm max segment length when flattening curves (smaller = smoother)

SHEETS = {
    "2000 x 1000": (2000, 1000),
    "2500 x 1250": (2500, 1250),
    "3000 x 1500": (3000, 1500),
}

DEFAULT_MARGIN = 10.0
DEFAULT_SPACING = 10.0

# Set True to print nesting improvement diagnostics to console
DEBUG_NESTING = False

DEBUG_DXF = False  # Set True to show full traceback on DXF import errors
DEBUG_PLACEMENT = False  # Enable detailed placement rejection stats
THICKNESSES = [2, 3, 4, 5, 6, 8, 10, 12]

# ---- EDIT THESE TO MATCH YOUR LASER / GAS / NOZZLE / POWER ----
# Units: mm/min (placeholders)
CUT_SPEED_TABLE = {
    "Mild Steel": {
        2: 6500, 3: 5000, 4: 4200, 5: 3600, 6: 3000, 8: 2300, 10: 1850, 12: 1550
    },
    "Stainless Steel": {
        2: 5200, 3: 4200, 4: 3600, 5: 3100, 6: 2600, 8: 2050, 10: 1700, 12: 1400
    },
}
# ------------------------------------------


# ---------------- Geometry helpers ----------------
def layer_excluded(layer_name: str) -> bool:
    up = (layer_name or "").upper()
    return any(k in up for k in EXCLUDE_LAYER_KEYWORDS)


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def keypt(p, tol=TOL):
    return (round(p[0] / tol) * tol, round(p[1] / tol) * tol)


def arc_len(e):
    ang = math.radians((e.dxf.end_angle - e.dxf.start_angle) % 360.0)
    return abs(e.dxf.radius * ang)


def polygon_area(points):
    if len(points) < 3:
        return 0.0
    s = 0.0
    for i in range(len(points)):
        x1, y1 = points[i]
        x2, y2 = points[(i + 1) % len(points)]
        s += x1 * y2 - x2 * y1
    return 0.5 * s


def polygon_bbox(points):
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    return (min(xs), min(ys), max(xs), max(ys))


def bbox_contains(b1, b2):
    return b1[0] <= b2[0] and b1[1] <= b2[1] and b1[2] >= b2[2] and b1[3] >= b2[3]


def point_in_poly(pt, poly):
    x, y = pt
    inside = False
    n = len(poly)
    if n < 3:
        return False
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        if ((y1 > y) != (y2 > y)):
            xinters = (x2 - x1) * (y - y1) / (y2 - y1 + 1e-18) + x1
            if x < xinters:
                inside = not inside
    return inside


def is_closed_entity(e) -> bool:
    t = e.dxftype()
    if t in ("CIRCLE", "ELLIPSE"):
        return True
    if t in ("LWPOLYLINE", "POLYLINE"):
        return bool(getattr(e, "closed", False))
    if t == "SPLINE":
        return bool(getattr(e, "closed", False))
    return False


def lwpoly_points(e):
    """
    Return polyline points, expanding LWPOLYLINE bulge arcs into short segments.
    This improves visual fidelity and nesting tightness for curved profiles.
    """
    # Prefer bulge-aware points where available.
    try:
        pts_b = list(e.get_points("xyb"))
    except Exception:
        pts_b = []

    # Fallback to plain xy
    if not pts_b:
        pts = list(e.get_points("xy"))
        if len(pts) >= 2 and dist(pts[0], pts[-1]) < 1e-9:
            pts = pts[:-1]
        return pts

    def arc_points_from_bulge(p1, p2, bulge, max_seg=CURVE_MAX_SEG_MM):
        # bulge = tan(theta/4), sign indicates direction
        if abs(bulge) < 1e-12:
            return [p1, p2]
        x1, y1 = p1
        x2, y2 = p2
        chord = math.hypot(x2 - x1, y2 - y1)
        if chord < 1e-9:
            return [p1, p2]

        theta = 4.0 * math.atan(bulge)  # signed included angle
        sin_half = math.sin(theta / 2.0)
        if abs(sin_half) < 1e-12:
            return [p1, p2]

        r = (chord / 2.0) / abs(sin_half)

        # Midpoint of chord
        mx, my = (x1 + x2) / 2.0, (y1 + y2) / 2.0

        # Distance from midpoint to center along the normal
        h = math.sqrt(max(0.0, r * r - (chord / 2.0) ** 2))

        # Unit normal (perpendicular to chord)
        ux, uy = (x2 - x1) / chord, (y2 - y1) / chord
        nx, ny = -uy, ux

        # Choose center side based on sign of bulge
        cx = mx + (h if bulge > 0 else -h) * nx
        cy = my + (h if bulge > 0 else -h) * ny

        a1 = math.atan2(y1 - cy, x1 - cx)
        a2 = math.atan2(y2 - cy, x2 - cx)

        # Ensure we move from a1 toward a2 with the correct signed sweep (theta)
        sweep = theta
        # Build points
        arc_len = abs(sweep) * r
        nseg = max(1, int(math.ceil(arc_len / max(1e-9, max_seg))))
        out = []
        for i in range(nseg + 1):
            t = i / nseg
            ang = a1 + sweep * t
            out.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))
        return out

    # Build expanded point list
    out_pts = []
    n = len(pts_b)
    if n == 0:
        return []
    closed = bool(getattr(e, "closed", False))
    seg_count = n if closed else (n - 1)

    for i in range(seg_count):
        t1 = pts_b[i]
        t2 = pts_b[(i + 1) % n]
        x1, y1 = t1[0], t1[1]
        x2, y2 = t2[0], t2[1]
        b1 = float(t1[-1]) if len(t1) >= 3 else 0.0  # bulge is last item when present
        p1 = (x1, y1)
        p2 = (x2, y2)
        arc_pts = arc_points_from_bulge(p1, p2, b1)
        if not out_pts:
            out_pts.extend(arc_pts)
        else:
            # avoid duplicating the join point
            out_pts.extend(arc_pts[1:])

    # Remove duplicate closing point if present
    if len(out_pts) >= 2 and dist(out_pts[0], out_pts[-1]) < 1e-9:
        out_pts = out_pts[:-1]
    return out_pts


def poly_points(e):
    pts = [(v.dxf.location.x, v.dxf.location.y) for v in e.vertices()]
    if len(pts) >= 2 and dist(pts[0], pts[-1]) < 1e-9:
        pts = pts[:-1]
    return pts


def ellipse_len_approx(e, steps=200):
    pts = [e.point(i / steps) for i in range(steps + 1)]
    xy = [(p.x, p.y) for p in pts]
    return sum(dist(xy[i], xy[i + 1]) for i in range(steps))


def spline_len_approx(e, steps=400):
    curve = e.construction_tool()
    t0, t1 = curve.domain
    ts = [t0 + (t1 - t0) * i / steps for i in range(steps + 1)]
    pts = [curve.point(t) for t in ts]
    xy = [(p.x, p.y) for p in pts]
    return sum(dist(xy[i], xy[i + 1]) for i in range(steps))


def rotate_pt_90(p):
    x, y = p
    return (-y, x)


def normalise_points_to_origin(points):
    bx = polygon_bbox(points)
    return [(p[0] - bx[0], p[1] - bx[1]) for p in points]


def translate_points(points, dx, dy):
    return [(p[0] + dx, p[1] + dy) for p in points]


def nearest_vertex(points, from_pt):
    best = points[0]
    best_d = dist(best, from_pt)
    for p in points[1:]:
        d = dist(p, from_pt)
        if d < best_d:
            best_d = d
            best = p
    return best, best_d


def allows_90(rot_mode: str) -> bool:
    return rot_mode in ("0/90", "0/90/180/270")


def allowed_angles(rot_mode: str):
    if rot_mode == "0 only":
        return [0]
    if rot_mode == "0/90":
        return [0, 90]
    if rot_mode == "0/90/180/270":
        return [0, 90, 180, 270]
    return [0, 90]


# ---------------- Contours + holes-first routing ----------------
class Contour:
    def __init__(self, cid, kind, length_mm, area_mm2, points, bbox, meta=None):
        self.id = cid
        self.kind = kind
        self.length_mm = float(length_mm)
        self.area_mm2 = float(area_mm2)
        self.points = points
        self.bbox = bbox
        self.meta = meta or {}
        self.parent = None
        self.children = []

    def rep_point(self):
        return self.points[0] if self.points else (0.0, 0.0)

    def start_point_near(self, from_pt):
        if self.kind == "CIRCLE":
            cx, cy = self.meta["center"]
            r = self.meta["radius"]
            vx, vy = from_pt[0] - cx, from_pt[1] - cy
            vlen = math.hypot(vx, vy)
            if vlen < 1e-9:
                return (cx + r, cy)
            return (cx + r * vx / vlen, cy + r * vy / vlen)
        if not self.points:
            return (0.0, 0.0)
        p, _ = nearest_vertex(self.points, from_pt)
        return p


def extract_contours(dxf_path: str):
    doc = ezdxf.readfile(dxf_path)
    msp = doc.modelspace()

    contours = []
    cid = 0

    # Stitch graph for loose LINE/ARC loops
    adj = {}
    edge_id = 0

    def add_edge(a, b, ln, eid, kind="LINE", meta=None):
        """Add an undirected edge between snapped nodes a<->b.

        kind: "LINE" or "ARC"
        meta: dict with extra parameters for ARC reconstruction (center, radius, start_angle, end_angle)
        """
        adj.setdefault(a, []).append((b, ln, eid, kind, meta or {}))
        adj.setdefault(b, []).append((a, ln, eid, kind, meta or {}))

    for e in msp:
        layer = getattr(e.dxf, "layer", "")
        if layer_excluded(layer):
            continue

        t = e.dxftype()

        if is_closed_entity(e):
            if t == "LWPOLYLINE":
                pts = lwpoly_points(e)
                if len(pts) >= 3:
                    area = abs(polygon_area(pts))
                    bbox = polygon_bbox(pts)
                else:
                    area, bbox = 0.0, (0, 0, 0, 0)
                ln = e.length()
                contours.append(Contour(cid, "LWPOLYLINE", ln, area, pts, bbox))
                cid += 1

            elif t == "POLYLINE":
                pts = poly_points(e)
                if len(pts) >= 3:
                    area = abs(polygon_area(pts))
                    bbox = polygon_bbox(pts)
                else:
                    area, bbox = 0.0, (0, 0, 0, 0)
                try:
                    ln = e.length()
                except Exception:
                    ln = sum(dist(pts[i], pts[(i + 1) % len(pts)]) for i in range(len(pts))) if pts else 0.0
                contours.append(Contour(cid, "POLYLINE", ln, area, pts, bbox))
                cid += 1

            elif t == "CIRCLE":
                cx, cy = e.dxf.center.x, e.dxf.center.y
                r = e.dxf.radius
                ln = 2 * math.pi * r
                area = math.pi * r * r
                nseg = max(48, int(math.ceil((2 * math.pi * r) / max(1e-9, CURVE_MAX_SEG_MM))))
                pts = [(cx + r * math.cos(2 * math.pi * i / nseg), cy + r * math.sin(2 * math.pi * i / nseg)) for i in range(nseg)]
                bbox = (cx - r, cy - r, cx + r, cy + r)
                contours.append(Contour(cid, "CIRCLE", ln, area, pts, bbox, meta={"center": (cx, cy), "radius": r}))
                cid += 1

            elif t == "ELLIPSE":
                ln = ellipse_len_approx(e)
                nseg = max(96, int(math.ceil(max(1.0, ln) / max(1e-9, CURVE_MAX_SEG_MM))))
                pts = [(p.x, p.y) for p in [e.point(i / nseg) for i in range(nseg)]]
                area = abs(polygon_area(pts))
                bbox = polygon_bbox(pts)
                contours.append(Contour(cid, "ELLIPSE", ln, area, pts, bbox))
                cid += 1

            elif t == "SPLINE":
                ln = spline_len_approx(e)
                curve = e.construction_tool()
                t0, t1 = curve.domain
                pts = []
                steps = max(140, int(math.ceil(max(1.0, ln) / max(1e-9, CURVE_MAX_SEG_MM))))
                for i in range(steps):
                    tpar = t0 + (t1 - t0) * i / steps
                    p = curve.point(tpar)
                    pts.append((p.x, p.y))
                area = abs(polygon_area(pts))
                bbox = polygon_bbox(pts)
                contours.append(Contour(cid, "SPLINE", ln, area, pts, bbox))
                cid += 1

            continue

        if t == "LINE":
            s = e.dxf.start
            en = e.dxf.end
            a = keypt((s.x, s.y))
            b = keypt((en.x, en.y))
            add_edge(a, b, dist(a, b), edge_id, kind="LINE")
            edge_id += 1

        elif t == "ARC":
            center = (e.dxf.center.x, e.dxf.center.y)
            r = e.dxf.radius
            sa_deg = float(e.dxf.start_angle)
            ea_deg = float(e.dxf.end_angle)
            sa = math.radians(sa_deg)
            ea = math.radians(ea_deg)
            p1 = (center[0] + r * math.cos(sa), center[1] + r * math.sin(sa))
            p2 = (center[0] + r * math.cos(ea), center[1] + r * math.sin(ea))
            a = keypt(p1)
            b = keypt(p2)
            add_edge(a, b, arc_len(e), edge_id, kind="ARC",
                     meta={"center": center, "radius": r, "start_angle": sa_deg, "end_angle": ea_deg})
            edge_id += 1

    # stitched loops: degree-2 components
    visited = set()
    for node in list(adj.keys()):
        if node in visited:
            continue
        stack = [node]
        comp = []
        visited.add(node)
        while stack:
            n = stack.pop()
            comp.append(n)
            for nb, *_rest in adj.get(n, []):
                if nb not in visited:
                    visited.add(nb)
                    stack.append(nb)

        if len(comp) <= 2:
            continue
        if not all(len(adj.get(n, [])) == 2 for n in comp):
            continue

        seen_eids = set()
        ln = 0.0
        for n in comp:
            for _, eln, eid, *_rest in adj[n]:
                if eid not in seen_eids:
                    seen_eids.add(eid)
                    ln += eln

        # Reconstruct an ordered loop (degree-2 graph), preserving ARC curvature when possible.
        def sample_arc(meta, p_start, p_end, max_seg=CURVE_MAX_SEG_MM):
            try:
                cx, cy = meta["center"]
                r = float(meta["radius"])
                sa = math.radians(float(meta["start_angle"]))
                ea = math.radians(float(meta["end_angle"]))
            except Exception:
                return [p_start, p_end]

            # DXF ARC is CCW from start_angle to end_angle (mod 360)
            sweep = (ea - sa) % (2 * math.pi)
            if sweep < 1e-12:
                sweep = 2 * math.pi

            arc_len_est = abs(sweep) * r
            nseg = max(2, int(math.ceil(arc_len_est / max(1e-9, max_seg))))
            out = []
            for i in range(nseg + 1):
                t = i / nseg
                ang = sa + sweep * t
                out.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))

            # Ensure endpoints match our snapped graph direction; reverse if closer
            if dist(out[0], p_start) + dist(out[-1], p_end) > dist(out[0], p_end) + dist(out[-1], p_start):
                out.reverse()
            return out

        # Walk the cycle to get ordered points
        start_n = comp[0]
        ordered = [start_n]
        prev = None
        curr = start_n
        used_eids = set()

        while True:
            nbrs = adj.get(curr, [])
            # pick the neighbor that is not prev
            nxt = None
            nxt_info = None
            for info in nbrs:
                nb, eln, eid, kind, meta = info
                if eid in used_eids:
                    continue
                if prev is None or nb != prev:
                    nxt = nb
                    nxt_info = info
                    break
            if nxt is None:
                break
            nb, eln, eid, kind, meta = nxt_info
            used_eids.add(eid)

            p_start = curr
            p_end = nb
            if kind == "ARC":
                pts_seg = sample_arc(meta, p_start, p_end)
                ordered.extend(pts_seg[1:])  # avoid dup at join
            else:
                ordered.append(p_end)

            prev, curr = curr, nb
            if curr == start_n:
                break

        # Remove duplicate final point if closed
        if len(ordered) >= 2 and dist(ordered[0], ordered[-1]) < 1e-9:
            ordered = ordered[:-1]

        pts = ordered
        area = abs(polygon_area(pts)) if len(pts) >= 3 else 0.0
        bbox = polygon_bbox(pts) if len(pts) >= 2 else (0, 0, 0, 0)

        contours.append(Contour(cid, "STITCHED", ln, area, pts, bbox))
        cid += 1

    return contours


def build_containment_tree(contours):
    for c in contours:
        c.parent = None
        c.children = []

    sorted_by_area = sorted(contours, key=lambda x: x.area_mm2 if x.area_mm2 > 0 else float("inf"))
    for child in contours:
        pt = child.rep_point()
        best_parent = None
        best_area = float("inf")

        for cand in sorted_by_area:
            if cand.id == child.id:
                continue
            if cand.area_mm2 > 0 and child.area_mm2 > 0 and cand.area_mm2 <= child.area_mm2:
                continue
            if not bbox_contains(cand.bbox, child.bbox):
                continue
            if point_in_poly(pt, cand.points):
                if cand.area_mm2 > 0 and cand.area_mm2 < best_area:
                    best_parent = cand
                    best_area = cand.area_mm2

        child.parent = best_parent

    for c in contours:
        if c.parent is not None:
            c.parent.children.append(c)

    return [c for c in contours if c.parent is None]


def holes_first_route(roots, start_xy=(0.0, 0.0)):
    travel_mm = 0.0
    current = start_xy

    def visit(node, current_pt):
        nonlocal travel_mm
        children = node.children[:]
        while children:
            best_i = None
            best_d = float("inf")
            best_sp = None
            for i, ch in enumerate(children):
                sp = ch.start_point_near(current_pt)
                d = dist(current_pt, sp)
                if d < best_d:
                    best_d = d
                    best_i = i
                    best_sp = sp
            ch = children.pop(best_i)
            travel_mm += best_d
            current_pt = best_sp
            current_pt = visit(ch, current_pt)

        sp = node.start_point_near(current_pt)
        travel_mm += dist(current_pt, sp)
        return sp  # closed approx

    pending = roots[:]
    while pending:
        best_i = None
        best_d = float("inf")
        best_sp = None
        for i, r in enumerate(pending):
            sp = r.start_point_near(current)
            d = dist(current, sp)
            if d < best_d:
                best_d = d
                best_i = i
                best_sp = sp
        r = pending.pop(best_i)
        travel_mm += best_d
        current = best_sp
        current = visit(r, current)

    return travel_mm, current


# ---------------- Part model ----------------
def compute_part_model(dxf_path: str):
    contours_raw = extract_contours(dxf_path)
    if not contours_raw:
        raise ValueError("No closed contours detected after filtering.")

    cut_len = sum(c.length_mm for c in contours_raw)
    pierces = len(contours_raw)

    roots = build_containment_tree(contours_raw)
    if not roots:
        raise ValueError("No root contours detected.")

    outer = max(roots, key=lambda c: c.area_mm2)
    outer_poly = outer.points[:] if outer.points else []
    if len(outer_poly) < 3:
        raise ValueError("Outer contour not suitable for nesting footprint.")

    outer_bbox_raw = polygon_bbox(outer_poly)
    dx0, dy0 = -outer_bbox_raw[0], -outer_bbox_raw[1]

    outer_norm = translate_points(outer_poly, dx0, dy0)
    outer_norm = normalise_points_to_origin(outer_norm)
    ob = polygon_bbox(outer_norm)
    w = ob[2] - ob[0]
    h = ob[3] - ob[1]
    if w <= 0 or h <= 0:
        raise ValueError("Outer contour bbox invalid.")

    contours_norm = []
    for c in contours_raw:
        pts = translate_points(c.points, dx0, dy0)
        bb = polygon_bbox(pts) if len(pts) >= 2 else (0, 0, 0, 0)
        meta = dict(c.meta)
        if c.kind == "CIRCLE" and "center" in meta:
            cx, cy = meta["center"]
            meta["center"] = (cx + dx0, cy + dy0)
        contours_norm.append(Contour(c.id, c.kind, c.length_mm, c.area_mm2, pts, bb, meta=meta))

    return {
        "path": dxf_path,
        "name": os.path.basename(dxf_path),
        "cut_len": cut_len,
        "pierces": pierces,
        "outer_poly_norm": outer_norm,
        "outer_w": w,
        "outer_h": h,
        "contours_norm": contours_norm,
        "qty": 1,
        "rotation_mode": "0/90/180/270",
        "poly_cache": None,
    }


# ---------------- Bounding box nesting (fast) ----------------
class FreeRect:
    def __init__(self, x, y, w, h):
        self.x, self.y, self.w, self.h = x, y, w, h


def rect_fits(fr: FreeRect, w, h):
    return w <= fr.w and h <= fr.h


def split_free_rect(fr: FreeRect, px, py, pw, ph):
    new = []
    if py > fr.y:
        new.append(FreeRect(fr.x, fr.y, fr.w, py - fr.y))
    if py + ph < fr.y + fr.h:
        new.append(FreeRect(fr.x, py + ph, fr.w, (fr.y + fr.h) - (py + ph)))
    if px > fr.x:
        new.append(FreeRect(fr.x, py, px - fr.x, ph))
    if px + pw < fr.x + fr.w:
        new.append(FreeRect(px + pw, py, (fr.x + fr.w) - (px + pw), ph))
    return new


def prune_free_rects(free_rects):
    pruned = []
    for i, a in enumerate(free_rects):
        contained = False
        for j, b in enumerate(free_rects):
            if i == j:
                continue
            if a.x >= b.x and a.y >= b.y and a.x + a.w <= b.x + b.w and a.y + a.h <= b.y + b.h:
                contained = True
                break
        if not contained and a.w > 0 and a.h > 0:
            pruned.append(a)
    return pruned


def pack_rectangles_one_sheet(sheet_w, sheet_h, items, scan_variant=0):
    free = [FreeRect(0, 0, sheet_w, sheet_h)]
    placements = []

    items_sorted = sorted(items, key=lambda it: it["w"] * it["h"], reverse=True)

    for it in items_sorted:
        allow90 = it["allow_rotate_90"]

        best = None
        best_score = None

        for fr in free:
            for rotated in ([False, True] if allow90 else [False]):
                rw, rh = (it["h"], it["w"]) if rotated else (it["w"], it["h"])
                if not rect_fits(fr, rw, rh):
                    continue
                leftover = (fr.w * fr.h) - (rw * rh)
                short_side = min(fr.w - rw, fr.h - rh)
                long_side = max(fr.w - rw, fr.h - rh)

                if scan_variant == 0:
                    score = (leftover, short_side, long_side)
                elif scan_variant == 1:
                    score = (short_side, leftover, long_side)
                else:
                    score = (long_side, leftover, short_side)

                if best is None or score < best_score:
                    best = (fr, rw, rh, rotated)
                    best_score = score

        if best is None:
            if DEBUG_PLACEMENT:
                reject_stats['part_unplaced'] += 1
            continue

        fr, rw, rh, rotated = best
        px, py = fr.x, fr.y
        placements.append({"part_id": it["part_id"], "x": px, "y": py, "w": rw, "h": rh, "rotated": rotated})

        new_free = []
        for f in free:
            if px + rw <= f.x or px >= f.x + f.w or py + rh <= f.y or py >= f.y + f.h:
                new_free.append(f)
            else:
                new_free.extend(split_free_rect(f, px, py, rw, rh))
        free = prune_free_rects(new_free)
    # --- Post-pass compaction (improves offcut quality, preserves spacing guarantees) ---
    # This is safe: every move is collision-checked against buffered polys, so spacing/non-overlap stays enforced.
    compact_placements(placements, usable_rect, usable_prep, passes=3)

    # --- Local improvement: reinsert small parts into pockets (safe, collision-checked) ---
    improve_by_reinsertion(placements, parts, usable_rect, usable_prep, passes=1)

    placed_counts = {}
    for pl in placements:
        placed_counts[pl["part_id"]] = placed_counts.get(pl["part_id"], 0) + 1

    remaining = []
    counts_left = dict(placed_counts)
    for it in items_sorted:
        pid = it["part_id"]
        if counts_left.get(pid, 0) > 0:
            counts_left[pid] -= 1
        else:
            remaining.append(it)

    if DEBUG_PLACEMENT:
        try:
            print(f"[Placement debug summary] items={len(items)} pids={pids_processed} tested={candidates_tested} placed={len(placements)} remaining={len(remaining)} unplaced_parts={reject_stats.get('part_unplaced',0)}")
            for k in sorted(reject_stats.keys()):
                print(f"  {k}: {reject_stats[k]}")
        except Exception:
            pass
    return placements, remaining

def pack_polygons_one_sheet(parts, items, usable_w, usable_h, spacing_mm, scan_variant=0):
    usable_rect = box(0, 0, usable_w, usable_h)
    # Use a tiny positive buffer so parts that *touch* the usable boundary are allowed.
    # (prepared.contains() is strict and rejects boundary-touching geometries.)
    usable_prep = prep(usable_rect.buffer(1e-6))

    placed_polys = []
    placements = []

    strtree = None

    def rebuild_index():
        nonlocal strtree
        strtree = STRtree(placed_polys) if placed_polys else None

    rebuild_index()

    sheet_minx, sheet_miny, sheet_maxx, sheet_maxy = usable_rect.bounds
    current_max_y = 0.0



    reject_stats = defaultdict(int)
    candidates_tested = 0
    pids_processed = 0
    placed_counts_so_far = {}
    def score_candidate(x, y, poly_bounds):
        # Prefer low envelope (Y), then bottom-left, then tighter X extent.
        _, _, mx, my = poly_bounds
        new_max_y = max(current_max_y, my)
        # mx is the candidate's max-x; smaller tends to pack left and reduce ragged offcuts.
        if scan_variant == 0:
            return (new_max_y, y, x, mx)
        if scan_variant == 1:
            return (y, new_max_y, x, mx)
        return (new_max_y, x, y, mx)

    for part in parts:
        cache = part.get("poly_cache")
        if not cache or cache.get("spacing") != spacing_mm:
            part["poly_cache"] = build_poly_cache_for_part(part, spacing_mm)

    for pid in items:
        if DEBUG_PLACEMENT:
            pids_processed += 1
        part = parts[pid]
        cache = part["poly_cache"]
        angs = list(cache["polys"].keys())

        # Deterministic but smarter angle ordering:
        # If 0/180 (or 90/270) are both available, alternate them for repeated parts.
        n_prev = placed_counts_so_far.get(pid, 0)
        if 0 in angs and 180 in angs:
            preferred = 0 if (n_prev % 2 == 0) else 180
            angs = [preferred] + [a for a in angs if a != preferred]
        elif 90 in angs and 270 in angs:
            preferred = 90 if (n_prev % 2 == 0) else 270
            angs = [preferred] + [a for a in angs if a != preferred]

        candidates = candidates_from_vertices(
            placed_polys,
            sheet_minx, sheet_miny, sheet_maxx, sheet_maxy,
            stride=10 if len(placed_polys) > 40 else 6
        )

        best = None
        best_score = None

        for a in angs:
            poly0 = cache["polys"][a]
            minx0, miny0, maxx0, maxy0 = poly0.bounds
            w0 = maxx0 - minx0
            h0 = maxy0 - miny0
            if w0 > usable_w or h0 > usable_h:
                continue

            if scan_variant == 1:
                candidates.sort(key=lambda p: (p[0], p[1]))
            else:
                candidates.sort(key=lambda p: (p[1], p[0]))

            cap = 2500 if len(items) > 200 else 4000
            for (cx, cy) in candidates[:cap]:
                if DEBUG_PLACEMENT:
                    candidates_tested += 1
                ptry = translate(poly0, xoff=cx, yoff=cy)
                b = ptry.bounds
                if b[2] > usable_w or b[3] > usable_h:
                    if DEBUG_PLACEMENT:
                        reject_stats['outside_bounds'] += 1
                    continue
                if not usable_prep.contains(ptry):
                    if DEBUG_PLACEMENT:
                        reject_stats['outside_usable'] += 1
                    continue

                hit = False
                if strtree is not None:
                    # Shapely 2.x STRtree.query() returns indices; Shapely 1.8 returns geometries.
                    for q in strtree.query(ptry):
                        g = placed_polys[q] if not hasattr(q, "geom_type") else q
                        if geoms_collide(ptry, g):
                            hit = True
                            break
                            break
                else:
                    for g in placed_polys:
                        if geoms_collide(ptry, g):
                            hit = True
                            break
                if hit:
                    if DEBUG_PLACEMENT:
                        reject_stats['collision'] += 1
                    continue

                sc = score_candidate(cx, cy, b)
                if best is None or sc < best_score:
                    best = (cx, cy, a, ptry, w0, h0)
                    best_score = sc

            if best is not None and best_score[0] <= current_max_y + 1e-6:
                break

        if best is None:
            continue

        cx, cy, a, ppoly, w0, h0 = best
        out0 = cache["outlines"][a]
        outline = translate(out0, xoff=cx, yoff=cy)

        placed_polys.append(ppoly)
        rebuild_index()
        current_max_y = max(current_max_y, ppoly.bounds[3])

        placements.append({
            "part_id": pid,
            "x": cx,
            "y": cy,
            "angle": a,
            "poly": ppoly,
            "outline": outline,
            "w": w0,
            "h": h0,
        })
        placed_counts_so_far[pid] = placed_counts_so_far.get(pid, 0) + 1

        if len(placed_polys) in (1, 5, 10) or (len(placed_polys) % 15 == 0):
            rebuild_index()

    placed_counts = {}
    for pl in placements:
        placed_counts[pl["part_id"]] = placed_counts.get(pl["part_id"], 0) + 1

    remaining = []
    counts_left = dict(placed_counts)
    for pid in items:
        if counts_left.get(pid, 0) > 0:
            counts_left[pid] -= 1
        else:
            remaining.append(pid)

    # Post-pass: compact then try small-part pocket fill (keeps spacing via buffered polys)
    try:
        compact_placements(placements, usable_rect, usable_prep)
    except Exception as e:
        if DEBUG_NESTING:
            print("[compact] error:", repr(e))
    try:
        pocket_fill_small_parts(placements, usable_rect, usable_prep)
    except Exception as e:
        if DEBUG_NESTING:
            print("[pocket_fill] error:", repr(e))
    if DEBUG_PLACEMENT:
        try:
            print(f"[Placement debug summary] tested={candidates_tested} placed={len(placements)} unplaced_parts={reject_stats.get('part_unplaced',0)}")
            for k in sorted(reject_stats.keys()):
                print(f"  {k}: {reject_stats[k]}")
        except Exception:
            pass
    return placements, remaining



# ---------------- Polygon nesting (Shapely) ----------------
def to_shapely_polygon(points):
    if points[0] != points[-1]:
        points = points + [points[0]]
    poly = Polygon(points)
    if not poly.is_valid:
        poly = poly.buffer(0)
    return poly


def build_poly_cache_for_part(part, spacing_mm):
    """Build per-rotation Shapely geometry caches.

    Important: the 'outline' (true cut profile) and the 'poly' (spacing-buffered profile)
    must share the same local origin per rotation, otherwise preview and collision geometry
    will not align and spacing will appear wrong.

    Strategy:
    - rotate the outline
    - buffer the rotated outline by spacing/2
    - shift BOTH by the buffered bounds' minx/miny so the buffered poly starts at (0,0)
    """
    base_outline = to_shapely_polygon(part["outer_poly_norm"])
    angs = allowed_angles(part["rotation_mode"])

    polys = {}
    outlines = {}

    for a in angs:
        ro = base_outline if a == 0 else rotate(base_outline, a, origin=(0, 0), use_radians=False)

        # Buffer AFTER rotation so buffer stays symmetric about the outline.
        rb = ro.buffer(spacing_mm / 2.0, join_style=1, resolution=16)

        # Use buffered bounds for the origin shift, and apply the same shift to both.
        minx, miny, _, _ = rb.bounds
        if minx or miny:
            ro = translate(ro, xoff=-minx, yoff=-miny)
            rb = translate(rb, xoff=-minx, yoff=-miny)

        outlines[a] = ro
        polys[a] = rb

    return {"spacing": spacing_mm, "polys": polys, "outlines": outlines}


def candidates_from_vertices(placed_polys, sheet_minx, sheet_miny, sheet_maxx, sheet_maxy, stride=8):
    """
    Generate candidate anchor points for bottom-left style placement.

    Key idea: build small sets of candidate Xs and Ys independently and combine them.
    This is critical for "row/stack" packing, where a good X can come from the sheet
    edge while a good Y comes from the *top bound* of another part (and vice-versa).

    IMPORTANT: We add *bounds-derived* anchors (minx/miny/maxx/maxy) in addition to
    (subsampled) vertex coords. Bounds are much more reliable than vertices for thin
    parts, simplified geometries, or when stride subsampling would otherwise miss
    a top edge, causing the nester to stall after 1–2 placements.
    """
    eps = 0.25

    # Always include sheet origin as the first BL candidate.
    xs = {sheet_minx}
    ys = {sheet_miny}

    if not placed_polys:
        return [(sheet_minx, sheet_miny)]

    for p in placed_polys:
        if p is None or getattr(p, "is_empty", True):
            continue

        # Bounds anchors (most important)
        minx, miny, maxx, maxy = p.bounds
        xs.add(max(sheet_minx, minx))
        ys.add(max(sheet_miny, miny))
        xs.add(min(sheet_maxx, maxx))
        ys.add(min(sheet_maxy, maxy))
        xs.add(min(sheet_maxx, maxx + eps))
        ys.add(min(sheet_maxy, maxy + eps))

        # Vertex anchors (helpful for pockets)
        try:
            coords = list(p.exterior.coords)
        except Exception:
            coords = []
        # Subsampling vertices can accidentally drop the *key* notch/diagonal vertices
        # that allow parts to "nest into" each other. Only subsample when the exterior
        # ring is very dense.
        if len(coords) > 200:
            coords = coords[::max(1, stride)]
        # For typical DXF outlines with few vertices, keep them all.
        for (x, y) in coords:
            x = max(sheet_minx, min(sheet_maxx, x))
            y = max(sheet_miny, min(sheet_maxy, y))
            xs.add(x); ys.add(y)
            xs.add(min(sheet_maxx, x + eps))
            ys.add(min(sheet_maxy, y + eps))

    # Focus BL search: keep only a limited number of smallest coordinates
    xs_sorted = sorted(x for x in xs if x <= sheet_maxx)
    ys_sorted = sorted(y for y in ys if y <= sheet_maxy)

    # Tunables: more improves packing but costs time
    MAX_XS = 120
    MAX_YS = 120
    xs_sorted = xs_sorted[:MAX_XS]
    ys_sorted = ys_sorted[:MAX_YS]

    return [(x, y) for x in xs_sorted for y in ys_sorted]



def geoms_collide(a, b):
    """True collision test for spacing-buffered polys.

    We allow *touching* boundaries because the spacing buffer already enforces clearance.
    Shapely's intersects() counts touching as intersection, which can stall packing.
    """
    try:
        return a.intersects(b) and (not a.touches(b))
    except Exception:
        return a.intersects(b)



def _move_ok(ptry, usable_prep, strtree, placed_polys, geom_id_to_index, ignore_index=None):
    """Return True if ptry stays inside usable rect and does not intersect other placed polys.

    Notes:
      - In Shapely 2.x, STRtree.query() returns geometries (not indices).
      - We keep an id(geom)->index map so we can ignore the current item reliably.
    """
    if not usable_prep.contains(ptry):
        return False

    if strtree is None:
        for j, g in enumerate(placed_polys):
            if ignore_index is not None and j == ignore_index:
                continue
            if geoms_collide(ptry, g):
                return False
        return True

    for g in strtree.query(ptry):
        j = geom_id_to_index.get(id(g), None)
        if ignore_index is not None and j == ignore_index:
            continue
        if geoms_collide(ptry, g):
            return False
    return True


    # Fallback: brute force
    for j, g in enumerate(placed_polys):
        if ignore_index is not None and j == ignore_index:
            continue
        if geoms_collide(ptry, g):
            return False
    return True


def _binary_slide(poly, dx, dy, usable_prep, strtree, placed_polys, geom_id_to_index, ignore_index, iters=18):
    """Slide poly along (dx,dy) direction by the maximum safe fraction in [0,1]."""
    lo, hi = 0.0, 1.0
    best = poly
    for _ in range(iters):
        mid = (lo + hi) * 0.5
        ptry = translate(poly, xoff=dx * mid, yoff=dy * mid)
        if _move_ok(ptry, usable_prep, strtree, placed_polys, geom_id_to_index, ignore_index=ignore_index):
            best = ptry
            lo = mid
        else:
            hi = mid
    return best


def compact_placements(placements, usable_rect, usable_prep, passes=2):
    """
    Deterministic post-pass compaction:
      - for each part (bottom-left order), slide left as far as possible, then down.
    This improves offcut quality without risking overlaps, because every move is validated.
    """
    if not placements:
        return placements



def _placements_envelope(placements):
    """Return (max_x, max_y, bbox_area) envelope of current placements based on buffered polys."""
    if not placements:
        return (0.0, 0.0, 0.0)
    minx = min(pl["poly"].bounds[0] for pl in placements)
    miny = min(pl["poly"].bounds[1] for pl in placements)
    maxx = max(pl["poly"].bounds[2] for pl in placements)
    maxy = max(pl["poly"].bounds[3] for pl in placements)
    return (maxx, maxy, (maxx - minx) * (maxy - miny))


def _placements_score(placements):
    """Stronger lexicographic score for 'better offcuts'.

    Order of preference:
      1) smaller max_x (pulls right edge left)
      2) smaller max_y (pulls top edge down)
      3) smaller bbox area
      4) smaller sum of minx (encourages overall left shift even if max_x unchanged)
      5) smaller sum of miny (encourages overall down shift)
    """
    if not placements:
        return (0.0, 0.0, 0.0, 0.0, 0.0)

    minxs = [pl["poly"].bounds[0] for pl in placements]
    minys = [pl["poly"].bounds[1] for pl in placements]
    maxxs = [pl["poly"].bounds[2] for pl in placements]
    maxys = [pl["poly"].bounds[3] for pl in placements]

    minx = min(minxs)
    miny = min(minys)
    maxx = max(maxxs)
    maxy = max(maxys)
    area = (maxx - minx) * (maxy - miny)

    # Round a bit for stability/determinism
    return (round(maxx, 6), round(maxy, 6), round(area, 6), round(sum(minxs), 6), round(sum(minys), 6))


def pocket_fill_small_parts(placements, usable_rect, usable_prep, max_parts=25, max_tests=6000, eps=0.05):
    """Local improvement pass that can move a part *up into a pocket*.

    Unlike gravity compaction, this can move parts upward / into gaps.

    Correctness-first rules:
      - keep spacing guarantees by testing buffered polys ('poly')
      - never allow intersections
      - only accept moves that improve a stable lexicographic score (_placements_score)
    """
    if len(placements) < 2:
        return placements

    base_score = _placements_score(placements)

    # Choose candidate parts (smallest areas first)
    idxs = list(range(len(placements)))
    idxs.sort(key=lambda i: placements[i]["poly"].area)
    idxs = idxs[:max_parts]

    xmin, ymin, xmax, ymax = usable_rect.bounds

    for idx in idxs:
        pl = placements[idx]
        poly0 = pl["poly"]
        out0 = pl["outline"]

        # Remove current part from collision set
        others = [placements[i]["poly"] for i in range(len(placements)) if i != idx]
        strtree = STRtree(others) if others else None

        pminx, pminy, pmaxx, pmaxy = poly0.bounds
        pw = pmaxx - pminx
        ph = pmaxy - pminy

        # Candidate x/y anchors derived from other bounds
        xs = {xmin + eps, xmax - pw - eps}
        ys = {ymin + eps, ymax - ph - eps}

        for g in others:
            ox1, oy1, ox2, oy2 = g.bounds
            xs.update([ox1 - pw - eps, ox1 + eps, ox2 - pw - eps, ox2 + eps])
            ys.update([oy1 - ph - eps, oy1 + eps, oy2 - ph - eps, oy2 + eps])

        # Vertex-derived anchors (helps find pockets not aligned to bbox edges)
        # Sample a few vertices from neighbours and try aligning our minx/miny to them.
        stride = 6
        for g in others[:80]:
            try:
                coords = list(g.exterior.coords)
            except Exception:
                continue
            if len(coords) > 4:
                coords = coords[::max(1, len(coords)//stride)]
            for (vx, vy) in coords:
                xs.add(vx + eps)
                xs.add(vx - pw - eps)
                ys.add(vy + eps)
                ys.add(vy - ph - eps)

        # Keep only feasible ranges
        xs = [x for x in xs if xmin - 1e-6 <= x <= (xmax - pw + 1e-6)]
        ys = [y for y in ys if ymin - 1e-6 <= y <= (ymax - ph + 1e-6)]
        xs.sort()
        ys.sort()

        # Add local scan around current position (small bounded)
        for dx in (-60, -40, -20, -10, -5, 0, 5, 10, 20, 40, 60):
            x = pminx + dx
            if xmin - 1e-6 <= x <= (xmax - pw + 1e-6):
                xs.append(x)
        for dy in (-60, -40, -20, -10, -5, 0, 5, 10, 20, 40, 60, 80, 120):
            y = pminy + dy
            if ymin - 1e-6 <= y <= (ymax - ph + 1e-6):
                ys.append(y)

        xs = sorted(set(xs))
        ys = sorted(set(ys))

        def ok(ptry):
            if not usable_prep.contains(ptry):
                return False
            if not others:
                return True
            if strtree is None:
                # shouldn't happen, but be safe
                for g in others:
                    if geoms_collide(ptry, g):
                        return False
                return True
            for hit in strtree.query(ptry):
                # Shapely 2.x returns geometries; Shapely 1.8 also returns geometries here
                if ptry.intersects(hit):
                    return False
            return True

        best_poly = None
        best_out = None
        best_score = None

        tests = 0
        # Scan y then x to prefer lower placements, but acceptance is score-based
        for y in ys:
            if tests >= max_tests:
                break
            for x in xs:
                tests += 1
                if tests > max_tests:
                    break

                ptry = translate(poly0, xoff=(x - pminx), yoff=(y - pminy))
                if not ok(ptry):
                    continue

                tmp_score = _placements_score([{"poly": ptry}] + [{"poly": g} for g in others])
                if tmp_score < base_score:
                    if best_score is None or tmp_score < best_score:
                        best_score = tmp_score
                        best_poly = ptry
                        best_out = translate(out0, xoff=(x - pminx), yoff=(y - pminy))

        if best_poly is not None:
            dx = best_poly.bounds[0] - poly0.bounds[0]
            dy = best_poly.bounds[1] - poly0.bounds[1]
            pl["poly"] = best_poly
            pl["outline"] = best_out
            pl["x"] += dx
            pl["y"] += dy

            base_score = _placements_score(placements)
            if DEBUG_NESTING:
                print(f"[pocket_fill] moved part_id={pl.get('part_id')} by dx={dx:.3f}, dy={dy:.3f} new_score={base_score}")

    return placements


def improve_by_reinsertion(placements, parts, usable_rect, usable_prep, passes=1, eps=0.01, max_candidates=600):
    """
    Local improvement pass: try to reinsert small parts into better 'pockets'.

    This is still conservative and correctness-first:
      - remove one part at a time
      - try a bounded set of deterministic candidate (x,y) anchors derived from other parts' bounds
      - accept only if collision-free AND improves the sheet envelope (maxx, then maxy)
    """
    if len(placements) < 2:
        return placements

    def envelope_score(pls):
        maxx = max(pl["poly"].bounds[2] for pl in pls) if pls else 0.0
        maxy = max(pl["poly"].bounds[3] for pl in pls) if pls else 0.0
        # lexicographic: primarily reduce rightmost extent, then topmost
        return (round(maxx, 6), round(maxy, 6))

    def rebuild_tree(pls):
        geoms = [pl.get("poly", None) for pl in pls]
        # Filter out any non-geometry objects defensively (correctness > speed)
        good = []
        idx_map = []
        for i, g in enumerate(geoms):
            if g is not None and hasattr(g, "geom_type"):
                good.append(g)
                idx_map.append(i)
        if len(good) != len(geoms):
            # Fall back to brute-force collision checks (no STRtree) if anything is weird
            return geoms, None, {}
        try:
            tree = STRtree(good) if good else None
            id2i_good = {id(g): i for i, g in enumerate(good)}
            # Map STRtree geometry -> index in original `geoms` list
            id2i = {gid: idx_map[i] for gid, i in ((k, v) for k, v in id2i_good.items())}
            return geoms, tree, id2i
        except Exception:
            # If STRtree refuses inputs for any reason, fall back safely
            return geoms, None, {}

    base_score = envelope_score(placements)

    # Process smaller parts first (they're more likely to fit in pockets)
    for _ in range(max(1, int(passes))):
        # Stable deterministic order each pass
        order = sorted(range(len(placements)), key=lambda i: (placements[i]["poly"].area, placements[i]["part_id"]))
        improved_any = False

        for idx in order:
            if idx >= len(placements):
                continue

            target = placements[idx]
            pid = target["part_id"]
            part = parts[pid]  # existing part definition from your current system

            # Pull out the target part
            others = [pl for j, pl in enumerate(placements) if j != idx]
            other_geoms, tree, id2i = rebuild_tree(others)

            # Build candidate anchors from other bounds
            xs = {0.0}
            ys = {0.0}
            bounds_list = [pl["poly"].bounds for pl in others]
            for (minx, miny, maxx, maxy) in bounds_list:
                xs.update([minx, maxx, maxx + eps, max(0.0, minx - eps)])
                ys.update([miny, maxy, maxy + eps, max(0.0, miny - eps)])

            # Prefer low/left anchors first (deterministic)
            xs_sorted = sorted(xs)
            ys_sorted = sorted(ys)

            # Build candidate pairs (x,y) with a cap
            candidates = []
            # 1) try "above" and "right of" each existing part (good for pocket filling)
            for (minx, miny, maxx, maxy) in bounds_list:
                candidates.append((minx, maxy + eps))
                candidates.append((maxx + eps, miny))
                candidates.append((maxx + eps, maxy + eps))
                candidates.append((minx, miny))
            # 2) mix a small grid from the unique x/y sets (still bounded)
            for x in xs_sorted[:60]:
                for y in ys_sorted[:60]:
                    candidates.append((x, y))
                    if len(candidates) >= max_candidates:
                        break
                if len(candidates) >= max_candidates:
                    break

            # Deduplicate candidates (rounded)
            seen = set()
            uniq = []
            for x, y in candidates:
                k = (round(x, 3), round(y, 3))
                if k in seen:
                    continue
                seen.add(k)
                uniq.append((x, y))
            candidates = uniq[:max_candidates]

            # Prepare the target geometry at its current rotation: reuse the stored poly/outline template
            base_poly = target["poly"]
            base_outline = target["outline"]

            # We will translate by aligning current poly's minx/miny to candidate x/y
            cur_minx, cur_miny, cur_maxx, cur_maxy = base_poly.bounds

            best_pl = None
            best_score = base_score

            for x, y in candidates:
                dx = x - cur_minx
                dy = y - cur_miny
                if abs(dx) < 1e-9 and abs(dy) < 1e-9:
                    continue

                ptry = translate(base_poly, xoff=dx, yoff=dy)

                # Inside sheet?
                if not usable_prep.contains(ptry):
                    continue

                # Collision check vs others
                ok = True
                if tree is None:
                    # Brute-force (safe) fallback
                    for og in other_geoms:
                        if og is None or not hasattr(og, "geom_type"):
                            continue
                        if ptry.intersects(og):
                            ok = False
                            break
                else:
                    for g in tree.query(ptry):
                        j = id2i.get(id(g), None)
                        if j is None:
                            continue
                        og = other_geoms[j]
                        if og is None or not hasattr(og, "geom_type"):
                            continue
                        if ptry.intersects(og):
                            ok = False
                            break
                if not ok:
                    continue

                # Candidate accepted -> evaluate score
                trial_pls = others + [{
                    **target,
                    "x": target["x"] + dx,
                    "y": target["y"] + dy,
                    "poly": ptry,
                    "outline": translate(base_outline, xoff=dx, yoff=dy),
                }]
                sc = envelope_score(trial_pls)
                if sc < best_score:
                    best_score = sc
                    best_pl = trial_pls[-1]

            if best_pl is not None:
                # Commit best placement back into placements
                placements[idx] = best_pl
                base_score = best_score
                improved_any = True

        if not improved_any:
            break

    return placements


# ---------------- Travel + job evaluation ----------------
def build_transformed_contours(part, angle_deg, dx_mm, dy_mm):
    turns = (angle_deg // 90) % 4

    contours = []
    for c in part["contours_norm"]:
        pts = c.points
        meta = dict(c.meta)

        pts_r = pts
        cxcy = meta.get("center") if c.kind == "CIRCLE" else None

        for _ in range(turns):
            pts_r = [rotate_pt_90(p) for p in pts_r]
            if cxcy is not None:
                cxcy = rotate_pt_90(cxcy)

        if turns != 0:
            pts_r = normalise_points_to_origin(pts_r)
            if c.kind == "CIRCLE" and cxcy is not None:
                bb = polygon_bbox([rotate_pt_90(p) for p in c.points]) if c.points else (0, 0, 0, 0)
                cx, cy = cxcy
                cx += -bb[0]
                cy += -bb[1]
                meta["center"] = (cx, cy)

        pts_t = translate_points(pts_r, dx_mm, dy_mm)
        bb = polygon_bbox(pts_t) if len(pts_t) >= 2 else (0, 0, 0, 0)
        contours.append(Contour(c.id, c.kind, c.length_mm, c.area_mm2, pts_t, bb, meta=meta))

    return contours


def holes_first_travel_for_instance(contours, start_xy):
    roots = build_containment_tree(contours)
    travel_mm, end_xy = holes_first_route(roots, start_xy=start_xy)
    return travel_mm, end_xy


def nearest_neighbour_order(instances, start_xy=(0.0, 0.0)):
    if not instances:
        return []
    remaining = set(range(len(instances)))
    order = []

    best = min(
        remaining,
        key=lambda i: (instances[i]["anchor_xy"][0] - start_xy[0]) ** 2 + (instances[i]["anchor_xy"][1] - start_xy[1]) ** 2
    )
    remaining.remove(best)
    order.append(best)

    while remaining:
        cx, cy = instances[order[-1]]["anchor_xy"]
        nxt = min(
            remaining,
            key=lambda i: (instances[i]["anchor_xy"][0] - cx) ** 2 + (instances[i]["anchor_xy"][1] - cy) ** 2
        )
        remaining.remove(nxt)
        order.append(nxt)

    return order


def estimate_sheet_times(parts, sheet_layout, sheet_w_mm, sheet_h_mm, margin_mm, cut_speed, travel_speed, pierce_sec, pierce_allow):
    placements = sheet_layout["placements"]
    instances = []
    cut_len_total = 0.0
    pierces_total = 0

    for pl in placements:
        pid = pl["part_id"]
        part = parts[pid]
        angle = int(pl.get("angle", 0))

        dx_mm = margin_mm + pl["x"]
        dy_mm = margin_mm + pl["y"]

        contours_inst = build_transformed_contours(part, angle_deg=angle, dx_mm=dx_mm, dy_mm=dy_mm)

        ax = dx_mm + pl["w"] / 2.0
        ay = dy_mm + pl["h"] / 2.0

        instances.append({"anchor_xy": (ax, ay), "contours": contours_inst})

        cut_len_total += part["cut_len"]
        pierces_total += part["pierces"]

    order = nearest_neighbour_order(instances, start_xy=(margin_mm, margin_mm))
    travel_mm = 0.0
    head_xy = (margin_mm, margin_mm)
    for oi in order:
        t_mm, end_xy = holes_first_travel_for_instance(instances[oi]["contours"], start_xy=head_xy)
        travel_mm += t_mm
        head_xy = end_xy

    pierce_allow_total = pierces_total * pierce_allow

    cut_time_min = cut_len_total / cut_speed if cut_speed > 0 else 0.0
    travel_time_min = travel_mm / travel_speed if travel_speed > 0 else 0.0
    pierce_time_min = (pierces_total * pierce_sec) / 60.0
    total_time_min = cut_time_min + travel_time_min + pierce_time_min

    return {
        "cut_len": cut_len_total,
        "pierces": pierces_total,
        "pierce_allow_len": pierce_allow_total,
        "effective_len": cut_len_total + pierce_allow_total,
        "travel_mm": travel_mm,
        "cut_time_min": cut_time_min,
        "travel_time_min": travel_time_min,
        "pierce_time_min": pierce_time_min,
        "total_time_min": total_time_min
    }


# ---------------- Zoom window ----------------
class ZoomWindow(tk.Toplevel):
    def __init__(self, parent, renderer):
        super().__init__(parent)
        self.title("Nest View (Zoom)")
        self.geometry("920x720")
        self.renderer = renderer

        self.scale = 1.0
        self.offx = 0.0
        self.offy = 0.0
        self.dragging = False
        self.lastx = 0
        self.lasty = 0

        top = ttk.Frame(self, padding=8)
        top.pack(fill="x")
        ttk.Label(top, text="Zoom:").pack(side="left")
        self.zoom_var = tk.DoubleVar(value=1.0)
        self.zoom = ttk.Scale(top, from_=0.2, to=6.0, orient="horizontal", variable=self.zoom_var, command=self.on_zoom)
        self.zoom.pack(side="left", fill="x", expand=True, padx=(6, 6))
        ttk.Button(top, text="Reset", command=self.reset_view).pack(side="left")

        self.canvas = tk.Canvas(self, bg="#111")
        self.canvas.pack(fill="both", expand=True)

        self.canvas.bind("<ButtonPress-1>", self.on_down)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_up)
        self.canvas.bind("<MouseWheel>", self.on_wheel)

        self.redraw()

    def on_zoom(self, _=None):
        self.scale = float(self.zoom_var.get())
        self.redraw()

    def reset_view(self):
        self.scale = 1.0
        self.zoom_var.set(1.0)
        self.offx = 0.0
        self.offy = 0.0
        self.redraw()

    def on_down(self, e):
        self.dragging = True
        self.lastx, self.lasty = e.x, e.y

    def on_drag(self, e):
        if not self.dragging:
            return
        dx = e.x - self.lastx
        dy = e.y - self.lasty
        self.offx += dx
        self.offy += dy
        self.lastx, self.lasty = e.x, e.y
        self.redraw()

    def on_up(self, _):
        self.dragging = False

    def on_wheel(self, e):
        if e.delta > 0:
            self.scale *= 1.12
        else:
            self.scale /= 1.12
        self.scale = max(0.2, min(6.0, self.scale))
        self.zoom_var.set(self.scale)
        self.redraw()

    def redraw(self):
        self.canvas.delete("all")
        self.renderer(self.canvas, self.scale, self.offx, self.offy)


# ---------------- Main GUI ----------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("DXF Nesting (Bounding Box / Polygon Shapely) + Multi-sheet + Variants + Zoom (v25)")
        self.geometry("1450x900")

        self.parts = []
        self.variants = []
        self.current_variant = 0
        self.current_sheet = 0

        self.sheet_var = tk.StringVar(value="3000 x 1500")
        self.margin_var = tk.StringVar(value=str(DEFAULT_MARGIN))
        self.spacing_var = tk.StringVar(value=str(DEFAULT_SPACING))

        self.nesting_mode_var = tk.StringVar(value="Polygon (Shapely) (realistic)")
        self.max_sheets_var = tk.StringVar(value="10")
        self.variants_var = tk.StringVar(value="5")

        self.rotation_global_var = tk.StringVar(value="0/90/180/270")
        self.cam_verify_var = tk.StringVar(value="80")


        self.debug_dxf_var = tk.BooleanVar(value=DEBUG_DXF)
        self.debug_place_var = tk.BooleanVar(value=DEBUG_PLACEMENT)
        self.material_var = tk.StringVar(value="Mild Steel")
        self.thickness_var = tk.IntVar(value=8)
        self.cut_speed_var = tk.StringVar(value="")

        self.travel_speed_var = tk.StringVar(value="20000")
        self.pierce_sec_var = tk.StringVar(value="1.0")
        self.pierce_allow_mm_var = tk.StringVar(value="1.0")

        root = ttk.Frame(self, padding=10)
        root.pack(fill="both", expand=True)

        # Row 1
        r1 = ttk.Frame(root)
        r1.pack(fill="x")

        r1b = ttk.Frame(root)
        r1b.pack(side="top", fill="x", pady=(0, 4))
        # Debug controls moved to second line to avoid hiding primary buttons on smaller windows
        ttk.Checkbutton(r1b, text="Debug DXF", variable=self.debug_dxf_var).pack(side="left", padx=(6, 14))
        ttk.Checkbutton(r1b, text="Debug placement", variable=self.debug_place_var).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Sheet:").pack(side="left")
        ttk.Combobox(r1, textvariable=self.sheet_var, values=list(SHEETS.keys()), state="readonly", width=14)\
            .pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Margin (mm):").pack(side="left")
        ttk.Entry(r1, textvariable=self.margin_var, width=7).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Spacing (mm):").pack(side="left")
        ttk.Entry(r1, textvariable=self.spacing_var, width=7).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Rotation cap:").pack(side="left")
        ttk.Combobox(
            r1,
            textvariable=self.rotation_global_var,
            values=["No rotation", "0/90", "0/90/180/270"],
            state="readonly",
            width=14
        ).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Mode:").pack(side="left")
        ttk.Combobox(
            r1,
            textvariable=self.nesting_mode_var,
            values=["Bounding Box (fast)", "Polygon (Shapely) (realistic)"],
            state="readonly",
            width=26
        ).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Max sheets:").pack(side="left")
        ttk.Entry(r1, textvariable=self.max_sheets_var, width=6).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="Variants:").pack(side="left")
        ttk.Entry(r1, textvariable=self.variants_var, width=6).pack(side="left", padx=(6, 14))

        ttk.Label(r1, text="CAM verify > %:").pack(side="left")
        ttk.Entry(r1, textvariable=self.cam_verify_var, width=6).pack(side="left", padx=(6, 14))



        ttk.Button(r1, text="Nest + Calculate", command=self.nest_start).pack(side="right", padx=(6, 0))
        ttk.Button(r1, text="Pick Nest…", command=self.pick_nest_dialog).pack(side="right", padx=(6, 0))

        # Row 2
        r2 = ttk.Frame(root)
        r2.pack(fill="x", pady=(10, 0))

        ttk.Label(r2, text="Material:").pack(side="left")
        mat = ttk.Combobox(r2, textvariable=self.material_var, values=list(CUT_SPEED_TABLE.keys()), state="readonly", width=14)
        mat.pack(side="left", padx=(6, 14))
        mat.bind("<<ComboboxSelected>>", lambda _e: self.update_cut_speed())

        ttk.Label(r2, text="Thickness (mm):").pack(side="left")
        thk = ttk.Combobox(r2, textvariable=self.thickness_var, values=THICKNESSES, state="readonly", width=6)
        thk.pack(side="left", padx=(6, 14))
        thk.bind("<<ComboboxSelected>>", lambda _e: self.update_cut_speed())

        ttk.Label(r2, text="Cut speed (mm/min):").pack(side="left")
        ttk.Entry(r2, textvariable=self.cut_speed_var, width=10).pack(side="left", padx=(6, 14))
        ttk.Label(r2, text="(auto; override ok)").pack(side="left")

        ttk.Label(r2, text="Travel speed (mm/min):").pack(side="left", padx=(14, 0))
        ttk.Entry(r2, textvariable=self.travel_speed_var, width=10).pack(side="left", padx=(6, 14))

        ttk.Label(r2, text="Pierce sec:").pack(side="left")
        ttk.Entry(r2, textvariable=self.pierce_sec_var, width=6).pack(side="left", padx=(6, 14))

        ttk.Label(r2, text="Pierce allow (mm):").pack(side="left")
        ttk.Entry(r2, textvariable=self.pierce_allow_mm_var, width=6).pack(side="left", padx=(6, 0))

        # Progress row (determinate %)
        rprog = ttk.Frame(root)
        rprog.pack(fill="x", pady=(10, 0))
        self.status_var = tk.StringVar(value="")
        ttk.Label(rprog, textvariable=self.status_var).pack(side="left")
        self.pbar = ttk.Progressbar(rprog, mode="determinate", maximum=100)
        self.pbar.pack(side="right", fill="x", expand=True, padx=(10, 0))
        self.pbar["value"] = 0

        # Split
        main = ttk.Frame(root)
        main.pack(fill="both", expand=True, pady=(10, 0))
        left = ttk.Frame(main)
        left.pack(side="left", fill="both", expand=True)
        right = ttk.Frame(main)
        right.pack(side="right", fill="both", expand=False)

        # Parts table
        tbl_frame = ttk.Frame(left)
        tbl_frame.pack(fill="x")

        self.tree = ttk.Treeview(tbl_frame, columns=("name", "qty", "rot", "w", "h"), show="headings", height=7)
        self.tree.heading("name", text="Part")
        self.tree.heading("qty", text="Qty")
        self.tree.heading("rot", text="Rotation")
        self.tree.heading("w", text="Outer W")
        self.tree.heading("h", text="Outer H")
        self.tree.column("name", width=460, anchor="w")
        self.tree.column("qty", width=60, anchor="center")
        self.tree.column("rot", width=140, anchor="center")
        self.tree.column("w", width=90, anchor="e")
        self.tree.column("h", width=90, anchor="e")
        self.tree.pack(side="left", fill="x", expand=True)
        self.tree.bind("<Double-1>", self.on_double_click_row)

        btns = ttk.Frame(tbl_frame)
        btns.pack(side="right", padx=(10, 0))
        ttk.Button(btns, text="Add DXF(s)…", command=self.add_dxfs).pack(fill="x")
        ttk.Button(btns, text="Remove", command=self.remove_selected).pack(fill="x", pady=(6, 0))
        ttk.Button(btns, text="Clear", command=self.clear_parts).pack(fill="x", pady=(6, 0))

        # Output
        self.out = tk.Text(left, height=22, wrap="word")
        self.out.pack(fill="both", expand=True, pady=(10, 0))
        self.out.insert("end", "Add DXFs. Double-click a row to set Qty/Rotation per part.\n")

        # Right: navigation + summary + preview
        nav = ttk.Frame(right)
        nav.pack(fill="x")
        ttk.Button(nav, text="Prev", command=self.prev_sheet).pack(side="left")
        ttk.Button(nav, text="Next", command=self.next_sheet).pack(side="left", padx=(6, 0))
        self.page_var = tk.StringVar(value="Sheet 0 of 0")
        ttk.Label(nav, textvariable=self.page_var).pack(side="left", padx=(10, 0))
        ttk.Button(nav, text="Open Zoom View…", command=self.open_zoom_view).pack(side="right")

        ttk.Label(right, text="Sheet summary").pack(anchor="w", pady=(8, 0))
        self.legend = tk.Text(right, width=62, height=9, wrap="word")
        self.legend.pack(padx=6, pady=(4, 6), fill="x")
        self.legend.configure(state="disabled")

        ttk.Label(right, text="Layout preview").pack(anchor="w")
        self.canvas = tk.Canvas(right, width=620, height=620, bg="#111")
        self.canvas.pack(padx=6, pady=6)

        self.update_cut_speed()

    # ---------- UI helpers ----------
    def ui(self, fn, *args, **kwargs):
        self.after(0, functools.partial(fn, *args, **kwargs))

    def ui_progress(self, percent, text):
        self.ui(self.set_progress, percent, text)

    def set_progress(self, percent, text=""):
        p = max(0, min(100, int(percent)))
        self.pbar["value"] = p
        self.status_var.set(f"{text} ({p}%)" if text else f"{p}%")
        self.update_idletasks()

    def update_cut_speed(self):
        mat = self.material_var.get()
        thk = int(self.thickness_var.get())
        speed = CUT_SPEED_TABLE.get(mat, {}).get(thk, "")
        self.cut_speed_var.set(str(speed) if speed != "" else "")

    def refresh_tree(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        for idx, p in enumerate(self.parts):
            self.tree.insert(
                "", "end", iid=str(idx),
                values=(p["name"], p["qty"], p["rotation_mode"], f"{p['outer_w']:.1f}", f"{p['outer_h']:.1f}")
            )

    def add_dxfs(self):
        paths = filedialog.askopenfilenames(
            title="Select DXF part file(s)",
            filetypes=[("DXF files", "*.dxf"), ("All files", "*.*")]
        )
        if not paths:
            return
        for p in paths:
            try:
                part = compute_part_model(p)
            except Exception as e:
                msg = f"{os.path.basename(p)}\n{type(e).__name__}: {e}"
                if self.debug_dxf_var.get():
                    msg += "\n\n" + traceback.format_exc()
                messagebox.showerror("DXF error", msg)
                continue
            self.parts.append(part)
        self.refresh_tree()

    def remove_selected(self):
        sel = self.tree.selection()
        if not sel:
            return
        idxs = sorted([int(i) for i in sel], reverse=True)
        for i in idxs:
            if 0 <= i < len(self.parts):
                self.parts.pop(i)
        self.refresh_tree()

    def clear_parts(self):
        self.parts = []
        self.variants = []
        self.current_variant = 0
        self.current_sheet = 0
        self.refresh_tree()
        self.canvas.delete("all")
        self.legend.configure(state="normal")
        self.legend.delete("1.0", "end")
        self.legend.configure(state="disabled")
        self.out.delete("1.0", "end")
        self.out.insert("end", "Add DXFs. Double-click a row to set Qty/Rotation per part.\n")
        self.page_var.set("Sheet 0 of 0")
        self.set_progress(0, "")

    def on_double_click_row(self, event):
        item = self.tree.identify_row(event.y)
        if not item:
            return
        idx = int(item)
        self.open_part_preview(idx)

    def open_edit_dialog(self, idx):
        p = self.parts[idx]
        win = tk.Toplevel(self)
        win.title("Edit Part Settings")
        win.resizable(False, False)

        ttk.Label(win, text=p["name"]).grid(row=0, column=0, columnspan=2, padx=10, pady=(10, 6), sticky="w")

        qty_var = tk.StringVar(value=str(p["qty"]))
        rot_var = tk.StringVar(value=p["rotation_mode"])

        ttk.Label(win, text="Quantity:").grid(row=1, column=0, padx=10, pady=6, sticky="e")
        ttk.Entry(win, textvariable=qty_var, width=10).grid(row=1, column=1, padx=10, pady=6, sticky="w")

        ttk.Label(win, text="Rotation:").grid(row=2, column=0, padx=10, pady=6, sticky="e")
        ttk.Combobox(
            win, textvariable=rot_var,
            values=["0 only", "0/90", "0/90/180/270"],
            state="readonly", width=14
        ).grid(row=2, column=1, padx=10, pady=6, sticky="w")

        def apply():
            try:
                q = int(qty_var.get().strip())
                if q < 0:
                    raise ValueError()
            except Exception:
                messagebox.showerror("Qty", "Enter a non-negative integer.")
                return
            p["qty"] = q
            p["rotation_mode"] = rot_var.get()
            self.refresh_tree()
            win.destroy()

        ttk.Button(win, text="Apply", command=apply).grid(row=3, column=0, columnspan=2, padx=10, pady=(6, 10))

    def open_part_preview(self, idx):
        """Open an in-app part preview with inline Qty/Rotation editing.

        This avoids the extra edit dialog while still allowing detailed settings.
        """
        p = self.parts[idx]

        win = tk.Toplevel(self)
        win.title(f"Part Preview: {p['name']}")
        win.geometry("900x650")
        win.minsize(700, 500)

        # ---- Controls row ----
        top = ttk.Frame(win)
        top.pack(side="top", fill="x", padx=10, pady=8)

        ttk.Label(top, text=p["name"], font=("Segoe UI", 11, "bold")).pack(side="left")

        # Qty
        ttk.Label(top, text="   Qty:").pack(side="left")
        qty_var = tk.IntVar(value=int(p.get("qty", 1)))

        qty_spin = ttk.Spinbox(top, from_=1, to=9999, textvariable=qty_var, width=6)
        qty_spin.pack(side="left", padx=(4, 10))

        # Rotation mode (what the part is allowed to use)
        ttk.Label(top, text="Rotation allowed:").pack(side="left")
        rotmode_var = tk.StringVar(value=p.get("rotation_mode", "0/90/180/270"))
        rotmode_box = ttk.Combobox(
            top,
            textvariable=rotmode_var,
            values=["0 only", "0/90", "0/90/180/270"],
            width=14,
            state="readonly",
        )
        rotmode_box.pack(side="left", padx=(4, 10))

        # Angle to preview
        ttk.Label(top, text="Preview angle:").pack(side="left")
        angle_var = tk.StringVar(value="0")
        angle_box = ttk.Combobox(top, textvariable=angle_var, values=["0"], width=6, state="readonly")
        angle_box.pack(side="left", padx=(4, 10))

        show_buf_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Show spacing buffer", variable=show_buf_var).pack(side="right")

        # Apply / Close
        btns = ttk.Frame(top)
        btns.pack(side="right", padx=(10, 0))
        apply_btn = ttk.Button(btns, text="Apply", width=10)
        apply_btn.pack(side="left", padx=(0, 6))
        ttk.Button(btns, text="Close", width=10, command=win.destroy).pack(side="left")

        # Canvas
        canvas = tk.Canvas(win, bg="#0b0b0b", highlightthickness=0)
        canvas.pack(side="top", fill="both", expand=True, padx=10, pady=(0, 10))

        def _preview_part():
            # Do NOT mutate the stored part until the user clicks Apply.
            pp = dict(p)
            pp["qty"] = max(1, int(qty_var.get() or 1))
            pp["rotation_mode"] = rotmode_var.get()
            return pp

        def _preview_cache():
            spacing_mm = float(self.spacing_var.get())
            return build_poly_cache_for_part(_preview_part(), spacing_mm)

        def refresh_angle_choices():
            angs = allowed_angles(rotmode_var.get())
            angle_box["values"] = [str(a) for a in angs]
            if str(angle_var.get()) not in [str(a) for a in angs]:
                angle_var.set(str(angs[0] if angs else 0))
        def apply_changes():
            # Commit Qty/rotation mode to the part model
            try:
                q = int(qty_var.get())
            except Exception:
                q = int(p.get('qty', 1))
            q = max(1, q)
            p['qty'] = q
            p['rotation_mode'] = rotmode_var.get()
            spacing_mm = float(self.spacing_var.get())
            p['poly_cache'] = build_poly_cache_for_part(p, spacing_mm)
            try:
                self.tree.set(str(idx), 'qty', str(p['qty']))
                self.tree.set(str(idx), 'rot', p['rotation_mode'])
            except Exception:
                pass
            refresh_angle_choices()
            redraw()
            win.destroy()

        def draw_geom_filled(geom, fill="#6a2c91", outline="#ff9900", stipple="gray25"):
            # Handles Polygon / MultiPolygon / GeometryCollection
            from shapely.geometry import Polygon as ShpPolygon
            geoms = []
            if geom is None or geom.is_empty:
                return
            gt = getattr(geom, "geom_type", "")
            if gt == "Polygon":
                geoms = [geom]
            elif gt in ("MultiPolygon", "GeometryCollection"):
                geoms = [g for g in geom.geoms if getattr(g, "geom_type", "") == "Polygon"]
            else:
                return

            bg = canvas["bg"]

            # Compute transform for current canvas size based on buffer bounds for consistent view
            all_bounds = []
            for g in geoms:
                all_bounds.append(g.bounds)
            minx = min(b[0] for b in all_bounds)
            miny = min(b[1] for b in all_bounds)
            maxx = max(b[2] for b in all_bounds)
            maxy = max(b[3] for b in all_bounds)

            w = max(1, canvas.winfo_width())
            h = max(1, canvas.winfo_height())
            pad = 30
            sx = (w - 2 * pad) / max(1e-9, (maxx - minx))
            sy = (h - 2 * pad) / max(1e-9, (maxy - miny))
            s = min(sx, sy)

            def tx(x): return pad + (x - minx) * s
            def ty(y): return h - (pad + (y - miny) * s)  # invert Y

            # Draw each polygon: exterior filled, then holes filled with background
            for g in geoms:
                ext = [(tx(x), ty(y)) for (x, y) in list(g.exterior.coords)]
                flat = [c for pt in ext for c in pt]
                canvas.create_polygon(*flat, fill=fill, outline=outline, width=2, stipple=stipple)

                for ring in g.interiors:
                    pts = [(tx(x), ty(y)) for (x, y) in list(ring.coords)]
                    flat2 = [c for pt in pts for c in pt]
                    canvas.create_polygon(*flat2, fill=bg, outline=bg, width=1)

            return (tx, ty)

        def draw_outline_dashed(geom, tx, ty, colour="#d0d0d0"):
            if geom is None or geom.is_empty:
                return
            gt = getattr(geom, "geom_type", "")
            geoms = []
            if gt == "Polygon":
                geoms = [geom]
            elif gt in ("MultiPolygon", "GeometryCollection"):
                geoms = [g for g in geom.geoms if getattr(g, "geom_type", "") == "Polygon"]
            else:
                return
            for g in geoms:
                pts = [(tx(x), ty(y)) for (x, y) in list(g.exterior.coords)]
                flat = [c for pt in pts for c in pt]
                canvas.create_line(*flat, fill=colour, width=2, dash=(6, 6))

        def redraw():
            canvas.delete("all")
            # Ensure cache exists
            spacing_mm = float(self.spacing_var.get())
            cache = _preview_cache()
            if not cache or cache.get("spacing") != spacing_mm:
                p["poly_cache"] = build_poly_cache_for_part(p, spacing_mm)
                cache = p["poly_cache"]

            try:
                a = int(angle_var.get())
            except Exception:
                a = 0

            outline = cache["outlines"].get(a)
            buf = cache["polys"].get(a)

            # Draw filled outline first; use buffer bounds for scaling if buffer shown, else outline bounds
            tx_ty = draw_geom_filled(outline)
            if tx_ty and show_buf_var.get():
                tx, ty = tx_ty
                draw_outline_dashed(buf, tx, ty)
        # Events
        apply_btn.config(command=apply_changes)

        qty_spin.bind('<Return>', lambda e: redraw())
        qty_spin.bind('<FocusOut>', lambda e: redraw())
        rotmode_box.bind('<<ComboboxSelected>>', lambda e: (refresh_angle_choices(), redraw()))
        angle_box.bind('<<ComboboxSelected>>', lambda e: redraw())
        show_buf_var.trace_add('write', lambda *_: redraw())

        # Resize redraw debounce
        _resize_job = {'id': None}
        def on_resize(_event):
            if _resize_job['id'] is not None:
                win.after_cancel(_resize_job['id'])
            _resize_job['id'] = win.after(80, redraw)
        win.bind('<Configure>', on_resize)

        refresh_angle_choices()
        redraw()
    def parse_float(self, s, name):
        try:
            return float(str(s).strip())
        except Exception:
            raise ValueError(f"Invalid {name}: {s}")

    def parse_int(self, s, name):
        try:
            return int(str(s).strip())
        except Exception:
            raise ValueError(f"Invalid {name}: {s}")

    def _snapshot_settings(self):
        # Read all Tk variables on UI thread; worker uses this dict only.
        return {
            "sheet_key": self.sheet_var.get(),
            "margin": self.margin_var.get(),
            "spacing": self.spacing_var.get(),
            "max_sheets": self.max_sheets_var.get(),
            "variants": self.variants_var.get(),
            "cam_thresh": self.cam_verify_var.get(),
            "cut_speed": self.cut_speed_var.get(),
            "travel_speed": self.travel_speed_var.get(),
            "pierce_sec": self.pierce_sec_var.get(),
            "pierce_allow": self.pierce_allow_mm_var.get(),
            "mode": self.nesting_mode_var.get(),
            "rot_global": self.rotation_global_var.get(),
        }

    # ---------- Nesting ----------
    def nest_start(self):
        global DEBUG_PLACEMENT
        DEBUG_PLACEMENT = bool(self.debug_place_var.get())
        if not self.parts:
            messagebox.showwarning("No parts", "Add at least one DXF.")
            return
        settings = self._snapshot_settings()
        self.set_progress(0, "Starting")
        t = threading.Thread(target=self._nest_worker, args=(settings,), daemon=True)
        t.start()

    def _nest_worker(self, settings):
        try:
            sw, sh = SHEETS[settings["sheet_key"]]
            margin = self.parse_float(settings["margin"], "margin")
            spacing = self.parse_float(settings["spacing"], "spacing")
            max_sheets = self.parse_int(settings["max_sheets"], "max sheets")
            nvars = self.parse_int(settings["variants"], "variants")
            cam_thresh = self.parse_float(settings["cam_thresh"], "CAM verify %")

            cut_speed = self.parse_float(settings["cut_speed"], "cut speed")
            travel_speed = self.parse_float(settings["travel_speed"], "travel speed")
            pierce_sec = self.parse_float(settings["pierce_sec"], "pierce sec")
            pierce_allow = self.parse_float(settings["pierce_allow"], "pierce allow")

            if margin < 0 or spacing < 0:
                raise ValueError("Margin/spacing must be >= 0")
            if max_sheets <= 0:
                raise ValueError("Max sheets must be > 0")
            if nvars <= 0:
                raise ValueError("Variants must be > 0")
            if cut_speed <= 0 or travel_speed <= 0:
                raise ValueError("Speeds must be > 0")
            if pierce_sec < 0 or pierce_allow < 0:
                raise ValueError("Pierce values must be >= 0")
            if cam_thresh < 0 or cam_thresh > 100:
                raise ValueError("CAM verify % must be 0..100")

            mode = settings["mode"]
            rot_global = settings["rot_global"]
            allow90_global = (rot_global in ("0/90", "0/90/180/270"))

            usable_w = sw - 2 * margin
            usable_h = sh - 2 * margin
            if usable_w <= 0 or usable_h <= 0:
                raise ValueError("Margin too large for sheet.")

            total_units = nvars * max_sheets
            done_units = 0

            variant_keys = ["area_desc", "shuffle", "shuffle"]
            base_seed = 12345
            variants = []

            part_area_proxy = [p["outer_w"] * p["outer_h"] for p in self.parts]

            for vi in range(nvars):
                vkey = variant_keys[vi % len(variant_keys)]
                scan_variant = vi % 3
                seed = base_seed + vi * 101
                rnd = random.Random(seed)

                saved_rot = [p["rotation_mode"] for p in self.parts]
                if not allow90_global:
                    for p in self.parts:
                        p["rotation_mode"] = "0 only"

                if mode == "Bounding Box (fast)":
                    items = []
                    for pid, part in enumerate(self.parts):
                        for _ in range(part["qty"]):
                            items.append({
                                "part_id": pid,
                                "w": part["outer_w"] + spacing,
                                "h": part["outer_h"] + spacing,
                                "allow_rotate_90": allows_90(part["rotation_mode"]),
                            })

                    if vkey == "shuffle":
                        rnd.shuffle(items)
                    else:
                        items.sort(key=lambda it: part_area_proxy[it["part_id"]], reverse=True)

                    sheets = []
                    remaining = items[:]
                    for si in range(max_sheets):
                        if not remaining:
                            done_units += (max_sheets - si)
                            break
                        placements, remaining2 = pack_rectangles_one_sheet(
                            usable_w, usable_h, remaining, scan_variant=scan_variant
                        )
                        if not placements:
                            done_units += (max_sheets - si)
                            break
                        sheets.append({"placements": placements, "mode": mode})
                        remaining = remaining2
                        done_units += 1
                        pct = int(done_units * 100 / total_units)
                        self.ui_progress(pct, f"Variant {vi+1}/{nvars} - Sheet {si+1}/{max_sheets}")

                else:
                    items = []
                    for pid, part in enumerate(self.parts):
                        for _ in range(part["qty"]):
                            items.append(pid)

                    if vkey == "shuffle":
                        rnd.shuffle(items)
                    else:
                        items.sort(key=lambda pid: part_area_proxy[pid], reverse=True)

                    sheets = []
                    remaining = items[:]
                    for si in range(max_sheets):
                        if not remaining:
                            done_units += (max_sheets - si)
                            break
                        placements, remaining2 = pack_polygons_one_sheet(
                            parts=self.parts,
                            items=remaining,
                            usable_w=usable_w,
                            usable_h=usable_h,
                            spacing_mm=spacing,
                            scan_variant=scan_variant
                        )
                        if not placements:
                            done_units += (max_sheets - si)
                            break
                        sheets.append({"placements": placements, "mode": mode})
                        remaining = remaining2
                        done_units += 1
                        pct = int(done_units * 100 / total_units)
                        self.ui_progress(pct, f"Variant {vi+1}/{nvars} - Sheet {si+1}/{max_sheets}")

                for p, r in zip(self.parts, saved_rot):
                    p["rotation_mode"] = r

                placed_counts = {i: 0 for i in range(len(self.parts))}
                total_placed = 0
                for shl in sheets:
                    for pl in shl["placements"]:
                        pid = pl["part_id"]
                        placed_counts[pid] += 1
                        total_placed += 1

                per_sheet_stats = []
                per_sheet_util = []
                usable_area = usable_w * usable_h

                for sh_i, shl in enumerate(sheets):
                    st = estimate_sheet_times(
                        parts=self.parts,
                        sheet_layout=shl,
                        sheet_w_mm=sw,
                        sheet_h_mm=sh,
                        margin_mm=margin,
                        cut_speed=cut_speed,
                        travel_speed=travel_speed,
                        pierce_sec=pierce_sec,
                        pierce_allow=pierce_allow
                    )
                    per_sheet_stats.append(st)

                    if mode == "Bounding Box (fast)":
                        area_used = sum(pl["w"] * pl["h"] for pl in shl["placements"])
                        util = (area_used / usable_area * 100.0) if usable_area > 0 else 0.0
                    else:
                        area_used = sum(pl["poly"].area for pl in shl["placements"])
                        util = (area_used / usable_area * 100.0) if usable_area > 0 else 0.0
                    per_sheet_util.append(util)

                total_time = sum(s["total_time_min"] for s in per_sheet_stats)
                total_cut = sum(s["cut_len"] for s in per_sheet_stats)
                total_travel = sum(s["travel_mm"] for s in per_sheet_stats)

                variants.append({
                    "name": f"Variant {vi+1} ({vkey}, scan {scan_variant})",
                    "result": {
                        "sheets": sheets,
                        "placed_counts": placed_counts,
                        "total_placed": total_placed,
                        "items_remaining": len(remaining),
                    },
                    "per_sheet": per_sheet_stats,
                    "per_sheet_util": per_sheet_util,
                    "summary": {
                        "sheets": len(sheets),
                        "placed": total_placed,
                        "remaining": len(remaining),
                        "time_min": total_time,
                        "cut_mm": total_cut,
                        "travel_mm": total_travel,
                        "max_util": max(per_sheet_util) if per_sheet_util else 0.0,
                    },
                    "meta": {
                        "sheet": (sw, sh),
                        "margin": margin,
                        "spacing": spacing,
                        "mode": mode,
                        "rotation_global": rot_global,
                        "cam_thresh": cam_thresh,
                    }
                })

            variants.sort(key=lambda v: (-v["summary"]["placed"], v["summary"]["sheets"], v["summary"]["time_min"]))
            self.ui(self._nest_done_ok, variants)

        except Exception as e:
            self.ui(self._nest_done_err, e)

    def _nest_done_ok(self, variants):
        self.variants = variants
        self.current_variant = 0
        self.current_sheet = 0
        self.set_progress(100, "Done")
        self.status_var.set("")
        self.render_current()

    def _nest_done_err(self, e):
        self.set_progress(0, "")
        self.status_var.set("")
        messagebox.showerror("Nesting error", str(e))

    # ---------- Variant/sheet navigation ----------
    def render_current(self):
        if not self.variants:
            self.page_var.set("Sheet 0 of 0")
            return

        var = self.variants[self.current_variant]
        sheets = var["result"]["sheets"]
        if not sheets:
            self.page_var.set("Sheet 0 of 0")
            self.canvas.delete("all")
            self.out.delete("1.0", "end")
            self.out.insert("end", "No sheets produced.\n")
            return

        self.current_sheet = max(0, min(self.current_sheet, len(sheets) - 1))
        self.page_var.set(f"Sheet {self.current_sheet + 1} of {len(sheets)}   |   {var['name']}")

        meta = var["meta"]
        sheet_layout = sheets[self.current_sheet]
        sh_stat = var["per_sheet"][self.current_sheet]
        util = var["per_sheet_util"][self.current_sheet]
        cam_thresh = meta["cam_thresh"]
        cam_flag = util >= cam_thresh

        placed_counts_total = var["result"]["placed_counts"]

        per_sheet_qty = {i: 0 for i in range(len(self.parts))}
        for pl in sheet_layout["placements"]:
            per_sheet_qty[pl["part_id"]] += 1

        self.out.delete("1.0", "end")
        self.out.insert("end", f"{var['name']}\n")
        self.out.insert("end", f"Sheet: {self.sheet_var.get()} | Margin {meta['margin']:.1f} | Spacing {meta['spacing']:.1f}\n")
        self.out.insert("end", f"Mode: {meta['mode']} | Rotation cap: {meta['rotation_global']}\n\n")

        self.out.insert("end", "Requested vs placed (total across all sheets):\n")
        for i, part in enumerate(self.parts):
            self.out.insert(
                "end",
                f"  {i+1:>2} | {part['name']} ({part['rotation_mode']}): requested {part['qty']}, placed {placed_counts_total.get(i,0)}\n"
            )

        self.out.insert("end", f"\nSheets used: {var['summary']['sheets']} | Items remaining: {var['summary']['remaining']}\n")
        self.out.insert(
            "end",
            f"TOTAL cut: {var['summary']['cut_mm']:.1f} mm | TOTAL travel: {var['summary']['travel_mm']:.1f} mm | TOTAL time: {var['summary']['time_min']:.2f} min\n\n"
        )

        self.out.insert("end", f"Current sheet: {self.current_sheet + 1}\n")
        self.out.insert("end", f"  Utilisation (usable): {util:.1f}%\n")
        if cam_flag:
            self.out.insert("end", f"  CAM verification required: {util:.1f}% >= {cam_thresh:.1f}%\n")
        self.out.insert("end", f"  Cut length:   {sh_stat['cut_len']:.1f} mm\n")
        self.out.insert("end", f"  Travel:       {sh_stat['travel_mm']:.1f} mm (holes-first)\n")
        self.out.insert("end", f"  Pierces:      {sh_stat['pierces']}\n")
        self.out.insert("end", f"  TOTAL time:   {sh_stat['total_time_min']:.2f} min\n")

        lines = []
        lines.append(f"Utilisation: {util:.1f}% (usable)")
        if cam_flag:
            lines.append(f"CAM verification required (>{cam_thresh:.0f}%)")
        lines.append("Qty on this sheet:")
        for i, part in enumerate(self.parts):
            q = per_sheet_qty.get(i, 0)
            if q > 0:
                lines.append(f"  {i+1:>2} | qty {q:<3} | {part['name']}")
        text = "\n".join(lines) + "\n"
        self.legend.configure(state="normal")
        self.legend.delete("1.0", "end")
        self.legend.insert("end", text)
        self.legend.configure(state="disabled")

        self.draw_sheet_preview(sheet_layout, meta, util, cam_flag)

    def prev_sheet(self):
        if not self.variants:
            return
        self.current_sheet = max(0, self.current_sheet - 1)
        self.render_current()

    def next_sheet(self):
        if not self.variants:
            return
        var = self.variants[self.current_variant]
        self.current_sheet = min(len(var["result"]["sheets"]) - 1, self.current_sheet + 1)
        self.render_current()

    def pick_nest_dialog(self):
        if not self.variants:
            messagebox.showinfo("Pick Nest", "Run Nest + Calculate first.")
            return

        win = tk.Toplevel(self)
        win.title("Pick Nest Variant")
        win.geometry("760x320")

        lst = tk.Listbox(win)
        lst.pack(fill="both", expand=True, padx=10, pady=10)

        for i, v in enumerate(self.variants):
            s = v["summary"]
            lst.insert(
                "end",
                f"{i+1}. {v['name']} | sheets {s['sheets']} | placed {s['placed']} | rem {s['remaining']} | max util {s['max_util']:.1f}% | time {s['time_min']:.2f} min"
            )

        def choose():
            sel = lst.curselection()
            if not sel:
                return
            self.current_variant = sel[0]
            self.current_sheet = 0
            self.render_current()
            win.destroy()

        ttk.Button(win, text="Select", command=choose).pack(pady=(0, 10))

    # ---------- Preview + zoom ----------
    def draw_sheet_preview(self, sheet_layout, meta, util, cam_flag):
        self.canvas.delete("all")

        sw, sh = SHEETS[self.sheet_var.get()]
        margin = meta["margin"]
        mode = meta["mode"]
        placements = sheet_layout["placements"]

        cw = int(self.canvas["width"])
        ch = int(self.canvas["height"])
        scale = min((cw - 20) / sw, (ch - 20) / sh)
        ox, oy = 10, 10

        def sx(x): return ox + x * scale
        def sy(y): return oy + y * scale

        outline_col = "#ff7a00" if cam_flag else "#777"
        self.canvas.create_rectangle(sx(0), sy(0), sx(sw), sy(sh), outline=outline_col, width=2)
        self.canvas.create_rectangle(sx(margin), sy(margin), sx(sw - margin), sy(sh - margin), outline="#444", dash=(4, 4))

        colors = ["#4cc9f0", "#f72585", "#b5179e", "#7209b7", "#3a86ff", "#ffbe0b", "#fb5607", "#06d6a0"]

        if mode == "Bounding Box (fast)":
            for pl in placements:
                pid = pl["part_id"]
                col = colors[pid % len(colors)]
                x = margin + pl["x"]
                y = margin + pl["y"]
                w = pl["w"]
                h = pl["h"]
                self.canvas.create_rectangle(sx(x), sy(y), sx(x + w), sy(y + h), outline=col, width=2)
        else:
            # Polygon mode: filled parts for visibility (outline + stippled fill), holes punched out.
            bg = self.canvas.cget("bg") or "#111"

            def _iter_polys(g):
                if g is None:
                    return []
                gt = getattr(g, "geom_type", "")
                if gt == "Polygon":
                    return [g]
                if gt == "MultiPolygon":
                    return list(g.geoms)
                if gt == "GeometryCollection":
                    out = []
                    for gg in g.geoms:
                        out.extend(_iter_polys(gg))
                    return out
                return []

            for pl in placements:
                pid = pl["part_id"]
                col = colors[pid % len(colors)]
                outline = pl.get("outline")
                for poly in _iter_polys(outline):
                    # Exterior
                    ext = list(poly.exterior.coords)
                    if len(ext) >= 3:
                        flat = []
                        for (x, y) in ext[:-1]:
                            flat.extend([sx(margin + x), sy(margin + y)])
                        self.canvas.create_polygon(
                            *flat,
                            outline=col,
                            fill=col,
                            stipple="gray25",
                            width=2
                        )
                    # Holes
                    for ring in getattr(poly, "interiors", []):
                        pts = list(ring.coords)
                        if len(pts) < 3:
                            continue
                        hflat = []
                        for (x, y) in pts[:-1]:
                            hflat.extend([sx(margin + x), sy(margin + y)])
                        self.canvas.create_polygon(
                            *hflat,
                            outline=col,
                            fill=bg,
                            width=2
                        )
        self.canvas.create_text(
            sx(margin + 5), sy(margin + 5), anchor="nw",
            text=f"{util:.1f}% util", fill="#ddd", font=("Segoe UI", 10, "bold")
        )

    def open_zoom_view(self):
        if not self.variants:
            messagebox.showinfo("Zoom View", "Run Nest + Calculate first.")
            return

        var = self.variants[self.current_variant]
        meta = var["meta"]
        sheet_layout = var["result"]["sheets"][self.current_sheet]
        util = var["per_sheet_util"][self.current_sheet]
        cam_thresh = meta["cam_thresh"]
        cam_flag = util >= cam_thresh

        sw, sh = SHEETS[self.sheet_var.get()]
        margin = meta["margin"]
        mode = meta["mode"]
        placements = sheet_layout["placements"]
        colors = ["#4cc9f0", "#f72585", "#b5179e", "#7209b7", "#3a86ff", "#ffbe0b", "#fb5607", "#06d6a0"]

        def renderer(canvas, zoom_scale, offx, offy):
            cw = canvas.winfo_width()
            ch = canvas.winfo_height()
            base = min((cw - 20) / sw, (ch - 20) / sh)
            sc = base * zoom_scale
            ox, oy = 10 + offx, 10 + offy

            def sx(x): return ox + x * sc
            def sy(y): return oy + y * sc

            outline_col = "#ff7a00" if cam_flag else "#777"
            canvas.create_rectangle(sx(0), sy(0), sx(sw), sy(sh), outline=outline_col, width=2)
            canvas.create_rectangle(sx(margin), sy(margin), sx(sw - margin), sy(sh - margin), outline="#444", dash=(4, 4))

            if mode == "Bounding Box (fast)":
                for pl in placements:
                    pid = pl["part_id"]
                    col = colors[pid % len(colors)]
                    x = margin + pl["x"]
                    y = margin + pl["y"]
                    w = pl["w"]
                    h = pl["h"]
                    canvas.create_rectangle(sx(x), sy(y), sx(x + w), sy(y + h), outline=col, width=2)
            else:
                # Polygon mode: filled parts for visibility (outline + stippled fill), holes punched out.
                bg = canvas.cget("bg") or "#111"

                def _iter_polys(g):
                    if g is None:
                        return []
                    gt = getattr(g, "geom_type", "")
                    if gt == "Polygon":
                        return [g]
                    if gt == "MultiPolygon":
                        return list(g.geoms)
                    if gt == "GeometryCollection":
                        out = []
                        for gg in g.geoms:
                            out.extend(_iter_polys(gg))
                        return out
                    return []

                for pl in placements:
                    pid = pl["part_id"]
                    col = colors[pid % len(colors)]
                    outline = pl.get("outline")
                    for poly in _iter_polys(outline):
                        ext = list(poly.exterior.coords)
                        if len(ext) >= 3:
                            flat = []
                            for (x, y) in ext[:-1]:
                                flat.extend([sx(margin + x), sy(margin + y)])
                            canvas.create_polygon(
                                *flat,
                                outline=col,
                                fill=col,
                                stipple="gray25",
                                width=2
                            )
                        for ring in getattr(poly, "interiors", []):
                            pts = list(ring.coords)
                            if len(pts) < 3:
                                continue
                            hflat = []
                            for (x, y) in pts[:-1]:
                                hflat.extend([sx(margin + x), sy(margin + y)])
                            canvas.create_polygon(
                                *hflat,
                                outline=col,
                                fill=bg,
                                width=2
                            )
            canvas.create_text(
                sx(margin + 5), sy(margin + 5), anchor="nw",
                text=f"{util:.1f}% util", fill="#ddd", font=("Segoe UI", 10, "bold")
            )

        ZoomWindow(self, renderer)


if __name__ == "__main__":
    App().mainloop()
