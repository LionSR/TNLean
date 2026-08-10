#!/usr/bin/env python3
"""Audit a tenkz `.tnlog` event stream (tenkz spec section 5).

A `.tnlog` is a line-oriented stream `event|key=value|...` written by the
tenkz LaTeX environments.  Every picture opens with `picture|id=kN|lang=kernel`
(the kernel surface is the package surface since the S4 swap); kernel records
belong to their picture by nesting.  `tree|picture=0` marks a `\\tntree`
typeset outside any environment (legal in running math).

Hard errors (exit 1):
  malformed-event      A field fails its type (e.g. an unexpanded expl3
                       token such as `\\l__tenkz_nrows_int` in a numeric
                       slot).  The stream is the contraction record; a
                       non-numeric coordinate names no cell, so the event
                       describes no drawable ink.
  malformed-tree       A tree's canonical numeric bracketing is not a
                       rooted binary tree, or disagrees with its declared
                       leaf and vertex counts.
  duplicate-picture    Two `picture` lines share one id: picture identity
                       is the key of every back-reference.
  dangling-picture-ref An event references an undeclared picture.
  empty-picture        A kernel picture emitted no content events.  A
                       tensor diagram with no atoms and no regions denotes
                       no tensor network -- historically the "34 fake
                       diagrams" class.
  label-overlap       A measured `tn label` visible support strictly intersects
                      a sibling glyph node or explicit visible wire node.
  bbox-coverage       A library-owned label, glyph, or wire use did not
                      produce its required measured geometry.
  kernel-crossing     A declared kernel crossing did not produce the
                      recorded under/over occlusion, or hit no intersection.
  kernel-check        A kernel equation check reported a malformed relation
                      or unequal boundary signatures.
  eq-boundary-mismatch Two panels of one equation group expose different
                       boundary kinds, multiplicities, or orientations.  A
                       tensor equation equates two maps of one type, so the
                       multisets of open legs must agree side-to-side, an
                       index leaving one side must leave the other, and only
                       the drawing directions may rotate.
  eq-unchecked        An equation group holds panels its own check records
                      never folded into a relation: the group's arithmetic
                      (relations plus distinct adjacent contractions plus one
                      equals panels) does not close, so some panel's boundary
                      was never compared.  A check record whose scope owns no
                      panel at all fails the same way.
  eq-check-drift      The stream's check policy is not its source's: it
                      retires a relation the source never opted out of, the
                      source opts out of a relation the stream checked anyway,
                      or the two disagree about comparing modulo bundles.  The
                      stream is then stale against the source it is read with;
                      only the waivers both state stand, and the comparison
                      runs in the stricter of the two readings.

Advisories (never affect the exit code):
  eq-sibling-mismatch  Consecutive kernel pictures joined by `=` in the
                       source, outside any equation group, expose different
                       boundaries.  The source `=` is a heuristic, not a
                       declaration: the mechanism that makes an equation
                       checkable is `tenkzeq` (DESIGN.md, "Equation
                       grouping"), so a mismatch here reports a picture pair
                       still to be moved into the scope.
  eq-sibling-unread    Pictures share one display but are not all joined by a
                       relation, so the display states a product, a sum, or a
                       map that only the scope classifies.  Reading it
                       pairwise would compare one factor against a whole side,
                       so nothing is claimed about it at all.
  eq-check-off         An equation group waived one relation with
                       `check={off={k: reason}}`, and its source declares the
                       same waiver.  Legal, and never silent: it is reported
                       with its reason.
  repeated-topology    Identical canonical atom+bond content in several
                       pictures: review ordinary TeX composition.  Repetition
                       alone never extends the public grammar.
  dialect-mismatch     An event kind foreign to its picture's language
                       (each sub-language owns its event dialect).
  unknown-event/lang   Forward-compatibility notes.
  stale-log            The source declares picture constructs but the log
                       has none (failed or interrupted compile).

The equation group is the `tenkzeq` scope and nothing else.  Every panel of
one scope carries that scope's number in its `picture` record and the scope
writes one `check` record per joiner, so the in-group enforcement above reads
the stream alone and runs wherever a picture compiles -- no source, no
heuristic.

Source heuristic (documented, deliberately simple, advisory only): out of
scope, picture-producing constructs (`\\begin{tenkz...}`) are matched to log
pictures in order of appearance; standalone `\\tntree` drawings emit no
picture event and are excluded.  The match is used only when the counts
agree.  Two consecutive pictures are "one displayed equation" when the source
between them contains `=` and no math-mode boundary (`$`, `\\[`, `\\]`),
no cell separator `&`, no other environment, and is short.

Usage: tenkz_audit.py file.tnlog [file.tex]
If file.tex is omitted, a sibling `<stem>.tex` is used when present.
Exit status: 1 iff hard errors were found.
"""

from __future__ import annotations

import hashlib
import re
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, NamedTuple, Optional

from tenkzlib.texcase import (
    Construct,
    following_group,
    following_group_span,
    scan_picture_event_constructs,
    strip_comments,
    top_level_options,
)
from tenkzlib.tnlog import (
    FIELD_VALIDATORS,
    Event,
    Picture,
    _is_int,
    _is_nonnegative_int,
    _is_positive_int,
    parse_log,
)

# The .tnlog language tag of the one picture environment: since the S4
# surface swap the `tenkz` environment is the kernel surface.
# The shared source other scripts (tenkz_lint.py) import.
ENVIRONMENT_LANGS = {
    "tenkz": "kernel",
}

KNOWN_LANGS = set(ENVIRONMENT_LANGS.values())

# Empty-picture hard check applies exactly to the spec's list (section 5.4).
EMPTY_CHECK_LANGS = {"kernel"}

# Event kinds the language is expected to emit -- generated by grepping
# every event call site in tex/tenkz/*.code.tex (DESIGN.md 5.1 carries the
# same table; keep the two in step by hand).  Geometry/use events and
# `warning` are cross-cutting/derived and are stripped from a picture's
# content before this table is consulted (see Picture.content), so listing
# them here is harmless but never load-bearing.
DIALECT_KINDS = {
    "kernel": {
        "atom",
        "wire",
        "mark",
        "frame",
        "string",
        "stringbead",
        "stringcross",
        "kernel-boundary",
    },
}


Rect = tuple[int, int, int, int]
Point = tuple[int, int]


def _point_rect_distance_sq(point: Point, rect: Rect) -> int:
    """Squared Euclidean distance to a closed axis-aligned rectangle."""
    x, y = point
    xmin, xmax, ymin, ymax = rect
    dx = max(xmin - x, 0, x - xmax)
    dy = max(ymin - y, 0, y - ymax)
    return dx * dx + dy * dy


def _rects_intersect(left: Rect, right: Rect) -> bool:
    return (max(left[0], right[0]) < min(left[1], right[1])
            and max(left[2], right[2]) < min(left[3], right[3]))


def _rect_contains(outer: Rect, inner: Rect) -> bool:
    return (outer[0] <= inner[0] and inner[1] <= outer[1]
            and outer[2] <= inner[2] and inner[3] <= outer[3])


def _circle2_intersects_rect(center: Point, diameter: int, rect: Rect) -> bool:
    """Strict overlap of a circle in doubled coordinates with a rectangle."""
    doubled_rect = tuple(2 * coordinate for coordinate in rect)
    return _point_rect_distance_sq(center, doubled_rect) < diameter * diameter


def _circles2_intersect(
        left_center: Point, left_diameter: int,
        right_center: Point, right_diameter: int) -> bool:
    dx = left_center[0] - right_center[0]
    dy = left_center[1] - right_center[1]
    diameter = left_diameter + right_diameter
    return dx * dx + dy * dy < diameter * diameter


def _circle_intersects_rect(bounds: Rect, rect: Rect) -> bool:
    xmin, xmax, ymin, ymax = bounds
    # Double every coordinate so half-scaled-point centres remain exact.
    center = (xmin + xmax, ymin + ymax)
    return _circle2_intersects_rect(center, xmax - xmin, rect)


def _roundrect_parts(bounds: Rect, radius: int) -> tuple[
        tuple[Rect, Rect], tuple[tuple[Point, int], ...]]:
    xmin, xmax, ymin, ymax = bounds
    rectangles = (
        (xmin + radius, xmax - radius, ymin, ymax),
        (xmin, xmax, ymin + radius, ymax - radius),
    )
    circles = tuple(
        ((2 * x, 2 * y), 2 * radius)
        for x, y in ((xmin + radius, ymin + radius),
                     (xmin + radius, ymax - radius),
                     (xmax - radius, ymin + radius),
                     (xmax - radius, ymax - radius))
    )
    return rectangles, circles


def _roundrect_intersects_rect(bounds: Rect, radius: int, rect: Rect) -> bool:
    rectangles, circles = _roundrect_parts(bounds, radius)
    if any(_rects_intersect(part, rect) for part in rectangles):
        return True
    return any(_circle2_intersects_rect(center, diameter, rect)
               for center, diameter in circles)


def _circle2_intersects_roundrect(
        center: Point, diameter: int, bounds: Rect, radius: int) -> bool:
    rectangles, circles = _roundrect_parts(bounds, radius)
    if any(_circle2_intersects_rect(center, diameter, part)
           for part in rectangles):
        return True
    return any(_circles2_intersect(center, diameter, other_center, other_diameter)
               for other_center, other_diameter in circles)


def _circle_intersects_roundrect(
        circle: Rect, bounds: Rect, radius: int) -> bool:
    center = (circle[0] + circle[1], circle[2] + circle[3])
    return _circle2_intersects_roundrect(
        center, circle[1] - circle[0], bounds, radius)


def _roundrects_intersect(
        left: Rect, left_radius: int, right: Rect, right_radius: int) -> bool:
    left_rectangles, left_circles = _roundrect_parts(left, left_radius)
    if any(_roundrect_intersects_rect(right, right_radius, part)
           for part in left_rectangles):
        return True
    return any(_circle2_intersects_roundrect(
        center, diameter, right, right_radius)
        for center, diameter in left_circles)


def _label_shapes_intersect(
        left_shape: str, left: Rect, left_radius: int,
        right_shape: str, right: Rect, right_radius: int) -> bool:
    if left_shape == "rect" and right_shape == "rect":
        return _rects_intersect(left, right)
    if left_shape == "roundrect" and right_shape == "rect":
        return _roundrect_intersects_rect(left, left_radius, right)
    if left_shape == "rect" and right_shape == "roundrect":
        return _roundrect_intersects_rect(right, right_radius, left)
    return _roundrects_intersect(left, left_radius, right, right_radius)


def _polygon_intersects_rect(points: tuple[Point, ...], rect: Rect) -> bool:
    """Strict convex-polygon/rectangle overlap; boundary tangency is legal."""
    xmin, xmax, ymin, ymax = rect
    rectangle = ((xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax))
    axes: list[Point] = [(1, 0), (0, 1)]
    for index, point in enumerate(points):
        following = points[(index + 1) % len(points)]
        edge = (following[0] - point[0], following[1] - point[1])
        axes.append((-edge[1], edge[0]))
    for axis in axes:
        polygon_projection = [x * axis[0] + y * axis[1] for x, y in points]
        rectangle_projection = [x * axis[0] + y * axis[1]
                                for x, y in rectangle]
        if (max(polygon_projection) <= min(rectangle_projection)
                or max(rectangle_projection) <= min(polygon_projection)):
            return False
    return True


def _cross(left: Point, right: Point, point: Point) -> int:
    return ((right[0] - left[0]) * (point[1] - left[1])
            - (right[1] - left[1]) * (point[0] - left[0]))


def _on_segment(left: Point, right: Point, point: Point) -> bool:
    return (_cross(left, right, point) == 0
            and min(left[0], right[0]) <= point[0] <= max(left[0], right[0])
            and min(left[1], right[1]) <= point[1] <= max(left[1], right[1]))


def _segments_intersect_closed(a: Point, b: Point, c: Point, d: Point) -> bool:
    abc = _cross(a, b, c)
    abd = _cross(a, b, d)
    cda = _cross(c, d, a)
    cdb = _cross(c, d, b)
    if ((abc > 0) != (abd > 0) and (cda > 0) != (cdb > 0)):
        return True
    return ((abc == 0 and _on_segment(a, b, c))
            or (abd == 0 and _on_segment(a, b, d))
            or (cda == 0 and _on_segment(c, d, a))
            or (cdb == 0 and _on_segment(c, d, b)))


def _segment_intersects_rect(start: Point, end: Point, rect: Rect) -> bool:
    xmin, xmax, ymin, ymax = rect
    if (xmin <= start[0] <= xmax and ymin <= start[1] <= ymax):
        return True
    if (xmin <= end[0] <= xmax and ymin <= end[1] <= ymax):
        return True
    corners = ((xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax))
    return any(
        _segments_intersect_closed(start, end, corner, following)
        for corner, following in zip(corners, corners[1:] + corners[:1])
    )


def _point_within_segment_stroke(
        point: Point, start: Point, end: Point, stroke: int) -> bool:
    dx = end[0] - start[0]
    dy = end[1] - start[1]
    length_sq = dx * dx + dy * dy
    if length_sq == 0:
        distance_sq = ((point[0] - start[0]) ** 2
                       + (point[1] - start[1]) ** 2)
        return distance_sq < stroke * stroke
    projection = ((point[0] - start[0]) * dx
                  + (point[1] - start[1]) * dy)
    if projection <= 0:
        distance_sq = ((point[0] - start[0]) ** 2
                       + (point[1] - start[1]) ** 2)
        return distance_sq < stroke * stroke
    if projection >= length_sq:
        distance_sq = ((point[0] - end[0]) ** 2
                       + (point[1] - end[1]) ** 2)
        return distance_sq < stroke * stroke
    perpendicular = dx * (point[1] - start[1]) - dy * (point[0] - start[0])
    return perpendicular * perpendicular < stroke * stroke * length_sq


def _point_in_convex_polygon_closed(
        point: Point, points: tuple[Point, ...]) -> bool:
    crosses = [_cross(points[index], points[(index + 1) % len(points)], point)
               for index in range(len(points))]
    return all(cross >= 0 for cross in crosses) or all(
        cross <= 0 for cross in crosses)


def _stroked_polygon_intersects_circle2(
        points: tuple[Point, ...], stroke: int,
        center: Point, diameter: int) -> bool:
    doubled_points = tuple((2 * x, 2 * y) for x, y in points)
    if _point_in_convex_polygon_closed(center, doubled_points):
        return True
    reach = diameter + 2 * stroke
    return any(
        _point_within_segment_stroke(
            center, point, doubled_points[(index + 1) % len(points)], reach
        )
        for index, point in enumerate(doubled_points)
    )


def _segment_stroke_intersects_rect(
        start: Point, end: Point, stroke: int, rect: Rect) -> bool:
    if _segment_intersects_rect(start, end, rect):
        return True
    if (_point_rect_distance_sq(start, rect) < stroke * stroke
            or _point_rect_distance_sq(end, rect) < stroke * stroke):
        return True
    xmin, xmax, ymin, ymax = rect
    return any(
        _point_within_segment_stroke(corner, start, end, stroke)
        for corner in ((xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax))
    )


def _stroked_polygon_intersects_rect(
        points: tuple[Point, ...], stroke: int, rect: Rect) -> bool:
    if _polygon_intersects_rect(points, rect):
        return True
    if stroke <= 0:
        return False
    return any(
        _segment_stroke_intersects_rect(
            point, points[(index + 1) % len(points)], stroke, rect
        )
        for index, point in enumerate(points)
    )


def _stroked_polygon_intersects_roundrect(
        points: tuple[Point, ...], stroke: int,
        bounds: Rect, radius: int) -> bool:
    rectangles, circles = _roundrect_parts(bounds, radius)
    if any(_stroked_polygon_intersects_rect(points, stroke, part)
           for part in rectangles):
        return True
    return any(
        _stroked_polygon_intersects_circle2(
            points, stroke, center, diameter
        )
        for center, diameter in circles
    )


class ScopePolicy(NamedTuple):
    """What one equation's own source says about how it is checked."""

    waived: set[int]         # relations its `check={off={k: ...}}` retires
    modulo_bundles: bool     # whether it compares a bundle as its multiplicity
    relation_order: tuple[int, ...]  # the gap each relation glyph sits on
    product_gaps: set[int]   # gaps holding no glyph, joining by juxtaposition


def _segment_intersects_label(
        start: Point, end: Point, stroke: int,
        shape: str, bounds: Rect, radius: int) -> bool:
    """True when a drawn segment's ink meets a measured label box.

    `stroke` is the half-width the segment is drawn with, the reach a
    measured glyph already publishes under that name: a centreline clearing
    the box by less than that still paints on it."""
    if shape != "roundrect" or radius == 0:
        return _segment_stroke_intersects_rect(start, end, stroke, bounds)
    rectangles, circles = _roundrect_parts(bounds, radius)
    if any(_segment_stroke_intersects_rect(start, end, stroke, part)
           for part in rectangles):
        return True
    # `_roundrect_parts` returns corner centres and diameters already doubled
    # so that a half-scaled-point centre stays exact; only the segment and the
    # stroke it is drawn with are doubled here to meet them.
    return any(
        _point_within_segment_stroke(
            center,
            (2 * start[0], 2 * start[1]), (2 * end[0], 2 * end[1]),
            diameter + 2 * stroke,
        )
        for center, diameter in circles
    )


def _label_inscribed_in_glyph(
        label_owner: int, label_rect: Rect,
        glyph_shape: str, glyph_bounds: Rect, glyph_owner: int) -> bool:
    """A box label deliberately inscribed in, and covered by, its own glyph.

    Containment is what makes the exemption safe to extend past the glyph's
    own outline: everything the label meets lies inside the glyph, and the
    glyph is painted over it."""
    return (glyph_shape == "rect" and label_owner > 0
            and label_owner == glyph_owner
            and _rect_contains(glyph_bounds, label_rect))


def parse_sp_point(value: str) -> Point:
    """Split an exact `x,y` picture-space point into its two integers."""
    x, y = value.split(",", 1)
    return (int(x), int(y))


# A closure end and the rail's own end are computed from one number, so they
# either coincide exactly or the rail was never joined to the row.  A
# hundredth of a point absorbs a rounding step and is two orders of magnitude
# below the reach a detached rail stands off by.
CLOSURE_JOIN_TOLERANCE_SP = 655


@dataclass
class Finding:
    severity: str  # "HARD" | "ADV" | "NOTE"
    rule: str
    where: str
    msg: str


class Audit:
    def __init__(self, log_path: Path, tex_path: Optional[Path]) -> None:
        self.log_path = log_path
        self.tex_path = tex_path
        self.findings: list[Finding] = []
        self.log_events: list[Event] = []
        self.pictures: list[Picture] = []
        self.by_id: dict[int | str, Picture] = {}
        self.constructs: list["Construct"] = []
        self.tex_linked = False

    def hard(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("HARD", rule, where, msg))

    def adv(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("ADV", rule, where, msg))

    def note(self, rule: str, where: str, msg: str) -> None:
        self.findings.append(Finding("NOTE", rule, where, msg))

    def require_fields(self, event: Event, required: set[str],
                        description: str) -> bool:
        """True if `event` carries every field in `required`; otherwise
        reports the standard malformed-event finding and returns False.
        Callers still decide their own control flow (continue vs. return)
        since that depends on whether the check runs inside a loop."""
        missing = sorted(required - event.attrs.keys())
        if missing:
            self.hard("malformed-event", f"{self.log_path.name}:{event.line}",
                      f"{description} event lacks required field(s): "
                      + ", ".join(missing))
            return False
        return True

    def events(self, picture_id: int | str | None = None) -> list[Event]:
        """Typed events already produced by `parse_log`, one picture or
        all of them.  The canonical accessor for consumers (tests, the
        `.tnlog` scripts) that would otherwise re-split the raw log a
        second time -- `Event.raw`/`.kind`/`.attrs` already carry
        whatever a hand-rolled `line.split('|')` pass would recompute."""
        if picture_id is None:
            return [e for pic in self.pictures for e in pic.events]
        pic = self.by_id.get(picture_id)
        return [] if pic is None else list(pic.events)

    # ---------------- parsing ----------------

    def parse_log(self) -> None:
        parsed = parse_log(
            self.log_path.read_text(encoding="utf-8"),
            source_name=self.log_path.name,
            known_langs=KNOWN_LANGS,
            hard=self.hard,
            advisory=self.adv,
            check_event=lambda event: (
                self.check_tree_event(event) if event.kind == "tree" else None
            ),
        )
        self.log_events = parsed.valid_events
        self.pictures = parsed.pictures
        self.by_id = parsed.by_id

    def check_tree_event(self, event: Event) -> None:
        """Validate the tree event as structural data, not display text."""
        where = f"{self.log_path.name}:{event.line}"
        required = {"id", "style", "leaves", "vertices", "topology",
                    "role", "species"}
        missing = sorted(required - event.attrs.keys())
        if missing:
            self.hard("malformed-tree", where,
                      f"tree event lacks required field(s): {', '.join(missing)}")
            return
        shape = parse_tree_topology(event.attrs["topology"])
        if shape is None:
            self.hard("malformed-tree", where,
                      f"invalid canonical topology {event.attrs['topology']!r}")
            return
        leaves, vertices = shape
        if not (_is_positive_int(event.attrs["leaves"])
                and _is_nonnegative_int(event.attrs["vertices"])):
            return  # generic field validation already reports these values
        declared = (int(event.attrs["leaves"]), int(event.attrs["vertices"]))
        if declared != (leaves, vertices):
            self.hard("malformed-tree", where,
                      f"topology has {leaves} leaves and {vertices} vertices, "
                      f"but event declares {declared[0]} and {declared[1]}")

    # ---------------- log-only checks ----------------

    def check_empty_pictures(self) -> None:
        for pic in self.pictures:
            if pic.content():
                continue
            where = f"{self.log_path.name}:{pic.line}"
            if pic.lang in EMPTY_CHECK_LANGS:
                self.hard("empty-picture", where,
                          f"picture {pic.ident} (lang={pic.lang}) emitted no "
                          f"content events")
            else:
                self.adv("empty-picture", where,
                         f"picture {pic.ident} (lang={pic.lang}) emitted no "
                         f"content events (lang outside the hard-check list)")

    def check_dialects(self) -> None:
        for pic in self.pictures:
            allowed = DIALECT_KINDS.get(pic.lang)
            if allowed is None:
                continue
            for e in pic.content():
                if e.kind not in allowed:
                    self.adv("dialect-mismatch", f"{self.log_path.name}:{e.line}",
                             f"{e.kind} event inside picture {pic.ident} "
                             f"(lang={pic.lang}); not part of that dialect")

    @staticmethod
    def _kernel_string_id(spelling: str) -> str:
        """Normalize a crossing operand to the renderer's string identifier."""
        text = spelling.strip()
        leg = re.fullmatch(
            r"leg\s+([nesw])\s+of\s+\{?\(\s*(\d+)\s*,\s*(\d+)\s*\)\}?",
            text,
        )
        if leg is not None:
            return f"leg-{leg.group(1)}-{leg.group(2)}-{leg.group(3)}"
        return text

    def check_kernel_crossings(self) -> None:
        """Match every declared crossing to the renderer's occlusion record."""
        crossing_pattern = re.compile(
            r"(?:^|,)\s*(under|over)\s+at\s+crossing\s+of\s+"
            r"(.+?)\s+and\s+(.+?)"
            r"(?=,\s*(?:under|over)\s+at\s+crossing\s+of\s+|\Z)"
        )
        for pic in self.pictures:
            if pic.lang != "kernel":
                continue
            atom_ids = {
                event.attrs["name"]: event.attrs["id"]
                for event in pic.events
                if event.kind == "atom"
                and event.attrs.get("name")
                and event.attrs.get("id")
            }
            wire_ids = {
                event.attrs.get("name", event.attrs.get("id", ""))
                for event in pic.events
                if event.kind == "wire"
            }
            wire_ids.discard("")
            pairing_hosts = {
                event.attrs.get("name", event.attrs.get("id", "")):
                    event.attrs.get("host", "")
                for event in pic.events
                if event.kind == "wire"
                and event.attrs.get("kind") == "pairing"
            }
            pairing_hosts.pop("", None)
            pairing_indices = {
                name: int(match.group(1))
                for name in pairing_hosts
                if (
                    match := re.fullmatch(r"skin-atom-\d+-([1-9]\d*)", name)
                )
            }
            strings = wire_ids | {
                event.attrs["id"]
                for event in pic.events
                if event.kind == "string" and event.attrs.get("id")
            }

            def crossing_id(spelling: str, declaring: str) -> str:
                text = spelling.strip()
                if text == "self":
                    return declaring
                pairing = re.fullmatch(
                    r"pairing\s+([1-9]\d*)\s+of\s+"
                    r"([A-Za-z][A-Za-z0-9\-]*)",
                    text,
                )
                if pairing is not None:
                    host = atom_ids.get(pairing.group(2))
                    if host is not None:
                        return f"skin-{host}-{pairing.group(1)}"
                return self._kernel_string_id(text)

            expected: Counter[tuple[str, str]] = Counter()
            explicit_pairs: set[frozenset[str]] = set()
            for wire in (event for event in pic.events
                         if event.kind == "wire" and "cross" in event.attrs):
                declaring = wire.attrs.get("name", wire.attrs.get("id", ""))
                declaring = self._kernel_string_id(declaring)
                matches = list(crossing_pattern.finditer(wire.attrs["cross"]))
                if not matches:
                    self.hard(
                        "kernel-crossing",
                        f"{self.log_path.name}:{wire.line}",
                        f"picture {pic.ident} wire {declaring!r} has an "
                        "unparseable crossing declaration",
                    )
                    continue
                for match in matches:
                    order, left_text, right_text = match.groups()
                    left = crossing_id(left_text, declaring)
                    right = crossing_id(right_text, declaring)
                    if declaring == left:
                        other = right
                    elif declaring == right:
                        other = left
                    else:
                        self.hard(
                            "kernel-crossing",
                            f"{self.log_path.name}:{wire.line}",
                            f"picture {pic.ident} crossing {left!r}/{right!r} "
                            f"does not name its declaring wire {declaring!r}",
                        )
                        continue
                    pair = (
                        (declaring, other) if order == "under"
                        else (other, declaring)
                    )
                    expected[pair] += 1
                    explicit_pairs.add(frozenset(pair))

            rendered: Counter[tuple[str, str]] = Counter()
            for event in (event for event in pic.events
                          if event.kind == "stringcross"):
                if not self.require_fields(
                    event, {"under", "over", "hits"}, "stringcross"
                ):
                    continue
                under = event.attrs["under"]
                over = event.attrs["over"]
                hits = event.attrs["hits"]
                if not _is_nonnegative_int(hits):
                    continue
                if int(hits) == 0:
                    self.hard(
                        "kernel-crossing",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} declared {under!r} under "
                        f"{over!r}, but the rendered paths do not intersect",
                    )
                missing = sorted({under, over} - strings)
                if missing:
                    self.hard(
                        "kernel-crossing",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} crossing names absent rendered "
                        f"string(s): {', '.join(missing)}",
                    )
                rendered[(under, over)] += 1

            # Pairings declared by one skin inherit their mutual paint order
            # from the declaration order.  They have no author-level `cross`
            # field, but the renderer still records their actual occlusions.
            # Treat only pairing/pairing intersections without an explicit
            # declaration as inherited; every other crossing remains checked
            # against author input above.
            for pair, count in rendered.items():
                if (
                    pairing_hosts.get(pair[0])
                    and pairing_hosts.get(pair[0]) == pairing_hosts.get(pair[1])
                    and pair[0] in pairing_indices
                    and pair[1] in pairing_indices
                    and frozenset(pair) not in explicit_pairs
                ):
                    ordered = tuple(
                        sorted(pair, key=pairing_indices.__getitem__)
                    )
                    expected[ordered] += count

            if expected != rendered:
                self.hard(
                    "kernel-crossing",
                    f"{self.log_path.name}:{pic.line}",
                    f"picture {pic.ident} declared occlusions "
                    f"{dict(expected)} but rendered {dict(rendered)}",
                )

    def check_kernel_checks(self) -> None:
        """Reject relation records that say the kernel check did not pass."""
        for pic in self.pictures:
            if pic.lang != "kernel":
                continue
            boundaries = [
                event for event in pic.events
                if event.kind == "kernel-boundary"
            ]
            if len(boundaries) != 1:
                self.hard(
                    "kernel-check",
                    f"{self.log_path.name}:{pic.line}",
                    f"picture {pic.ident} emitted {len(boundaries)} kernel "
                    "boundary records; expected exactly one",
                )
        for event in self.log_events:
            if event.kind != "check":
                continue
            result = event.attrs["result"]
            if result in {"mismatch", "malformed"}:
                relation = event.attrs.get("relation", "?")
                self.hard(
                    "kernel-check",
                    f"{self.log_path.name}:{event.line}",
                    f"kernel relation {relation} reported result={result}",
                )

    def closure_rails(
            self, pic: Picture
    ) -> list[tuple[Event, tuple[Point, ...], int]]:
        """Return every well-formed closure contour measured in `pic`.

        A rail is its polyline and the half-stroke it is drawn with."""
        rails: list[tuple[Event, tuple[Point, ...], int]] = []
        required = {"name", "row", "side", "west", "east", "stroke", "points"}
        for event in pic.events:
            if event.kind != "closure-rail":
                continue
            if not self.require_fields(event, required, "closure-rail"):
                continue
            if not _is_nonnegative_int(event.attrs["stroke"]):
                continue  # FIELD_VALIDATORS already reported the bad value.
            try:
                points = tuple(
                    parse_sp_point(part)
                    for part in event.attrs["points"].split(";")
                )
            except ValueError:
                continue  # FIELD_VALIDATORS already reported the bad value.
            if len(points) < 2:
                continue
            rails.append((event, points, int(event.attrs["stroke"])))
        return rails

    def check_closure_rails(self) -> None:
        """A traced row's closure must reach the row it closes.

        The mathematics a periodic picture states is a contraction of the
        row's two virtual ends.  A rail drawn short of them asserts that
        contraction in the record and denies it in the ink, and no measured
        gate sees the difference, because a wire carries no measured box.
        The closure publishes its own contour instead, and the two ends it
        names must be the two ends it starts and finishes on."""
        for pic in self.pictures:
            for event, points, _stroke in self.closure_rails(pic):
                for side, end, corner in (
                        ("west", event.attrs["west"], points[0]),
                        ("east", event.attrs["east"], points[-1]),
                ):
                    if end == "none":
                        continue
                    anchor = parse_sp_point(end)
                    gap = max(abs(anchor[0] - corner[0]),
                              abs(anchor[1] - corner[1]))
                    if gap > CLOSURE_JOIN_TOLERANCE_SP:
                        self.hard(
                            "closure-detached",
                            f"{self.log_path.name}:{event.line}",
                            f"picture {pic.ident} closure "
                            f"{event.attrs['name']} stops "
                            f"{gap / 65536:.2f}pt short of the {side} virtual "
                            f"end of row {event.attrs['row']}",
                        )

    def check_label_overlaps(self) -> None:
        """Reject label intersections with exact sibling visible geometry."""
        bbox_required = {"class", "id", "xmin", "xmax", "ymin", "ymax"}
        label_required = {"shape", "radius"}
        glyph_required = {"owner", "shape", "xmin", "xmax", "ymin", "ymax",
                          "radius", "stroke", "x1", "y1", "x2", "y2",
                          "x3", "y3"}
        wire_required = {"owner", "shape", "xmin", "xmax", "y", "outer",
                         "inner",
                         "cut-shape", "cut-xmin", "cut-xmax", "cut-ymin",
                         "cut-ymax", "cut-radius", "cut-id"}
        for pic in self.pictures:
            rectangles: list[tuple[Event, str, Rect, str, int]] = []
            for event in pic.events:
                if event.kind != "bbox":
                    continue
                if not self.require_fields(event, bbox_required, "bbox"):
                    continue
                if (event.attrs["class"] not in {"label", "wire"}
                        or any(not _is_int(event.attrs[field])
                               for field in ("xmin", "xmax", "ymin", "ymax"))
                        or not _is_positive_int(event.attrs["id"])):
                    continue  # FIELD_VALIDATORS already reported the bad value.
                xmin, xmax, ymin, ymax = (
                    int(event.attrs[field])
                    for field in ("xmin", "xmax", "ymin", "ymax")
                )
                if xmin > xmax or ymin > ymax:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"bbox id={event.attrs['id']} has inverted extents: "
                        f"({xmin},{ymin})--({xmax},{ymax})",
                    )
                    continue
                shape = "rect"
                radius = 0
                if event.attrs["class"] == "label":
                    if not self.require_fields(event, label_required, "label bbox"):
                        continue
                    if (event.attrs["shape"] not in {"rect", "roundrect"}
                            or not _is_nonnegative_int(event.attrs["radius"])):
                        continue
                    shape = event.attrs["shape"]
                    radius = int(event.attrs["radius"])
                    if shape == "rect" and radius != 0:
                        self.hard(
                            "malformed-event",
                            f"{self.log_path.name}:{event.line}",
                            f"rect label bbox id={event.attrs['id']} has "
                            f"nonzero radius={radius}",
                        )
                        continue
                    if (shape == "roundrect"
                            and (2 * radius > xmax - xmin
                                 or 2 * radius > ymax - ymin)):
                        self.hard(
                            "malformed-event",
                            f"{self.log_path.name}:{event.line}",
                            f"roundrect label bbox id={event.attrs['id']} "
                            f"radius={radius} exceeds half its measured width "
                            "or height",
                        )
                        continue
                rectangles.append(
                    (event, event.attrs["class"],
                     (xmin, xmax, ymin, ymax), shape, radius)
                )
            glyphs: list[
                tuple[Event, str, Rect, int, int, tuple[Point, ...]]
            ] = []
            for event in pic.events:
                if event.kind != "glyph-geometry":
                    continue
                if not self.require_fields(event, glyph_required, "glyph-geometry"):
                    continue
                numeric = glyph_required - {"shape"}
                if any(not _is_int(event.attrs[field]) for field in numeric):
                    continue
                bounds = tuple(int(event.attrs[field])
                               for field in ("xmin", "xmax", "ymin", "ymax"))
                if bounds[0] > bounds[1] or bounds[2] > bounds[3]:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"glyph owner={event.attrs['owner']} has inverted "
                        f"extents: ({bounds[0]},{bounds[2]})--"
                        f"({bounds[1]},{bounds[3]})",
                    )
                    continue
                if (event.attrs["shape"] == "circle"
                        and bounds[1] - bounds[0] != bounds[3] - bounds[2]):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"circle glyph owner={event.attrs['owner']} has unequal "
                        "measured width and height; ellipses are unsupported",
                    )
                    continue
                radius = int(event.attrs["radius"])
                stroke = int(event.attrs["stroke"])
                if radius < 0 or stroke < 0:
                    continue  # FIELD_VALIDATORS already reported the bad value.
                if (event.attrs["shape"] == "roundrect"
                        and (2 * radius > bounds[1] - bounds[0]
                             or 2 * radius > bounds[3] - bounds[2])):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"roundrect glyph owner={event.attrs['owner']} radius="
                        f"{radius} exceeds half its measured width or height",
                    )
                    continue
                points = tuple((int(event.attrs[f"x{index}"]),
                                int(event.attrs[f"y{index}"]))
                               for index in range(1, 4))
                glyphs.append((event, event.attrs["shape"], bounds,
                               radius, stroke, points))
            cut_wires: list[tuple[Event, Rect, int, str, Rect, int, int]] = []
            for event in pic.events:
                if event.kind != "wire-geometry":
                    continue
                if not self.require_fields(event, wire_required, "wire-geometry"):
                    continue
                numeric = wire_required - {"shape", "cut-shape"}
                if any(not _is_int(event.attrs[field]) for field in numeric):
                    continue
                if (event.attrs["shape"] != "rect-minus-label"
                        or event.attrs["cut-shape"] not in {"rect", "roundrect"}
                        or not _is_positive_int(event.attrs["owner"])
                        or not _is_positive_int(event.attrs["cut-id"])
                        or not _is_positive_int(event.attrs["outer"])
                        or not _is_nonnegative_int(event.attrs["inner"])
                        or not _is_nonnegative_int(event.attrs["cut-radius"])):
                    continue  # FIELD_VALIDATORS already reported the bad value.
                xmin = int(event.attrs["xmin"])
                xmax = int(event.attrs["xmax"])
                center_y = int(event.attrs["y"])
                outer = int(event.attrs["outer"])
                bounds = (
                    xmin,
                    xmax,
                    Fraction(2 * center_y - outer, 2),
                    Fraction(2 * center_y + outer, 2),
                )
                cut = tuple(int(event.attrs[field]) for field in (
                    "cut-xmin", "cut-xmax", "cut-ymin", "cut-ymax"
                ))
                radius = int(event.attrs["cut-radius"])
                inner = int(event.attrs["inner"])
                if xmin > xmax:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"wire owner={event.attrs['owner']} has inverted "
                        f"horizontal extents: {xmin}--{xmax}",
                    )
                    continue
                if cut[0] > cut[1] or cut[2] > cut[3]:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"wire owner={event.attrs['owner']} has inverted cut "
                        f"extents: ({cut[0]},{cut[2]})--({cut[1]},{cut[3]})",
                    )
                    continue
                if inner >= outer:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"wire owner={event.attrs['owner']} inner gap={inner} "
                        f"is not smaller than outer width={outer}",
                    )
                    continue
                if event.attrs["cut-shape"] == "rect" and radius != 0:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"rect wire cut owner={event.attrs['owner']} has "
                        f"nonzero radius={radius}",
                    )
                    continue
                if (event.attrs["cut-shape"] == "roundrect"
                        and (2 * radius > cut[1] - cut[0]
                             or 2 * radius > cut[3] - cut[2])):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"roundrect wire cut owner={event.attrs['owner']} "
                        f"radius={radius} exceeds half its width or height",
                    )
                    continue
                cut_wires.append((event, bounds, inner,
                                  event.attrs["cut-shape"], cut, radius,
                                  int(event.attrs["cut-id"])))
            rails = self.closure_rails(pic)
            labels = [rect for rect in rectangles if rect[1] == "label"]
            wire_boxes = [rect for rect in rectangles if rect[1] == "wire"]
            labels_by_id: dict[int, tuple[Event, str, Rect, str, int]] = {}
            duplicate_label_ids: set[int] = set()
            for label in labels:
                label_id = int(label[0].attrs["id"])
                if label_id in labels_by_id:
                    duplicate_label_ids.add(label_id)
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{label[0].line}",
                        f"picture {pic.ident} repeats label bbox id={label_id}",
                    )
                    continue
                labels_by_id[label_id] = label


            valid_cut_wires: list[
                tuple[Event, Rect, int, str, Rect, int, int]
            ] = []
            for wire in cut_wires:
                if wire[6] in duplicate_label_ids:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{wire[0].line}",
                        f"wire owner={wire[0].attrs['owner']} references "
                        f"non-unique cut label bbox id={wire[6]}",
                    )
                    continue
                cut_label = labels_by_id.get(wire[6])
                if cut_label is None:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{wire[0].line}",
                        f"wire owner={wire[0].attrs['owner']} references missing "
                        f"cut label bbox id={wire[6]}",
                    )
                    continue
                if (cut_label[2] != wire[4] or cut_label[3] != wire[3]
                        or cut_label[4] != wire[5]):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{wire[0].line}",
                        f"wire owner={wire[0].attrs['owner']} cut geometry "
                        f"disagrees with label bbox id={wire[6]}",
                    )
                    continue
                valid_cut_wires.append(wire)
            reported_label_pairs: set[tuple[int, int]] = set()
            for label in labels:
                label_rect = label[2]
                label_shape = label[3]
                label_radius = label[4]
                label_id = int(label[0].attrs["id"])
                owner = label[0].attrs.get("owner", "0")
                label_owner = int(owner) if _is_nonnegative_int(owner) else 0
                for other in wire_boxes:
                    other_rect = other[2]
                    if label_shape == "rect":
                        intersects = _rects_intersect(label_rect, other_rect)
                    else:
                        intersects = _roundrect_intersects_rect(
                            label_rect, label_radius, other_rect)
                    if intersects:
                        self.hard(
                            "label-overlap",
                            f"{self.log_path.name}:{label[0].line}",
                            f"picture {pic.ident} label bbox id="
                            f"{label[0].attrs['id']} intersects {other[1]} bbox "
                            f"id={other[0].attrs['id']}",
                        )
                for (wire_event, wire_rect, inner, cut_shape, cut_rect,
                     cut_radius, cut_id) in valid_cut_wires:
                    if label_id == cut_id:
                        continue
                    if _label_shapes_intersect(
                            label_shape, label_rect, label_radius,
                            cut_shape, cut_rect, cut_radius):
                        pair = tuple(sorted((label_id, cut_id)))
                        if pair not in reported_label_pairs:
                            reported_label_pairs.add(pair)
                            self.hard(
                                "label-overlap",
                                f"{self.log_path.name}:{label[0].line}",
                                f"picture {pic.ident} label bbox id={label_id} "
                                f"intersects label bbox id={cut_id}",
                            )
                        continue
                    wire_rects: list[Rect] = [wire_rect]
                    if inner > 0:
                        gap_bottom = Fraction(
                            wire_rect[2] + wire_rect[3] - inner, 2
                        )
                        gap_top = Fraction(
                            wire_rect[2] + wire_rect[3] + inner, 2
                        )
                        wire_rects = [
                            (wire_rect[0], wire_rect[1],
                             wire_rect[2], gap_bottom),
                            (wire_rect[0], wire_rect[1],
                             gap_top, wire_rect[3]),
                        ]
                    if label_shape == "rect":
                        intersects = any(
                            _rects_intersect(label_rect, rail)
                            for rail in wire_rects
                        )
                    else:
                        intersects = any(
                            _roundrect_intersects_rect(
                                label_rect, label_radius, rail
                            )
                            for rail in wire_rects
                        )
                    if intersects:
                        self.hard(
                            "label-overlap",
                            f"{self.log_path.name}:{label[0].line}",
                            f"picture {pic.ident} label bbox id={label_id} "
                            "intersects visible typed-map wire owned by ink "
                            f"id={wire_event.attrs['owner']}",
                        )
                # A rail runs out of the row's virtual end, which stands at
                # the end site's own centre, so its first and last stretch
                # lie under that site's glyph.  A name inscribed in and
                # covered by that glyph is painted over the rail, not on it.
                inscribed = any(
                    _label_inscribed_in_glyph(
                        label_owner, label_rect,
                        shape, bounds, int(event.attrs["owner"]))
                    for event, shape, bounds, _radius, _stroke, _points
                    in glyphs
                )
                for rail_event, rail_points, rail_stroke in (
                        [] if inscribed else rails):
                    # A closure rail is the one piece of network ink whose
                    # contour is published, and a name that lands on it is
                    # the pre-fix ink this gate was blind to: a label band
                    # shallower than the trace reach put every site name
                    # across the return that closes its own row.
                    if any(
                            _segment_intersects_label(
                                start, end, rail_stroke,
                                label_shape, label_rect, label_radius)
                            for start, end in zip(rail_points,
                                                  rail_points[1:])
                    ):
                        self.hard(
                            "label-overlap",
                            f"{self.log_path.name}:{label[0].line}",
                            f"picture {pic.ident} label bbox id={label_id} "
                            "intersects the closure "
                            f"{rail_event.attrs['name']} of row "
                            f"{rail_event.attrs['row']}",
                        )
                for event, shape, bounds, radius, stroke, points in glyphs:
                    glyph_owner = int(event.attrs["owner"])
                    # A box label is deliberately inscribed in its own glyph.
                    # Partial overlaps and intersections with sibling glyphs
                    # remain reportable.
                    if _label_inscribed_in_glyph(
                            label_owner, label_rect,
                            shape, bounds, glyph_owner):
                        continue
                    if label_shape == "rect":
                        if shape == "rect":
                            intersects = _rects_intersect(bounds, label_rect)
                        elif shape == "circle":
                            intersects = _circle_intersects_rect(bounds, label_rect)
                        elif shape == "roundrect":
                            intersects = _roundrect_intersects_rect(
                                bounds, radius, label_rect)
                        elif shape == "triangle":
                            intersects = _stroked_polygon_intersects_rect(
                                points, stroke, label_rect)
                        else:
                            continue
                    elif shape == "rect":
                        intersects = _roundrect_intersects_rect(
                            label_rect, label_radius, bounds)
                    elif shape == "circle":
                        intersects = _circle_intersects_roundrect(
                            bounds, label_rect, label_radius)
                    elif shape == "roundrect":
                        intersects = _roundrects_intersect(
                            label_rect, label_radius, bounds, radius)
                    elif shape == "triangle":
                        intersects = _stroked_polygon_intersects_roundrect(
                            points, stroke, label_rect, label_radius)
                    else:
                        continue  # generic field validation reports the shape
                    if intersects:
                        self.hard(
                            "label-overlap",
                            f"{self.log_path.name}:{label[0].line}",
                            f"picture {pic.ident} label bbox id="
                            f"{label[0].attrs['id']} intersects {shape} glyph "
                            f"owned by ink id={event.attrs.get('owner', '?')}",
                        )

    def check_bbox_coverage(self) -> None:
        """Every library-owned label/glyph/wire use has measured geometry."""
        for pic in self.pictures:
            uses = sum(event.kind == "label-use" for event in pic.events)
            boxes = sum(
                event.kind == "bbox" and event.attrs.get("class") == "label"
                for event in pic.events
            )
            if uses != boxes:
                self.hard(
                    "bbox-coverage",
                    f"{self.log_path.name}:{pic.line}",
                    f"picture {pic.ident} emitted {uses} label-use event(s) "
                    f"but {boxes} measured label bbox event(s)",
                )
            uses_by_id: dict[int, Event] = {}
            for event in pic.events:
                if event.kind != "ink-use":
                    continue
                if not self.require_fields(event, {"class", "id"}, "ink-use"):
                    continue
                if not _is_positive_int(event.attrs["id"]):
                    continue  # FIELD_VALIDATORS already reported the bad value.
                owner = int(event.attrs["id"])
                if owner in uses_by_id:
                    self.hard(
                        "bbox-coverage",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} repeats ink-use id={owner}",
                    )
                else:
                    uses_by_id[owner] = event

            geometry_by_owner: dict[int, list[Event]] = {}
            for event in pic.events:
                if (event.kind not in {"glyph-geometry", "wire-geometry"}
                        and (event.kind != "bbox"
                             or event.attrs.get("class") != "wire")):
                    continue
                owner_text = event.attrs.get("owner", "")
                if not _is_positive_int(owner_text):
                    self.hard(
                        "bbox-coverage",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} {event.kind} has no positive "
                        "ink owner",
                    )
                    continue
                geometry_by_owner.setdefault(int(owner_text), []).append(event)

            for owner, use in uses_by_id.items():
                geometry = geometry_by_owner.get(owner, [])
                expected = use.attrs.get("class")
                if expected == "glyph":
                    declared_shape = use.attrs.get("shape")
                    matching = [event for event in geometry
                                if event.kind == "glyph-geometry"
                                and event.attrs.get("shape") == declared_shape]
                    if declared_shape not in {
                            "rect", "circle", "roundrect", "triangle"}:
                        self.hard(
                            "bbox-coverage",
                            f"{self.log_path.name}:{use.line}",
                            f"picture {pic.ident} glyph ink-use id={owner} "
                            "declares no supported shape",
                        )
                else:
                    matching = [event for event in geometry
                                if event.kind == "wire-geometry"
                                or (event.kind == "bbox"
                                    and event.attrs.get("class") == "wire")]
                if not matching:
                    self.hard(
                        "bbox-coverage",
                        f"{self.log_path.name}:{use.line}",
                        f"picture {pic.ident} {expected} ink-use id={owner} "
                        "produced no matching geometry",
                    )
                elif len(matching) != 1:
                    self.hard(
                        "bbox-coverage",
                        f"{self.log_path.name}:{use.line}",
                        f"picture {pic.ident} {expected} ink-use id={owner} "
                        f"produced {len(matching)} matching geometries",
                    )
            for owner, geometry in geometry_by_owner.items():
                if owner not in uses_by_id:
                    event = geometry[0]
                    self.hard(
                        "bbox-coverage",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} {event.kind} names undeclared "
                        f"ink owner id={owner}",
                    )

    def check_repeated_topology(self) -> None:
        groups: dict[tuple[str, str], list[Picture]] = {}
        for pic in self.pictures:
            atoms = [e for e in pic.content() if e.kind == "atom"]
            if len(atoms) < 2:
                continue  # a repeated lone bead needs no composition review
            groups.setdefault((pic.lang, canonical_hash(pic)), []).append(pic)
        for (lang, digest), pics in sorted(groups.items(),
                                           key=lambda kv: kv[1][0].ident):
            if len(pics) < 2:
                continue
            ids = ", ".join(str(p.ident) for p in pics)
            self.adv("repeated-topology", self.log_path.name,
                     f"pictures {ids} (lang={lang}) share canonical topology "
                     f"{digest}; keep it inline or use ordinary TeX composition")

    # ---------------- source-linked checks ----------------

    def link_tex(self) -> None:
        if self.tex_path is None or not self.tex_path.exists():
            return
        src = strip_comments(self.tex_path.read_text(encoding="utf-8"))
        self.constructs = scan_picture_event_constructs(src)
        if len(self.constructs) == len(self.pictures) and self.pictures:
            self.tex_linked = True
        elif self.constructs and not self.pictures:
            self.adv("stale-log", self.log_path.name,
                     f"{self.tex_path.name} declares {len(self.constructs)} "
                     f"picture construct(s) but the log has none (failed or "
                     f"interrupted compile?)")
        elif len(self.constructs) != len(self.pictures):
            self.note("tex-unlinked", self.log_path.name,
                      f"{len(self.constructs)} construct(s) in "
                      f"{self.tex_path.name} vs {len(self.pictures)} picture(s) "
                      f"in the log; source-linked advisories disabled "
                      f"(macro-generated pictures?)")
        if self.tex_linked:
            self._tex_src = src

    # ---------------- the equation group ----------------

    def _scope_index(self) -> tuple[dict[int, int], dict[int, list[int]]]:
        """Map picture position to its `tenkzeq` scope and back.

        A picture record carries `scope=` exactly when it is a panel of an
        equation group, so the grouping is a fact of the stream and needs
        neither source nor heuristic.
        """
        picture_indices = {
            picture.ident: index for index, picture in enumerate(self.pictures)
        }
        picture_scopes: dict[int, int] = {}
        scope_pictures: dict[int, list[int]] = {}
        for event in self.log_events:
            if event.kind != "picture":
                continue
            scope = event.attrs.get("scope", "")
            picture = picture_indices.get(event.attrs.get("id", ""))
            if picture is None or not scope.isdigit():
                continue
            scope_index = int(scope)
            picture_scopes[picture] = scope_index
            scope_pictures.setdefault(scope_index, []).append(picture)
        return picture_scopes, scope_pictures

    def _scope_checks(self) -> tuple[dict[int, list[Event]], set[int]]:
        """Each scope's `check` records, and the scopes that failed arity."""
        scope_events: dict[int, list[Event]] = {}
        malformed_scopes: set[int] = set()
        for event in self.log_events:
            if event.kind != "check":
                continue
            scope = event.attrs.get("scope", "")
            if not scope.isdigit():
                continue
            scope_index = int(scope)
            if event.attrs.get("result") == "malformed":
                malformed_scopes.add(scope_index)
                continue
            scope_events.setdefault(scope_index, []).append(event)
        return scope_events, malformed_scopes

    def _tex_line(self, offset: int) -> int:
        """The source line an offset falls on."""
        return self._tex_src.count("\n", 0, offset) + 1

    def _tenkzeq_spans(self) -> list[tuple[int, int]]:
        """Source spans of the equation environments, innermost first."""
        spans: list[tuple[int, int]] = []
        stack: list[int] = []
        # TeX reads the space after a control word as part of it, so
        # `\begin {tenkzeq}` opens the same environment; the shared construct
        # scanner allows it and the span scan must agree, or a spaced source
        # would look to the audit like an equation with no source at all.
        for token in re.finditer(
            r"\\(begin|end)\s*\{tenkzeq\}", self._tex_src
        ):
            if token.group(1) == "begin":
                stack.append(token.end())
            elif stack:
                spans.append((stack.pop(), token.start()))
        return spans

    def _source_check_policy(self) -> Optional[dict[int, ScopePolicy]]:
        r"""Per scope, the check policy the source itself declares.

        The policy is the relations it waives, whether it compares modulo
        bundles, and which gap between its panels each joiner occupies.  That
        last part is exact rather than heuristic.  `tenkzeq` makes `=` the
        active relation glyph over its whole body while a picture resets it,
        so between two panels every unescaped `=` records one relation and a
        gap holding none joins its panels by juxtaposition -- a product.
        Reading the gaps for that one character therefore names the same
        joiners the kernel recorded, `\mbox{a=b}` included, which no reading
        of the mathematics could do.  `None` when no source is linked: the stream is then the only
        witness of its own policy, which is honoured and reported.  With a
        source, a waiver counts and a bundle expansion applies only where the
        environment's own `check=` says so, so a stale or edited stream can
        neither retire a comparison the author never opted out of nor loosen
        one the author never loosened.
        """
        if not self.tex_linked:
            return None
        picture_scopes, scope_pictures = self._scope_index()
        authorized: dict[int, ScopePolicy] = {}
        for begin, end in self._tenkzeq_spans():
            members = [
                index for index, construct in enumerate(self.constructs)
                if begin <= construct.start and construct.end <= end
            ]
            scopes = {picture_scopes.get(member) for member in members}
            scope = scopes.pop() if len(scopes) == 1 else None
            # The source states which pictures one equation holds and the
            # stream states which scope each picture claimed.  Where the two
            # do not name the same group, the comparisons that ran were
            # between panels no author put on one relation.
            if scope is None or scope_pictures.get(scope) != members:
                self.hard(
                    "eq-unchecked",
                    f"{self.tex_path.name}:{self._tex_line(begin)}",
                    f"the source states an equation over "
                    f"{len(members)} picture(s) that the stream does not "
                    f"group: its panels claim "
                    f"{sorted(str(picture_scopes.get(member, 'no scope')) for member in members)}",
                )
                continue
            separators = [
                self._tex_src[
                    self.constructs[left].end:self.constructs[right].start
                ]
                for left, right in zip(members, members[1:])
            ]
            marks = [relation_marks(separator) for separator in separators]
            # One entry per glyph, in source order, so the k-th relation keeps
            # the gap it sits on even where a gap carries more than one.
            relation_order = tuple(
                position + 1
                for position, count in enumerate(marks)
                for _ in range(count)
            )
            product_gaps = {
                position + 1 for position, count in enumerate(marks) if not count
            }
            authorized[scope] = ScopePolicy(
                _tenkzeq_declared_offs(self._tex_src, begin) or set(),
                _tenkzeq_declares_bundles(self._tex_src, begin),
                relation_order,
                product_gaps,
            )
        return authorized

    def check_equation_groups(self) -> None:
        """Enforce the boundary signature inside every equation group.

        The group is the `tenkzeq` scope.  Two facts carry it in the stream:
        every panel's `picture` record names its scope, and the scope writes
        one `check` record per joiner -- a relation comparison or a product
        contraction.  A mismatch inside a group is a hard error, not an
        advisory: an equation whose sides expose different boundaries states
        an identity between maps of different types.

        Two rules apply.  The group's arithmetic must close -- relations plus
        distinct adjacent contractions plus one equals panels -- so that no
        panel escapes comparison; a group whose arithmetic fails is read as
        unchecked, and its panels are then compared pair by pair, keeping the
        waivers the source authorizes.  And a side that is one panel is compared here
        whatever the kernel's verdict said, so a stream whose comparison never
        ran is caught rather than trusted -- for every relation of a group
        with no contraction in it, and, where the source settles which gaps
        its relations cross, for the single-panel sides of a group that holds
        one too.  Only a composite side's fold is left to the kernel, which is
        the one answer the audit does not recompute.

        Both halves of the ownership are checked.  A panel names its scope and
        a check names the scope it belongs to; a check whose scope owns no
        panel is an equation the stream does not contain, and a waiver the
        source and the stream disagree about means the two are not the same
        document.
        """
        _, scope_pictures = self._scope_index()
        scope_events, malformed_scopes = self._scope_checks()
        policy = self._source_check_policy()
        for scope in sorted(set(scope_events) | set(malformed_scopes)):
            if scope in scope_pictures:
                continue
            # A check record's scope is its ownership key.  A scope that owns
            # no panel names an equation the stream does not contain, which is
            # what an emitter losing `scope=` from its picture headers looks
            # like: the comparisons are recorded and the panels they name have
            # left the group.
            self.hard(
                "eq-unchecked", self.log_path.name,
                f"equation scope {scope} records "
                f"{len(scope_events.get(scope, []))} check(s) but owns no "
                f"panel; the scope's pictures never claimed it",
            )
        for scope in sorted(scope_pictures):
            members = scope_pictures[scope]
            records = scope_events.get(scope, [])
            relation_records = [
                event for event in records
                if event.attrs.get("relation", "").isdigit()
            ]
            relations = {
                int(event.attrs["relation"]): event for event in relation_records
            }
            product_records = [event for event in records if "product" in event.attrs]
            # A contraction names the adjacent panel pair it folded.  Only a
            # well-formed sequence of distinct adjacent pairs counts toward
            # closure: otherwise one pair recorded twice stands in for another
            # that was lost, and the panel that pair held escapes comparison.
            products = {
                pair for pair in (
                    _product_pair(event, len(members)) for event in product_records
                )
                if pair is not None
            }
            # Only a comparison states the mode it ran in; a waiver ran none
            # and says nothing, so a scope whose every relation is waived
            # leaves the mode unobserved rather than observed to be off.
            stated = [
                event for event in records
                if event.attrs.get("result") in {"equal", "mismatch", "contracted"}
            ]
            logged_modulo = any(
                event.attrs.get("modulo") == "bundles" for event in stated
            )
            where = f"{self.log_path.name}:{self.pictures[members[0]].line}"
            source = (
                None if policy is None
                else policy.get(scope, ScopePolicy(set(), False, (), set()))
            )
            declared = set() if source is None else source.waived
            declared_modulo = logged_modulo if source is None else source.modulo_bundles
            relation_order = () if source is None else source.relation_order
            relation_gaps = set(relation_order)
            product_gaps = set() if source is None else source.product_gaps
            # A bundle expansion loosens the comparison, so the source has to
            # ask for it: a stale stream carrying `modulo=bundles` past a
            # source that no longer says so would accept a bundle against a
            # count the current source rejects.  The comparison then runs in
            # the stricter of the two readings.
            modulo = logged_modulo and declared_modulo
            if policy is not None and stated and logged_modulo != declared_modulo:
                self.hard(
                    "eq-check-drift", where,
                    f"equation scope {scope} compares "
                    f"{'modulo bundles' if logged_modulo else 'strand for strand'}"
                    f" but its source asks for "
                    f"{'modulo bundles' if declared_modulo else 'strand for strand'}"
                    f"; the stream is not this source's",
                )
            closed = (
                scope not in malformed_scopes
                # An equation asserts at least one relation, so a scope
                # recording none compared nothing, however its panels count.
                and relations
                and len(relation_records) == len(relations)
                and set(relations) == set(range(1, len(relations) + 1))
                and len(product_records) == len(products)
                # With a source the joiners are placed, not merely counted:
                # the contractions are exactly the gaps holding no relation
                # glyph, and there are as many relations as glyphs.  A stream
                # that moves a joiner to another gap leaves a panel outside
                # every side while its counts still balance.
                and (source is None or products == product_gaps)
                and (source is None or len(relations) == len(relation_order))
                and len(relations) + len(products) + 1 == len(members)
            )
            waived: set[int] = {
                relation for relation, event in relations.items()
                if event.attrs.get("result") == "off"
            }
            if policy is not None:
                for relation in sorted(waived - declared):
                    self.hard(
                        "eq-check-drift", where,
                        f"equation scope {scope} waives relation {relation} "
                        f"but its source declares no such opt-out",
                    )
                for relation in sorted(declared - waived):
                    self.hard(
                        "eq-check-drift", where,
                        f"the source waives relation {relation} of equation "
                        f"scope {scope} but the stream records no waiver; the "
                        f"stream predates this source",
                    )
                # Only the waivers both state stand.  A forged one on its own
                # relation retires nothing; it does not retire the author's
                # honest opt-out on another relation of the same equation,
                # which would report a mismatch the author waived.
                waived &= declared
            for relation in sorted(waived):
                event = relations[relation]
                self.adv(
                    "eq-check-off",
                    f"{self.log_path.name}:{event.line}",
                    f"equation scope {scope} waived relation {relation}: "
                    f"{event.attrs.get('reason', '(no reason recorded)')}",
                )
            if not closed:
                if scope not in malformed_scopes:
                    # A malformed scope already failed as a hard kernel-check.
                    self.hard(
                        "eq-unchecked", where,
                        f"equation scope {scope} holds {len(members)} panel(s) "
                        f"but records {len(relation_records)} relation(s) and "
                        f"{len(product_records)} contraction(s) over "
                        f"{len(products)} distinct adjacent pair(s); every "
                        f"panel must fold into a compared side",
                    )
                # The fallback reads the panels as adjacent pairs, which is
                # what the kernel's own malformed-scope path does -- and it
                # honours the source's waivers there for the same reason the
                # kernel honours its own: an author who opted a relation out
                # did not opt back in by losing a record elsewhere.  The
                # waivers name relations and the walk visits gaps, so they are
                # mapped onto the gaps their glyphs sit on first.
                self._compare_adjacent(
                    members, scope, modulo,
                    _waived_gaps(waived, relation_order),
                )
                continue
            if not products:
                # Every side is one panel here, so the k-th relation is the
                # k-th gap: the walk is the same one, and it can say which
                # relation each pair sits on.
                self._compare_adjacent(
                    members, scope, modulo, waived, by_relation=True
                )
                continue
            # A composite side's signature is a fold over an interface the
            # kernel resolves, and its verdict is the `check` record that
            # `check_kernel_checks` rejects when it says mismatch.  The sides
            # that are one panel need no fold, so where the source settles
            # every gap -- each one either a relation it writes or a
            # contraction the stream records -- their relations are compared
            # here as well.
            gaps = relation_gaps | products
            if not relation_gaps or len(gaps) != len(members) - 1:
                continue
            sides = self._scope_sides(members, sorted(relation_gaps))
            for relation, (left, right) in enumerate(zip(sides, sides[1:]), 1):
                if relation in waived or len(left) != 1 or len(right) != 1:
                    continue
                self._compare_panels(
                    self.pictures[left[0]], self.pictures[right[0]],
                    self.hard, "eq-boundary-mismatch",
                    f"sit on relation {relation} of equation scope {scope}",
                    modulo=modulo,
                )

    @staticmethod
    def _scope_sides(members: list[int], relation_gaps: list[int]) -> list[list[int]]:
        """The panel groups a scope's relations delimit, in source order."""
        sides: list[list[int]] = []
        start = 0
        for gap in relation_gaps:
            sides.append(members[start:gap])
            start = gap
        sides.append(members[start:])
        return sides

    def _compare_adjacent(self, members: list[int], scope: int, modulo: bool,
                          waived_gaps: set[int],
                          by_relation: bool = False) -> None:
        """Compare a scope's panels pair by pair, skipping the waived gaps.

        `by_relation` says whether a pair can be named as the relation it sits
        on.  It can where every side is one panel; where the group's own
        account of its joiners did not hold, a panel's neighbour is all there
        is to compare it against and the finding says only that.
        """
        for gap in range(1, len(members)):
            if gap in waived_gaps:
                continue
            self._compare_panels(
                self.pictures[members[gap - 1]],
                self.pictures[members[gap]],
                self.hard, "eq-boundary-mismatch",
                f"sit on relation {gap} of equation scope {scope}"
                if by_relation else
                f"are adjacent panels {gap} and {gap + 1} of equation "
                f"scope {scope}",
                modulo=modulo,
            )

    def _compare_panels(self, left: Picture, right: Picture,
                        report: Callable[[str, str, str], None], rule: str,
                        relation: str, source: str = "",
                        modulo: bool = False) -> None:
        """Report when two panels expose different open-leg classes.

        Only the page face is dropped: a panel drawn rotated cuts the same
        indices on other sides of its frame.  Everything else the entry
        states -- virtual or physical, strand weight, and the orientation of
        a directed index -- belongs to the index and must agree.
        """
        sig_left, sig_right = left.kernel_boundary(), right.kernel_boundary()
        if sig_left is None or sig_right is None or sig_left == sig_right:
            return
        classes_left = boundary_classes(sig_left, modulo)
        classes_right = boundary_classes(sig_right, modulo)
        if classes_left == classes_right:
            return
        report(rule, f"{self.log_path.name}:{left.line}",
               f"pictures {left.ident} and {right.ident} {relation} "
               f"but open-leg classes differ: {sig_left} vs {sig_right}"
               f"{source}")

    def _display_runs(self) -> list[list[int]]:
        """Maximal runs of pictures the source sets in one display.

        Two consecutive pictures share a display when the source between them
        crosses no environment and no display-math boundary and is short.
        Panels of a `tenkzeq` scope are excluded: their group owns them.
        """
        picture_scopes, _ = self._scope_index()
        runs: list[list[int]] = []
        current: list[int] = []
        for index in range(len(self.pictures)):
            picture = self.pictures[index]
            if picture.lang != "kernel" or index in picture_scopes:
                current = []
                continue
            if current:
                previous, this = self.constructs[current[-1]], self.constructs[index]
                separator = (
                    self._tex_src[previous.end:this.start]
                    if previous.end <= this.start else None
                )
                if separator is None or not one_display(separator):
                    current = []
            if not current:
                # A run enters the list once, when it opens; it is the same
                # list that grows, so closing it must not enter it again.
                current = []
                runs.append(current)
            current.append(index)
        return [run for run in runs if len(run) > 1]

    def check_equation_boundaries(self) -> None:
        """Advise on pictures the source sets in one display, out of scope.

        The mechanism is `tenkzeq`; the mathematics between two pictures is a
        reading of the source, not a declaration, so nothing here fails the
        stream.  A display whose panels are all joined by a relation is read
        pairwise.  A display that asserts a relation somewhere but joins other
        panels another way -- a product, a sum, an arrow -- states a
        composition only the scope can classify, and the pairwise reading
        would compare one factor against a whole side; it is reported as
        unread rather than guessed at.  Pictures that assert no relation at
        all are simply adjacent, and nothing is said about them.
        """
        if not self.tex_linked:
            return
        for run in self._display_runs():
            separators = [
                self._tex_src[self.constructs[left].end:self.constructs[right].start]
                for left, right in zip(run, run[1:])
            ]
            if not any(same_equation(separator) for separator in separators):
                continue  # adjacent pictures, not a display asserting anything
            first = self.constructs[run[0]]
            if not all(same_equation(separator) for separator in separators):
                self.adv(
                    "eq-sibling-unread",
                    f"{self.log_path.name}:{self.pictures[run[0]].line}",
                    f"{len(run)} pictures share one display but are not all "
                    f"joined by a relation; the composition they state is the "
                    f"scope's to classify [{self.tex_path.name}:{first.line}]",
                )
                continue
            for left, right in zip(run, run[1:]):
                self._compare_panels(
                    self.pictures[left], self.pictures[right], self.adv,
                    "eq-sibling-mismatch",
                    "sit on one source `=` outside every equation group",
                    f" [{self.tex_path.name}:{self.constructs[left].line}]",
                )

    # ---------------- driver ----------------

    def run(self) -> int:
        self.parse_log()
        self.link_tex()
        self.check_empty_pictures()
        self.check_dialects()
        self.check_kernel_crossings()
        self.check_kernel_checks()
        self.check_bbox_coverage()
        self.check_closure_rails()
        self.check_label_overlaps()
        self.check_equation_groups()
        self.check_equation_boundaries()
        self.check_repeated_topology()
        return self.report()

    def report(self) -> int:
        hard = [f for f in self.findings if f.severity == "HARD"]
        advs = [f for f in self.findings if f.severity == "ADV"]
        notes = [f for f in self.findings if f.severity == "NOTE"]
        tex = self.tex_path.name if self.tex_path and self.tex_path.exists() else "none"
        linked = " (linked)" if self.tex_linked else ""
        print(f"== tenkz audit: {self.log_path.name} -- "
              f"{len(self.pictures)} picture(s); tex: {tex}{linked} ==")
        for f in hard + advs + notes:
            print(f"  {f.severity:<4} [{f.rule}] {f.where}: {f.msg}")
        if hard:
            print(f"  FAIL: {len(hard)} hard error(s), {len(advs)} advisory(ies)")
            return 1
        print(f"  ok: no hard errors ({len(advs)} advisory(ies))")
        return 0


# ---------------- canonical topology ----------------

def parse_tree_topology(value: str) -> Optional[tuple[int, int]]:
    """Return (leaves, internal vertices) for canonical numeric bracketing.

    A canonical tree is either the next positive leaf number or a pair of
    canonical trees.  Consequently the leaf sequence must be exactly
    1,2,...,n; labels and TeX never enter this structural field.
    """
    pos = 0
    leaf_numbers: list[int] = []

    def parse_node() -> Optional[int]:
        nonlocal pos
        if pos >= len(value):
            return None
        if value[pos].isdigit():
            start = pos
            while pos < len(value) and value[pos].isdigit():
                pos += 1
            leaf = int(value[start:pos])
            if leaf <= 0:
                return None
            leaf_numbers.append(leaf)
            return 0
        if value[pos] != "(":
            return None
        pos += 1
        left = parse_node()
        if left is None or pos >= len(value) or value[pos] != ",":
            return None
        pos += 1
        right = parse_node()
        if right is None or pos >= len(value) or value[pos] != ")":
            return None
        pos += 1
        return left + right + 1

    try:
        vertices = parse_node()
    except (RecursionError, ValueError):
        return None
    if (vertices is None or pos != len(value)
            or leaf_numbers != list(range(1, len(leaf_numbers) + 1))):
        return None
    return len(leaf_numbers), vertices


def canonical_hash(pic: Picture) -> str:
    """Order-free digest of a picture's content.  Attributes are sorted and
    the `picture` back-reference is dropped (identity must not depend on
    position in the document)."""
    lines = []
    for e in pic.content():
        attrs = {k: v for k, v in e.attrs.items() if k != "picture"}
        lines.append(e.kind + "|" + "|".join(
            f"{k}={v}" for k, v in sorted(attrs.items())))
    payload = "\n".join(sorted(lines)).encode("utf-8")
    return hashlib.sha1(payload).hexdigest()[:12]


# ---------------- TeX source scanning ----------------

_INLINE_EQUALITY_SPACE = r"(?:\s|\\[,;:!]|\\(?:quad|qquad)\b)*"
_INLINE_EQUALITY_GLUE = re.compile(
    rf"\${_INLINE_EQUALITY_SPACE}={_INLINE_EQUALITY_SPACE}\$"
)


def _tenkzeq_check_value(source: str, position: int) -> str | None:
    """One equation's `check=` value, unwrapped from its braces.

    ``None`` when the environment states no single top-level `check` key, in
    which case it declares no policy at all -- neither a waiver nor a
    comparison mode -- and both readers below agree on that.
    """
    options = following_group(source, position, "[", "]")
    if options is None:
        return None
    check_values = [
        value for key, value in top_level_options(options) if key == "check"
    ]
    if len(check_values) != 1 or check_values[0] is None:
        return None
    check_value = check_values[0]
    grouped = following_group_span(check_value, 0, "{", "}")
    if grouped is not None and not check_value[grouped[1] :].strip():
        check_value = grouped[0]
    return check_value


def _tenkzeq_declared_offs(source: str, position: int) -> set[int] | None:
    """Return source-authorized opt-outs from one equation's actual options."""
    check_value = _tenkzeq_check_value(source, position)
    if check_value is None:
        return None
    declared: set[int] = set()
    for key, value in top_level_options(check_value):
        if key != "off" or value is None:
            continue
        # A reason is prose about the mathematics and carries braces of its
        # own, so the relation is read off the front and the rest is left
        # alone.  The relation is read as a number, matching the kernel, so
        # a leading zero names the relation it looks like.
        # The key list strips one layer of braces from a value, so the
        # kernel reads `off={1: reason}` and `off=1: reason` as one thing
        # and so does this.
        payload = value.strip()
        if payload.startswith("{") and payload.endswith("}"):
            payload = payload[1:-1]
        match = re.match(r"\s*(\d+)\s*:", payload)
        if match is not None:
            declared.add(int(match.group(1)))
    return declared


def _tenkzeq_declares_bundles(source: str, position: int) -> bool:
    """True when one equation's own options ask to compare modulo bundles.

    The equivalence is read from the options themselves and not from the
    whole value: an opt-out's reason is prose an author writes about the
    mathematics, and prose that names an option is still prose.
    """
    check_value = _tenkzeq_check_value(source, position)
    if check_value is None:
        return False
    for key, value in top_level_options(check_value):
        if key != "modulo" or value is None:
            continue
        # The key list strips one layer of braces from a value, so
        # `modulo=bundles` and `modulo={bundles}` are one thing to the kernel
        # and one thing here.
        word = value.strip()
        if word.startswith("{") and word.endswith("}"):
            word = word[1:-1].strip()
        if word == "bundles":
            return True
    return False


_ORIENTATIONS = frozenset({"to", "from"})
_BUNDLE = re.compile(r"bundle=([1-9]\d*)")
_PRODUCT_PAIR = re.compile(r"(\d+)-(\d+)")


def _waived_gaps(waived: set[int], relation_order: tuple[int, ...]) -> set[int]:
    """The gaps a scope's waived relations sit on.

    A waiver names a relation by its ordinal while a pairwise comparison walks
    gaps, and the two agree only where every side is one panel.  The source
    lists the gap each of its relation glyphs sits on, one entry per glyph, so
    a gap carrying two of them keeps both ordinals; with no source there is
    nothing to map them through and they stand as they are.
    """
    if not relation_order:
        return set(waived)
    return {
        relation_order[relation - 1] for relation in waived
        if 1 <= relation <= len(relation_order)
    }


def _product_pair(event: Event, panels: int) -> int | None:
    """The left panel of a contraction, or `None` when it names no pair.

    A contraction folds one adjacent pair of a scope's panels, so a record
    naming a non-adjacent or out-of-range pair describes a fold the group
    cannot contain.
    """
    match = _PRODUCT_PAIR.fullmatch(event.attrs.get("product", ""))
    if match is None:
        return None
    left, right = int(match.group(1)), int(match.group(2))
    if right != left + 1 or left < 1 or right > panels:
        return None
    return left


def boundary_classes(signature: tuple[str, ...],
                     modulo_bundles: bool = False) -> Counter:
    """The multiset of open-leg classes a boundary signature exposes.

    Under `check={modulo=bundles}` a bundled strand stands for its own
    multiplicity of single strands, and the comparison expands it, exactly as
    the kernel's own comparison does.
    """
    classes: Counter = Counter()
    for item in signature:
        kind, weight, orientation = signature_entry_class(item)
        bundle = _BUNDLE.fullmatch(weight) if modulo_bundles else None
        if bundle is None:
            classes[(kind, weight, orientation)] += 1
        else:
            classes[(kind, "single", orientation)] += int(bundle.group(1))
    return classes


def signature_entry_class(item: str) -> tuple[str, str, str]:
    """Classify one boundary-signature entry, dropping only its page face.

    An entry is ``kind:face`` followed by the optional fields the index
    itself carries: a strand weight, and the orientation of a directed
    index (``to`` when it leaves the panel, ``from`` when it enters).  A
    rotated panel cuts its indices on other faces of its frame, so the face
    is not compared; weight and orientation are the index's own and are.
    """
    parts = [part.strip() for part in item.split(":")]
    kind = parts[0]
    if kind in {"edge", "open"}:
        kind = "virtual"
    rest = parts[2:]
    orientation = next((part for part in rest if part in _ORIENTATIONS), "none")
    weight = next((part for part in rest if part not in _ORIENTATIONS), "single")
    return kind, re.sub(r"\s*=\s*", "=", weight), orientation


_RELATION_MARK = re.compile(r"(?<!\\)(?:\\\\)*=")


def relation_marks(sep: str) -> int:
    r"""The relation glyphs one gap of an equation body holds.

    Inside `tenkzeq` the equals sign is the active relation glyph and a
    picture resets it, so between two panels each unescaped `=` records one
    relation.  A `\=` is a control symbol and never becomes that token.
    """
    return len(_RELATION_MARK.findall(sep))


def one_display(sep: str) -> bool:
    """True when the comment-stripped source between two pictures keeps them
    in one display: it crosses no environment, no display-math boundary and
    no cell separator, and is short.  Inline mathematics is the joiner the
    display is made of and does not end it."""
    if any(tok in sep for tok in ("\\[", "\\]", "&", "\\begin", "\\end")):
        return False
    return len(sep.strip()) <= 200


def same_equation(sep: str) -> bool:
    """Heuristic: the comment-stripped source between two constructs is a
    single displayed equation's glue iff it contains a brace-top-level `=`, crosses no
    math-mode boundary and no other environment, and is short.  This keeps
    the check to `A = B` pairs like the gauge/blocking benchmarks.

    A complete inline-math atom containing only a bare equality and standard
    math-spacing commands is glue rather than a boundary.  Other inline math
    remains a boundary so formulae between pictures cannot create false
    equation-pair matches.
    """
    if _INLINE_EQUALITY_GLUE.fullmatch(sep.strip()):
        return True
    if any(tok in sep for tok in ("$", "\\[", "\\]", "&", "\\begin", "\\end")):
        return False
    if len(sep.strip()) > 200:
        return False
    depth = 0
    escaped = False
    for char in sep:
        if char == "\\":
            escaped = not escaped
            continue
        if char == "{" and not escaped:
            depth += 1
        elif char == "}" and not escaped:
            depth = max(0, depth - 1)
        elif char == "=" and depth == 0:
            return True
        escaped = False
    return False


# ---------------- CLI ----------------

def main(argv: list[str]) -> int:
    args = [a for a in argv if not a.startswith("-")]
    if "-h" in argv or "--help" in argv or not 1 <= len(args) <= 2:
        print(__doc__.strip().splitlines()[0])
        print("usage: tenkz_audit.py file.tnlog [file.tex]")
        return 0 if ("-h" in argv or "--help" in argv) else 2
    log_path = Path(args[0])
    if not log_path.exists():
        print(f"tenkz_audit: no such file: {log_path}", file=sys.stderr)
        return 2
    if len(args) == 2:
        tex_path: Optional[Path] = Path(args[1])
    else:
        sibling = log_path.with_suffix(".tex")
        tex_path = sibling if sibling.exists() else None
    return Audit(log_path, tex_path).run()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
