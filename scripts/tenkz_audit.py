#!/usr/bin/env python3
"""Audit a tenkz `.tnlog` event stream (tenkz spec section 5).

A `.tnlog` is a line-oriented stream `event|key=value|...` written by the
tenkz LaTeX environments.  Every picture opens with `picture|id=N|lang=L`
(langs: grid, cd, lattice, free, planes); subsequent events carry an
explicit `picture=N` back-reference.  `tree|picture=0` marks a `\\tntree`
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
  malformed-region     A lattice region lacks cells= or a free region lacks
                       members=, so its declarative extent is unavailable.
  unknown-region-member
                       A free region references a name before an atom, join,
                       or earlier named region declares it.
  duplicate-enclosure-name
                       Two free atoms, joins, or regions share one semantic
                       enclosure name in a picture.
  duplicate-picture    Two `picture` lines share one id: picture identity
                       is the key of every back-reference.
  conflicting-faceports
                       Two faceports records declare different slots for the
                       same cell face.  The first valid declaration remains
                       authoritative; identical retries are idempotent.
  dangling-picture-ref An event references an undeclared picture.
  empty-picture        A grid/lattice/free picture emitted no content
                       events.  A tensor diagram with no atoms and no
                       regions denotes no tensor network -- historically
                       the "34 fake diagrams" class.
  pairleg-faceport-mismatch
                       A grid pairleg names a contraction slot absent from the
                       upper cell's declared down face.  Explicit declarations
                       resolve `center`, comma-separated slots, `rows`, and
                       `none`.  If no faceports event exists, the check is
                       skipped for compatibility with legacy logs, including
                       simple centred faces.
  label-overlap       A measured `tn label` visible support strictly intersects
                      a sibling glyph node or explicit visible wire node.
  bbox-coverage       A library-owned label, glyph, or wire use did not
                      produce its required measured geometry.
  kernel-crossing     A declared kernel crossing did not produce the
                      recorded under/over occlusion, or hit no intersection.
  kernel-check        A kernel equation check reported a malformed relation
                      or unequal boundary signatures.
  eq-boundary-mismatch Consecutive kernel pictures joined by `=` in the
                       source have different boundary kinds or
                       multiplicities.  A tensor equation equates two maps
                       of one type, so the multisets of open legs must agree
                       side-to-side; their drawing directions may rotate.

Advisories (never affect the exit code):
  eq-boundary-mismatch Consecutive legacy-grid pictures joined by `=` have
                       different directional boundary signatures.
  periodic-no-dots     A traced (periodic) chain of >= 4 columns without
                       an ellipsis cell: a closed word of generic length n
                       drawn with every site reads as fixed length.
  repeated-topology    Identical canonical atom+bond content in several
                       pictures: review ordinary TeX composition.  Repetition
                       alone never extends the public grammar.
  dialect-mismatch     An event kind foreign to its picture's language
                       (each sub-language owns its event dialect).
  unknown-event/lang   Forward-compatibility notes.
  stale-log            The source declares picture constructs but the log
                       has none (failed or interrupted compile).

Source heuristic (documented, deliberately simple): picture-producing
constructs (`\\begin{tenkz...}` and `\\tnpic`) are matched to log pictures
in order of appearance; the match is used only when the counts agree.
Two consecutive grid pictures are "one displayed equation" when the
source between them contains `=` and no math-mode boundary (`$`, `\\[`,
`\\]`), no cell separator `&`, no other environment, and is short.

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
from typing import Optional

from tenkzlib.texcase import Construct, scan_constructs, strip_comments
from tenkzlib.tnlog import (
    FIELD_VALIDATORS,
    Event,
    Picture,
    _is_cell,
    _is_int,
    _is_nonnegative_int,
    _is_pairleg_port,
    _is_positive_int,
    parse_log,
)

# The .tnlog dialect tag each tenkz environment logs -- the single
# argument each sub-language's code passes to `\tenkz@beginpicture` in
# tex/tenkz/*.code.tex (grep `tenkz@beginpicture{` to re-verify). Note
# `tenkzplanes` logs `lattice`, same as `tenkzlattice`: it is a preset
# over the same renderer, not a distinct runtime dialect, even though
# blueprint/src/Packages/tenkz_pic.py independently tags it `planes` for
# a finer CSS modifier class -- that is a presentation-layer distinction
# on top of this table, not a second copy of it; the two need not agree.
# The shared source other scripts (tenkz_lint.py) import.
ENVIRONMENT_LANGS = {
    "tenkz": "grid",
    "tnpic": "grid",
    "tenkzcd": "cd",
    "tenkzlattice": "lattice",
    "tenkzplanes": "lattice",
    "tenkzfree": "free",
}

KNOWN_LANGS = set(ENVIRONMENT_LANGS.values()) | {"kernel"}

# Empty-picture hard check applies exactly to the spec's list (section 5.4).
EMPTY_CHECK_LANGS = {"grid", "lattice", "free", "kernel"}

# Event kinds each dialect is expected to emit -- generated by grepping
# every `\tenkz@event{...}` call site in tex/tenkz/*.code.tex (DESIGN.md
# 5.1 carries the same table; keep the two in step by hand). `warning`
# Geometry/use events, `warning`, and `boundary` are cross-cutting/derived
# and are stripped from a picture's content before this table is consulted
# (see Picture.content), so listing them here is harmless but never load-bearing.
DIALECT_KINDS = {
    "grid": {"atom", "bond", "faceports", "pairleg", "trace", "pairtrace",
             "phtrace", "hooks", "cup", "hole", "span", "warning", "boundary"},
    "free": {"atom", "join", "region"},
    "lattice": {"lattice", "site", "region", "edge", "cup", "trace",
                "pairtrace", "label-anchor-site", "surface", "boundary", "warning"},
    "cd": {"cdcell", "cdobject", "cdarrow", "cdmap", "tree"},
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
        self.log_events = parsed.events
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
                elif e.kind == "atom" and pic.lang in {"grid", "free"}:
                    want = "cell" if pic.lang == "grid" else "name"
                    if want not in e.attrs:
                        self.adv("dialect-mismatch",
                                 f"{self.log_path.name}:{e.line}",
                                 f"atom in {pic.lang} picture {pic.ident} lacks "
                                 f"{want}=")
                elif e.kind == "region" and pic.lang in {"lattice", "free"}:
                    want = "cells" if pic.lang == "lattice" else "members"
                    if want not in e.attrs:
                        self.hard("malformed-region",
                                  f"{self.log_path.name}:{e.line}",
                                  f"region in {pic.lang} picture {pic.ident} "
                                  f"lacks {want}=")

    def check_free_region_names(self) -> None:
        """Validate the ordered named-member grammar recorded by free regions.

        Atom names, optional join names, and optional region names share one
        namespace.  Region members must already be declared, which also makes
        nesting direction explicit and rejects forward/cyclic references.
        """
        for pic in self.pictures:
            if pic.lang != "free":
                continue
            declared: dict[str, Event] = {}
            for event in pic.events:
                name: Optional[str] = None
                if event.kind == "atom":
                    name = event.attrs.get("name")
                elif event.kind == "join":
                    name = event.attrs.get("name")
                elif event.kind == "region":
                    members = [
                        member.strip()
                        for member in event.attrs.get("members", "").split(",")
                        if member.strip()
                    ]
                    for member in members:
                        if member not in declared:
                            self.hard(
                                "unknown-region-member",
                                f"{self.log_path.name}:{event.line}",
                                f"free region references {member!r} before a "
                                "named atom, join, or region declares it",
                            )
                    name = event.attrs.get("name")
                if not name:
                    continue
                if name in declared:
                    self.hard(
                        "duplicate-enclosure-name",
                        f"{self.log_path.name}:{event.line}",
                        f"free enclosure name {name!r} was already declared "
                        f"at line {declared[name].line}",
                    )
                else:
                    declared[name] = event

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
            if not self.require_fields(event, {"result"}, "check"):
                continue
            result = event.attrs["result"]
            if result in {"mismatch", "malformed"}:
                relation = event.attrs.get("relation", "?")
                self.hard(
                    "kernel-check",
                    f"{self.log_path.name}:{event.line}",
                    f"kernel relation {relation} reported result={result}",
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

            label_anchor_sites: dict[int, set[tuple[int, int]]] = {}
            for event in pic.events:
                if event.kind != "label-anchor-site":
                    continue
                if pic.lang != "lattice":
                    self.hard(
                        "dialect-mismatch",
                        f"{self.log_path.name}:{event.line}",
                        "label-anchor-site is valid only in a lattice picture",
                    )
                    continue
                required = {"label", "x", "y"}
                if not self.require_fields(event, required, "label-anchor-site"):
                    continue
                if any(not _is_int(event.attrs[field]) for field in required):
                    continue
                label_id = int(event.attrs["label"])
                if label_id <= 0:
                    continue
                anchor_site = (int(event.attrs["x"]), int(event.attrs["y"]))
                if anchor_site in label_anchor_sites.get(label_id, set()):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} repeats anchor site "
                        f"{anchor_site} for label bbox id={label_id}",
                    )
                    continue
                if label_id not in labels_by_id:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} anchor site references missing "
                        f"label bbox id={label_id}",
                    )
                    continue
                if not any(
                        shape == "circle"
                        and 2 * anchor_site[0] == bounds[0] + bounds[1]
                        and 2 * anchor_site[1] == bounds[2] + bounds[3]
                        for _, shape, bounds, _, _, _ in glyphs):
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} anchor site for label bbox "
                        f"id={label_id} matches no circle glyph center",
                    )
                    continue
                label_anchor_sites.setdefault(label_id, set()).add(anchor_site)

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
                for event, shape, bounds, radius, stroke, points in glyphs:
                    anchor_sites = label_anchor_sites.get(label_id, set())
                    if (shape == "circle" and any(
                            2 * site[0] == bounds[0] + bounds[1]
                            and 2 * site[1] == bounds[2] + bounds[3]
                            for site in anchor_sites)):
                        continue
                    glyph_owner = int(event.attrs["owner"])
                    # A box label is deliberately inscribed in its own glyph.
                    # Partial overlaps and intersections with sibling glyphs
                    # remain reportable.
                    if (shape == "rect" and label_owner > 0
                            and label_owner == glyph_owner
                            and _rect_contains(bounds, label_rect)):
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

    @staticmethod
    def _declared_face_ports(
            event: Event) -> Optional[tuple[set[str], Optional[int]]]:
        """Resolve explicit slots and an optional inclusive `rows` bound."""
        at = event.attrs.get("at", "").strip()
        if at == "center":
            return {"center"}, None
        if at == "none":
            return set(), None
        if at == "rows":
            arity = event.attrs.get("arity", "")
            if not _is_nonnegative_int(arity):
                return None
            count = int(arity)
            # A one-row physical face emits its unique contraction as `center`.
            return ({"center"} if count == 1 else set()), count
        slots = [slot.strip() for slot in at.split(",")]
        if slots and all(
                _is_pairleg_port(slot) and slot != "center" for slot in slots):
            return set(slots), None
        return None

    def check_pairleg_faceports(self) -> None:
        """Cross-check pairleg slots against explicit upper down-face declarations.

        Older event streams did not always emit faceports records.  Absence is
        therefore deliberately not an error; an explicit declaration is the
        authority whenever one is present.
        """
        for pic in self.pictures:
            if pic.lang != "grid":
                continue
            declared: dict[
                tuple[str, str], tuple[set[str], Optional[int], int]
            ] = {}
            for event in pic.events:
                if event.kind != "faceports":
                    continue
                cell = event.attrs.get("cell", "")
                face = event.attrs.get("face", "")
                if (not _is_cell(cell)
                        or face not in {"up", "down", "west", "east"}):
                    continue
                missing = [
                    field for field in ("arity", "at")
                    if field not in event.attrs
                ]
                if missing:
                    fields = ",".join(f"{field}=" for field in missing)
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} face={face} "
                        f"lacks required {fields}",
                    )
                    continue
                at = event.attrs["at"]
                arity = event.attrs["arity"]
                if not at or not _is_nonnegative_int(arity):
                    continue  # FIELD_VALIDATORS already emitted malformed-event.
                declaration = self._declared_face_ports(event)
                if declaration is None:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} "
                        f"face={face} has invalid at={at!r}",
                    )
                    continue
                ports, row_count = declaration
                expected_arity = row_count if row_count is not None else len(ports)
                if int(arity) != expected_arity:
                    self.hard(
                        "malformed-event",
                        f"{self.log_path.name}:{event.line}",
                        f"picture {pic.ident} faceports cell={cell} face={face} "
                        f"declares arity={arity} but at={at!r} resolves to "
                        f"{expected_arity} port(s)",
                    )
                    continue
                key = cell, face
                previous = declared.get(key)
                if previous is None:
                    declared[key] = ports, row_count, event.line
                    continue
                previous_ports, previous_rows, previous_line = previous
                if previous_ports == ports and previous_rows == row_count:
                    continue
                self.hard(
                    "conflicting-faceports",
                    f"{self.log_path.name}:{event.line}",
                    f"picture {pic.ident} cell={cell} face={face} conflicts "
                    f"with its declaration on line {previous_line}",
                )
            for event in pic.events:
                if event.kind != "pairleg":
                    continue
                upper = event.attrs.get("upper", "")
                port = event.attrs.get("upper-port", "")
                down_key = upper, "down"
                if (not _is_cell(upper) or not _is_pairleg_port(port)
                        or down_key not in declared):
                    continue
                ports, row_count, _ = declared[down_key]
                matches = port in ports
                if not matches and row_count is not None and port != "center":
                    matches = row_count != 1 and int(port) <= row_count
                if matches:
                    continue
                available_parts = sorted(
                    ports,
                    key=lambda slot: -1 if slot == "center" else int(slot),
                )
                if row_count is not None:
                    available_parts.append(f"rows 1..{row_count}")
                available = ",".join(available_parts) or "none"
                self.hard(
                    "pairleg-faceport-mismatch",
                    f"{self.log_path.name}:{event.line}",
                    f"picture {pic.ident} pairleg upper={upper} names upper-port={port!r}, "
                    f"but its declared down face has ports {available}",
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
            # A cd parent emits its final addressed edges after all object
            # cells have been typeset.  Grid pictures declared inside that
            # line interval are therefore nested object cells.  Repeating an
            # object in several rows of one map family is the point of a
            # small-multiple diagram, not a candidate for a global named
            # figure definition.
            parents = []
            for pic in pics:
                containing = [
                    parent for parent in self.pictures
                    if parent.lang == "cd"
                    and parent.line < pic.line
                    and parent.content()
                    and pic.line < max(e.line for e in parent.content())
                ]
                parents.append(max(containing, key=lambda p: p.line,
                                   default=None))
            if parents[0] is not None and all(
                    parent is not None
                    and parent.ident == parents[0].ident
                    for parent in parents):
                continue
            ids = ", ".join(str(p.ident) for p in pics)
            self.adv("repeated-topology", self.log_path.name,
                     f"pictures {ids} (lang={lang}) share canonical topology "
                     f"{digest}; keep it inline or use ordinary TeX composition")

    def check_periodic_dots(self) -> None:
        for idx, pic in enumerate(self.pictures):
            if pic.lang != "grid":
                continue
            if not any(e.kind == "trace" for e in pic.events):
                continue
            ncols = pic.ncols()
            if ncols < 4:
                continue
            if self._has_dots_cell(idx, pic, ncols):
                continue
            self.adv("periodic-no-dots", f"{self.log_path.name}:{pic.line}",
                     f"picture {pic.ident}: traced chain of {ncols} columns "
                     f"without an ellipsis cell; a generic-length word should "
                     f"show \\tndots")

    def _has_dots_cell(self, idx: int, pic: Picture, ncols: int) -> bool:
        """Prefer the source (`\\tndots` in the matched body); otherwise use
        the atom-gap proxy: `\\tndots` emits no atom, so a column with no
        atom in any row is an ellipsis candidate.  The proxy over-detects
        (`\\tnX`/`\\tnghost` also emit no atom), so it only ever
        under-reports -- safe for an advisory."""
        if self.tex_linked:
            return re.search(r"\\tndots\b", self.constructs[idx].body) is not None
        cols_with_atoms = {int(e.attrs["cell"].split("-")[1])
                           for e in pic.events
                           if e.kind == "atom" and _is_cell(e.attrs.get("cell", ""))}
        return any(c not in cols_with_atoms for c in range(1, ncols + 1))

    # ---------------- source-linked checks ----------------

    def link_tex(self) -> None:
        if self.tex_path is None or not self.tex_path.exists():
            return
        src = strip_comments(self.tex_path.read_text(encoding="utf-8"))
        self.constructs = scan_constructs(src)
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

    def check_equation_boundaries(self) -> None:
        if not self.tex_linked:
            return
        for i in range(len(self.pictures) - 1):
            a, b = self.pictures[i], self.pictures[i + 1]
            if a.lang != b.lang or a.lang not in {"grid", "kernel"}:
                continue
            ca, cb = self.constructs[i], self.constructs[i + 1]
            if ca.end > cb.start:
                continue  # nested constructs: no linear separator
            sep = self._tex_src[ca.end:cb.start]
            if not same_equation(sep):
                continue
            if a.lang == "kernel":
                # `tenkzeq` already emits the authoritative result after
                # applying `off=` and `modulo=bundles`.  The log-only kernel
                # check consumes that result; do not re-check its raw panel
                # signatures here with less policy information.
                begin_a = self._tex_src.rfind(r"\begin{tenkzeq}", 0, ca.start)
                end_a = self._tex_src.rfind(r"\end{tenkzeq}", 0, ca.start)
                begin_b = self._tex_src.rfind(r"\begin{tenkzeq}", 0, cb.start)
                end_b = self._tex_src.rfind(r"\end{tenkzeq}", 0, cb.start)
                if begin_a > end_a and begin_a == begin_b and begin_b > end_b:
                    continue
            if a.lang == "kernel":
                sig_a, sig_b = a.kernel_boundary(), b.kernel_boundary()
            else:
                sig_a, sig_b = a.boundary(), b.boundary()
            if sig_a is None or sig_b is None or sig_a == sig_b:
                continue
            if a.lang == "kernel":
                # Rotation may change only the direction field.  Everything
                # after it, notably strand weight, remains semantic.
                def without_direction(item: str) -> tuple[str, ...]:
                    parts = item.split(":")
                    kind = parts[0].strip()
                    if kind in {"open", "edge"}:
                        kind = "virtual"
                    weight = (
                        ":".join(parts[2:]).strip()
                        if len(parts) > 2 else "single"
                    )
                    weight = re.sub(r"\s*=\s*", "=", weight)
                    return kind, weight

                kinds_a = Counter(without_direction(item) for item in sig_a)
                kinds_b = Counter(without_direction(item) for item in sig_b)
                if kinds_a == kinds_b:
                    continue
                self.hard("eq-boundary-mismatch",
                          f"{self.log_path.name}:{a.line}",
                          f"pictures {a.ident} and {b.ident} sit on one `=` "
                          f"but open-leg kinds differ: {sig_a} vs {sig_b} "
                          f"[{self.tex_path.name}:{ca.line}]")
            else:
                self.adv("eq-boundary-mismatch",
                         f"{self.log_path.name}:{a.line}",
                         f"pictures {a.ident} and {b.ident} sit on one `=` "
                         f"but open-leg signatures differ: {sig_a} vs "
                         f"{sig_b} [{self.tex_path.name}:{ca.line}]")

    # ---------------- driver ----------------

    def run(self) -> int:
        self.parse_log()
        self.link_tex()
        self.check_empty_pictures()
        self.check_dialects()
        self.check_free_region_names()
        self.check_kernel_crossings()
        self.check_kernel_checks()
        self.check_bbox_coverage()
        self.check_label_overlaps()
        self.check_pairleg_faceports()
        self.check_equation_boundaries()
        self.check_periodic_dots()
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
    """Order-free digest of a picture's content.  Attributes are sorted,
    the `picture` back-reference is dropped (identity must not depend on
    position in the document), and `dir=none` is normalized away so logs
    from emitters before the `dir` attribute hash identically."""
    lines = []
    for e in pic.content():
        attrs = {k: v for k, v in e.attrs.items() if k != "picture"}
        if e.kind == "bond" and attrs.get("dir") == "none":
            del attrs["dir"]
        if e.kind == "faceports":
            at = attrs.get("at", "")
            try:
                if at == "rows":
                    slots = range(1, int(attrs["arity"]) + 1)
                    attrs["at"] = ",".join(str(slot) for slot in slots)
                elif at not in {"center", "none"}:
                    slots = sorted({int(slot) for slot in at.split(",")})
                    attrs["at"] = ",".join(str(slot) for slot in slots)
            except (KeyError, ValueError):
                pass  # malformed fields are reported by the parser
        lines.append(e.kind + "|" + "|".join(
            f"{k}={v}" for k, v in sorted(attrs.items())))
    payload = "\n".join(sorted(lines)).encode("utf-8")
    return hashlib.sha1(payload).hexdigest()[:12]


# ---------------- TeX source scanning ----------------

_INLINE_EQUALITY_SPACE = r"(?:\s|\\[,;:!]|\\(?:quad|qquad)\b)*"
_INLINE_EQUALITY_GLUE = re.compile(
    rf"\${_INLINE_EQUALITY_SPACE}={_INLINE_EQUALITY_SPACE}\$"
)


def same_equation(sep: str) -> bool:
    """Heuristic: the comment-stripped source between two constructs is a
    single displayed equation's glue iff it contains `=`, crosses no
    math-mode boundary and no other environment, and is short.  This keeps
    the check to `A = B` pairs like the gauge/blocking benchmarks.

    A complete inline-math atom containing only a bare equality and standard
    math-spacing commands is glue rather than a boundary.  Other inline math
    remains a boundary so formulae between pictures cannot create false
    equation-pair matches.
    """
    if _INLINE_EQUALITY_GLUE.fullmatch(sep.strip()):
        return True
    if "=" not in sep:
        return False
    if any(tok in sep for tok in ("$", "\\[", "\\]", "&", "\\begin", "\\end")):
        return False
    return len(sep.strip()) <= 200


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
