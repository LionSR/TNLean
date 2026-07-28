"""Typed parser for the line-oriented tenkz event log."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable


INT_RE = re.compile(r"-?\d+")
NUMBER_RE = re.compile(r"-?(?:\d+(?:\.\d*)?|\.\d+)")


def _parse_int(value: str) -> int | None:
    if INT_RE.fullmatch(value) is None:
        return None
    try:
        return int(value)
    except ValueError:
        return None


def _is_int(value: str) -> bool:
    return _parse_int(value) is not None


def _is_picture_id(value: str) -> bool:
    """Dialect pictures use integer ids; the kernel prefixes its own with k."""
    if value.startswith("k"):
        return _is_int(value[1:])
    return _is_int(value)


def _is_number(value: str) -> bool:
    return NUMBER_RE.fullmatch(value) is not None


def _is_positive_int(value: str) -> bool:
    parsed = _parse_int(value)
    return parsed is not None and parsed > 0


def _is_nonnegative_int(value: str) -> bool:
    parsed = _parse_int(value)
    return parsed is not None and parsed >= 0


def _is_cell(value: str) -> bool:
    return re.fullmatch(r"\d+-\d+", value) is not None


def _is_lattice_cell(value: str) -> bool:
    return re.fullmatch(r"\d+-\d+(?:-\d+)?", value) is not None


def _is_lattice_cell_list(value: str) -> bool:
    return bool(value) and all(
        _is_lattice_cell(cell.strip()) for cell in value.split(",")
    )


def _is_region_cell_list(value: str) -> bool:
    """A resolved region may be empty; non-empty memberships stay strict."""
    return not value or _is_lattice_cell_list(value)


def _is_pairleg_port(value: str) -> bool:
    """A contraction starts at the centred face or a positive face slot."""
    if value == "center":
        return True
    parsed = _parse_int(value)
    return parsed is not None and parsed > 0


def _enum(*values: str) -> Callable[[str], bool]:
    allowed = set(values)
    return lambda value: value in allowed


def _any(value: str) -> bool:
    return value != ""


def _anything(_value: str) -> bool:
    return True


def _is_kernel_record_id(value: str) -> bool:
    return re.fullmatch(r"(?:atom|wire|mark|frame)-\d+", value) is not None


def _is_address_id(value: str) -> bool:
    return re.fullmatch(r"addr-\d+", value) is not None


def _is_dimension(value: str) -> bool:
    return re.fullmatch(r"-?(?:\d+(?:\.\d*)?|\.\d+)pt", value) is not None


# kind -> {field: validator}; fields absent here are accepted as opaque.
# Numeric slots are validated strictly: they are cell/row coordinates, and
# a coordinate that is not an integer addresses nothing.
FIELD_VALIDATORS: dict[str, dict[str, Callable[[str], bool]]] = {
    "picture": {"id": _is_picture_id, "lang": _any},
    "frame": {
        "picture": _is_picture_id,
        "scope": _enum("picture", "group"),
        "map": _any,
        "a": _is_number,
        "b": _is_number,
        "c": _is_number,
        "d": _is_number,
    },
    "label-use": {"picture": _is_picture_id},
    "label-anchor-site": {
        "picture": _is_picture_id,
        "label": _is_positive_int,
        "x": _is_int,
        "y": _is_int,
    },
    "ink-use": {
        "picture": _is_picture_id,
        "class": _enum("glyph", "wire"),
        "id": _is_positive_int,
        "shape": _enum("rect", "circle", "roundrect", "triangle"),
    },
    "atom": {
        "picture": _is_picture_id,
        "id": _is_kernel_record_id,
        "cell": _is_cell,
        "name": _any,
        "kind": _any,
    },
    "wire": {
        "picture": _is_picture_id,
        "id": _is_kernel_record_id,
        "kind": _enum("index", "string", "pairing"),
        "from": _is_address_id,
        "to": _is_address_id,
        "from-open": _enum("n", "e", "s", "w", "route"),
        "to-open": _enum("n", "e", "s", "w", "route"),
    },
    "mark": {
        "picture": _is_picture_id,
        "id": _is_kernel_record_id,
        "form": _enum("label", "enclosure", "prose"),
    },
    "string": {
        "picture": _is_picture_id,
        "id": _any,
        "kind": _enum("open", "closed", "wind", "around"),
        "pts": _is_positive_int,
    },
    "stringbead": {
        "picture": _is_picture_id,
        "id": _any,
        "t": _is_number,
        "x": _is_dimension,
        "y": _is_dimension,
    },
    "stringcross": {
        "picture": _is_picture_id,
        "under": _any,
        "over": _any,
        "hits": _is_nonnegative_int,
    },
    "kernel-boundary": {
        "picture": _is_picture_id,
        "signature": _anything,
    },
    "check": {
        "relation": _is_positive_int,
        "result": _enum("equal", "mismatch", "off", "malformed"),
        "reason": _any,
        "panels": _is_nonnegative_int,
        "relations": _is_nonnegative_int,
        "signature": _anything,
        "left": _anything,
        "right": _anything,
    },
    "faceports": {
        "picture": _is_picture_id,
        "cell": _is_cell,
        "face": _enum("up", "down", "west", "east"),
        "arity": _is_nonnegative_int,
        "at": _any,
    },
    "pairleg": {
        "picture": _is_picture_id,
        "upper": _is_cell,
        "lower": _is_cell,
        "upper-port": _is_pairleg_port,
        "column": _is_int,
    },
    "bond": {
        "picture": _is_picture_id,
        "row": _is_int,
        "from": _is_int,
        "to": _is_int,
        "dir": _enum("none", "left", "right", "forward", "reverse"),
    },
    "trace": {
        "picture": _is_picture_id,
        "row": _is_int,
        "side": _enum("above", "below"),
        "lang": _enum("lattice"),
        "axis": _enum("west-east", "north-south"),
        "sheet": _is_nonnegative_int,
        "slot": _is_positive_int,
        "from": _is_cell,
        "to": _is_cell,
    },
    "hooks": {
        "picture": _is_picture_id,
        "row": _is_int,
        "side": _enum("above", "below"),
    },
    "pairtrace": {
        "picture": _is_picture_id,
        "row": _is_int,
        "col": _is_int,
        "site": _is_cell,
    },
    "phtrace": {"picture": _is_picture_id, "row": _is_int, "col": _is_int},
    "cup": {
        "picture": _is_picture_id,
        "lang": _enum("lattice"),
        "side": _enum("west", "east", "north", "south"),
        "top": _is_int,
        "bottom": _is_int,
        "cell": _is_cell,
        "sheet-a": _is_int,
        "sheet-b": _is_int,
        "matrix": _is_int,
    },
    "hole": {"picture": _is_picture_id, "row": _is_int, "col": _is_int},
    "warning": {"picture": _is_picture_id, "code": _any},
    "boundary": {
        "picture": _is_picture_id,
        "virtual-west": _is_int,
        "virtual-east": _is_int,
        "virtual-north": _is_int,
        "virtual-south": _is_int,
        "physical-up": _is_int,
        "physical-down": _is_int,
    },
    "bbox": {
        "picture": _is_picture_id,
        "class": _enum("label", "wire"),
        "id": _is_positive_int,
        "xmin": _is_int,
        "xmax": _is_int,
        "ymin": _is_int,
        "ymax": _is_int,
        "shape": _enum("rect", "roundrect"),
        "radius": _is_nonnegative_int,
    },
    "glyph-geometry": {
        "picture": _is_picture_id,
        "owner": _is_positive_int,
        "shape": _enum("rect", "circle", "roundrect", "triangle"),
        "xmin": _is_int,
        "xmax": _is_int,
        "ymin": _is_int,
        "ymax": _is_int,
        "radius": _is_nonnegative_int,
        "stroke": _is_nonnegative_int,
        "x1": _is_int,
        "y1": _is_int,
        "x2": _is_int,
        "y2": _is_int,
        "x3": _is_int,
        "y3": _is_int,
    },
    "wire-geometry": {
        "picture": _is_picture_id,
        "owner": _is_positive_int,
        "shape": _enum("rect-minus-label"),
        "xmin": _is_int,
        "xmax": _is_int,
        "y": _is_int,
        "outer": _is_positive_int,
        "inner": _is_nonnegative_int,
        "cut-shape": _enum("rect", "roundrect"),
        "cut-xmin": _is_int,
        "cut-xmax": _is_int,
        "cut-ymin": _is_int,
        "cut-ymax": _is_int,
        "cut-radius": _is_nonnegative_int,
        "cut-id": _is_positive_int,
    },
    "lattice": {
        "picture": _is_picture_id,
        "rows": _is_positive_int,
        "cols": _is_positive_int,
        "sheets": _is_positive_int,
        "roles": _any,
    },
    "site": {"picture": _is_picture_id, "cell": _is_lattice_cell, "mode": _enum("removed")},
    "region": {
        "picture": _is_picture_id,
        "lang": _enum("free", "lattice"),
        "slot": _enum(
            "selected", "secondary", "complement", "collar", "neutral", "group"
        ),
        "cells": _is_region_cell_list,
        "members": _any,
        "outline": _enum("0", "1"),
        "name": _any,
    },
    "edge": {
        "picture": _is_picture_id,
        "from": _is_lattice_cell,
        "to": _is_lattice_cell,
        "role": _enum("none", "operator", "marked", "extra", "passive"),
    },
    "cdcell": {"picture": _is_picture_id, "index": _is_int},
    "cdobject": {"picture": _is_picture_id, "cell": _is_cell},
    "cdarrow": {"picture": _is_picture_id, "from": _any, "to": _any},
    "cdmap": {
        "picture": _is_picture_id,
        "from": _is_cell,
        "to": _is_cell,
        "fused": _enum("0", "1"),
        "role": _enum("none", "operator", "marked", "extra", "passive"),
        "species": _any,
    },
    "tree": {
        "picture": _is_picture_id,
        "id": _is_positive_int,
        "style": _enum("wire", "ribbon"),
        "leaves": _is_positive_int,
        "vertices": _is_nonnegative_int,
        "topology": _any,
        "role": _enum("none", "operator", "marked", "extra", "passive"),
        "species": _any,
    },
    "join": {"picture": _is_picture_id, "from": _any, "to": _any},
    "span": {
        "picture": _is_picture_id,
        "row": _is_positive_int,
        "col": _is_positive_int,
        "length": _is_positive_int,
        "kind": _enum("brace above", "brace below", "box"),
    },
}


@dataclass
class Event:
    kind: str
    attrs: dict[str, str]
    line: int
    raw: str


@dataclass
class Picture:
    ident: int | str
    lang: str
    line: int
    events: list[Event] = field(default_factory=list)

    def content(self) -> list[Event]:
        """Return events that denote ink rather than derived diagnostics."""
        excluded = {
            "bbox",
            "label-use",
            "label-anchor-site",
            "ink-use",
            "glyph-geometry",
            "wire-geometry",
            "frame",
            "boundary",
            "kernel-boundary",
            "warning",
        }
        return [event for event in self.events if event.kind not in excluded]

    def boundary(self) -> tuple[int, int, int, int] | None:
        for event in self.events:
            if event.kind == "boundary":
                try:
                    return tuple(
                        int(event.attrs[key].strip())
                        for key in (
                            "virtual-west",
                            "virtual-east",
                            "physical-up",
                            "physical-down",
                        )
                    )
                except (KeyError, ValueError):
                    return None
        return None

    def kernel_boundary(self) -> tuple[str, ...] | None:
        """Return the kernel's canonical exposed-index multiset."""
        for event in self.events:
            if event.kind == "kernel-boundary" and "signature" in event.attrs:
                return tuple(
                    item.strip()
                    for item in event.attrs["signature"].split(",")
                    if item.strip()
                )
        return None

    def ncols(self) -> int:
        columns = 0
        for event in self.events:
            if (
                event.kind == "atom"
                and "cell" in event.attrs
                and _is_cell(event.attrs["cell"].strip())
            ):
                columns = max(columns, int(event.attrs["cell"].strip().split("-")[1]))
            elif event.kind == "bond":
                for key in ("from", "to"):
                    value = event.attrs.get(key, "").strip()
                    if _is_int(value):
                        columns = max(columns, int(value))
        return columns


@dataclass
class ParsedLog:
    events: list[Event]
    pictures: list[Picture]
    by_id: dict[int | str, Picture]


FindingCallback = Callable[[str, str, str], None]
EventCallback = Callable[[Event], None]


def _ignore_finding(_rule: str, _where: str, _message: str) -> None:
    pass


def parse_log(
    text: str,
    *,
    source_name: str = "<tnlog>",
    known_langs: set[str] | None = None,
    hard: FindingCallback = _ignore_finding,
    advisory: FindingCallback = _ignore_finding,
    check_event: EventCallback | None = None,
) -> ParsedLog:
    """Parse and validate one complete event stream."""
    events: list[Event] = []
    pictures: list[Picture] = []
    by_id: dict[int | str, Picture] = {}
    # The kernel writes its records inside their picture's group with no
    # picture= field; nesting order is the reference.  Track the open one.
    current_kernel: Picture | None = None
    for line_number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        where = f"{source_name}:{line_number}"
        parts = line.split("|")
        kind = parts[0].strip()
        attrs: dict[str, str] = {}
        valid = True
        for part in parts[1:]:
            if "=" not in part:
                hard(
                    "malformed-event",
                    where,
                    f"bare field {part.strip()!r} (expected key=value): {line}",
                )
                valid = False
                continue
            key, value = part.split("=", 1)
            attrs[key.strip()] = value.strip()
        event = Event(kind, attrs, line_number, line)
        events.append(event)
        validators = FIELD_VALIDATORS.get(kind)
        if validators is None:
            advisory("unknown-event", where, f"unrecognized event kind {kind!r}")
        else:
            for key, value in attrs.items():
                validator = validators.get(key)
                if validator is not None and not validator(value):
                    hard(
                        "malformed-event",
                        where,
                        f"{kind} field {key}={value!r} fails validation: {line}",
                    )
                    valid = False
            if kind != "picture" and "picture" not in attrs:
                if current_kernel is not None and kind in {
                    "atom",
                    "wire",
                    "mark",
                    "frame",
                    "string",
                    "stringbead",
                    "stringcross",
                    "kernel-boundary",
                }:
                    # A kernel record: it belongs to the open kernel picture
                    # by nesting, not by a picture= field.
                    current_kernel.events.append(event)
                    continue
                if kind == "check":
                    if check_event is not None:
                        check_event(event)
                    continue
                hard(
                    "malformed-event",
                    where,
                    f"{kind} event lacks required picture=: {line}",
                )
                valid = False
        if kind == "picture":
            if not valid or "id" not in attrs or not _is_picture_id(attrs["id"]):
                continue
            # Dialect ids stay integers (every existing consumer indexes with
            # them); kernel ids keep their k-prefixed spelling as strings.
            raw_id = attrs["id"]
            picture_id = raw_id if raw_id.startswith("k") else int(raw_id)
            lang = attrs.get("lang", "")
            if known_langs is not None and lang not in known_langs:
                advisory(
                    "unknown-lang",
                    where,
                    f"picture {picture_id} has lang={lang!r}",
                )
            if picture_id in by_id:
                hard(
                    "duplicate-picture",
                    where,
                    f"picture id {picture_id} already declared at line "
                    f"{by_id[picture_id].line}",
                )
                continue
            picture = Picture(picture_id, lang, line_number)
            by_id[picture_id] = picture
            pictures.append(picture)
            current_kernel = picture if lang == "kernel" else None
            continue
        if check_event is not None:
            check_event(event)
        reference = attrs.get("picture", "")
        if not _is_picture_id(reference):
            continue
        picture_id = reference if reference.startswith("k") else int(reference)
        if picture_id == 0 and kind == "tree":
            continue
        if picture_id not in by_id:
            hard(
                "dangling-picture-ref",
                where,
                f"{kind} references undeclared picture {picture_id}",
            )
            continue
        by_id[picture_id].events.append(event)
    return ParsedLog(events, pictures, by_id)
