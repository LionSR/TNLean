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
    """Kernel pictures use k-prefixed ids; plain integers remain accepted."""
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


def _is_sp_point(value: str) -> bool:
    """An exact picture-space point, two scaled-point integers."""
    return re.fullmatch(r"-?\d+,-?\d+", value) is not None


def _is_sp_end(value: str) -> bool:
    """A closure end: a measured point, or the word for a row that has none."""
    return value == "none" or _is_sp_point(value)


def _is_sp_standoff(value: str) -> bool:
    """A closure standoff: a page distance, or the word for a frame arc."""
    return value == "none" or _is_nonnegative_int(value)


def _is_sp_polyline(value: str) -> bool:
    """A measured contour: at least two points, semicolon separated."""
    parts = value.split(";")
    return len(parts) >= 2 and all(_is_sp_point(part) for part in parts)


# kind -> {field: validator}; fields absent here are accepted as opaque.
# Numeric slots are validated strictly: they are cell/row coordinates, and
# a coordinate that is not an integer addresses nothing.
FIELD_VALIDATORS: dict[str, dict[str, Callable[[str], bool]]] = {
    "picture": {
        "id": _is_picture_id,
        "lang": _any,
        "scope": _is_positive_int,
    },
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
        # "up" and "down" are the plane frame's independent transverse
        # physical axis; the page compass carries every other end.
        "from-open": _enum(
            "n", "ne", "e", "se", "s", "sw", "w", "nw", "up", "down", "route"
        ),
        "to-open": _enum(
            "n", "ne", "e", "se", "s", "sw", "w", "nw", "up", "down", "route"
        ),
    },
    "mark": {
        "picture": _is_picture_id,
        "id": _is_kernel_record_id,
        "form": _enum("label", "enclosure", "bracket", "prose"),
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
        "scope": _is_positive_int,
        "relation": _is_positive_int,
        "product": _is_cell,
        "result": _enum("equal", "mismatch", "off", "malformed", "contracted"),
        "reason": _any,
        "panels": _is_nonnegative_int,
        "relations": _is_nonnegative_int,
        "interface": _anything,
        "signature": _anything,
        "left": _anything,
        "right": _anything,
    },
    "warning": {"picture": _is_picture_id, "code": _any},
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
    "closure-rail": {
        "picture": _is_picture_id,
        "name": _any,
        "row": _is_positive_int,
        "side": _enum("west-east"),
        "west": _is_sp_end,
        "east": _is_sp_end,
        "stroke": _is_nonnegative_int,
        "clear": _is_sp_standoff,
        "points": _is_sp_polyline,
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
}

# Fields whose absence makes an otherwise typed event unusable.  Most event
# kinds are picture records and use the shared picture= requirement below;
# equation checks are top-level records whose scope is their ownership key and
# whose result determines whether the record can authorize a boundary check.
REQUIRED_FIELDS: dict[str, frozenset[str]] = {
    "check": frozenset({"scope", "result"}),
    "closure-rail": frozenset(
        {"name", "row", "side", "west", "east", "stroke", "clear", "points"}),
}

REQUIRED_CHECK_FIELDS_BY_RESULT: dict[str, frozenset[str]] = {
    "equal": frozenset({"relation", "signature"}),
    "off": frozenset({"relation", "reason"}),
    "malformed": frozenset({"reason", "panels", "relations"}),
    "contracted": frozenset({"product", "signature"}),
}
# A mismatch names the joiner it rejects: the relation ordinal, or the
# contracted product pair when the facing cuts of a product group fail to
# cancel.  Either field satisfies the requirement; a mismatch naming
# neither is unusable.

# Equation checks are scope-owned top-level records.  A picture= field would
# give them a second, conflicting owner and must never enter semantic checks.
FORBIDDEN_FIELDS: dict[str, frozenset[str]] = {
    "check": frozenset({"picture"}),
}

# A check record names the one joiner it resolved: a relation it compared or a
# product interface it contracted.  Carrying both would let one record stand
# for two joiners and close a scope that recorded only one of them.
EXCLUSIVE_FIELDS: dict[str, frozenset[str]] = {
    "check": frozenset({"relation", "product"}),
}


@dataclass
class Event:
    kind: str
    attrs: dict[str, str]
    line: int
    raw: str
    valid: bool = True  # False when canonical parsing rejects the record.


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
            "ink-use",
            "glyph-geometry",
            "wire-geometry",
            "closure-rail",
            "frame",
            "kernel-boundary",
            "warning",
        }
        return [event for event in self.events if event.kind not in excluded]

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


@dataclass
class ParsedLog:
    events: list[Event]
    pictures: list[Picture]
    by_id: dict[int | str, Picture]

    @property
    def valid_events(self) -> list[Event]:
        """Return only records accepted by the canonical parser."""
        return [event for event in self.events if event.valid]


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
            key = key.strip()
            if key in attrs:
                hard(
                    "malformed-event",
                    where,
                    f"duplicate field {key!r}: {line}",
                )
                valid = False
                continue
            attrs[key] = value.strip()
        event = Event(kind, attrs, line_number, line, valid)
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
            required = set(REQUIRED_FIELDS.get(kind, frozenset()))
            if kind == "check":
                result = attrs.get("result", "")
                required.update(
                    REQUIRED_CHECK_FIELDS_BY_RESULT.get(result, frozenset())
                )
                if result == "mismatch" and "product" not in attrs:
                    required.add("relation")
            missing = sorted(required - attrs.keys())
            if missing:
                hard(
                    "malformed-event",
                    where,
                    f"{kind} event lacks required field(s): {', '.join(missing)}: {line}",
                )
                valid = False
            forbidden = sorted(FORBIDDEN_FIELDS.get(kind, frozenset()) & attrs.keys())
            if forbidden:
                hard(
                    "malformed-event",
                    where,
                    f"{kind} event forbids field(s): {', '.join(forbidden)}: {line}",
                )
                valid = False
            exclusive = sorted(EXCLUSIVE_FIELDS.get(kind, frozenset()) & attrs.keys())
            if len(exclusive) > 1:
                hard(
                    "malformed-event",
                    where,
                    f"{kind} event names more than one joiner: "
                    f"{', '.join(exclusive)}: {line}",
                )
                valid = False
            event.valid = valid
            if kind == "check":
                # A scope-owned equation check is emitted outside every panel
                # and therefore closes the preceding kernel picture even when
                # the check itself is malformed.
                current_kernel = None
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
                    if event.valid:
                        current_kernel.events.append(event)
                    continue
                if kind == "check":
                    if check_event is not None and event.valid:
                        check_event(event)
                    continue
                hard(
                    "malformed-event",
                    where,
                    f"{kind} event lacks required picture=: {line}",
                )
                valid = False
                event.valid = False
        if kind == "picture":
            # Every picture header ends the preceding picture's implicit
            # ownership, even when the new header is malformed or duplicate.
            current_kernel = None
            if not valid or "id" not in attrs or not _is_picture_id(attrs["id"]):
                event.valid = False
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
                event.valid = False
                continue
            picture = Picture(picture_id, lang, line_number)
            by_id[picture_id] = picture
            pictures.append(picture)
            current_kernel = picture if lang == "kernel" else None
            continue
        reference = attrs.get("picture", "")
        if not _is_picture_id(reference):
            continue
        picture_id = reference if reference.startswith("k") else int(reference)
        if picture_id == 0 and kind == "tree":
            if check_event is not None and event.valid:
                check_event(event)
            continue
        if picture_id not in by_id:
            hard(
                "dangling-picture-ref",
                where,
                f"{kind} references undeclared picture {picture_id}",
            )
            event.valid = False
            continue
        if not event.valid:
            continue
        if check_event is not None:
            check_event(event)
        by_id[picture_id].events.append(event)
    return ParsedLog(events, pictures, by_id)
