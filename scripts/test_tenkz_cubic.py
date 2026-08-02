#!/usr/bin/env python3
"""Source-level topology regression for the declared cubic network."""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from tenkzlib.texcase import (
    following_group_span,
    scan_constructs,
    strip_comments,
    top_level_options,
)


ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    ROOT / "tex/tenkz/examples/cubic-lattice.tex",
    ROOT / "tests/tenkz/fig21d_cubic.tex",
    ROOT / "tests/tenkz/fig21d_cubic_v2.tex",
)
ADDRESS = tuple[int, int, int]
EDGE = tuple[ADDRESS, ADDRESS]
EXPECTED_ADDRESSES = set(product(range(1, 4), repeat=3))
EXPECTED_BY_AXIS: dict[str, set[EDGE]] = {
    "column": {
        ((row, col, member), (row, col + 1, member))
        for row in range(1, 4)
        for col in range(1, 3)
        for member in range(1, 4)
    },
    "row": {
        ((row, col, member), (row + 1, col, member))
        for row in range(1, 3)
        for col in range(1, 4)
        for member in range(1, 4)
    },
    "member": {
        ((row, col, member), (row, col, member + 1))
        for row in range(1, 4)
        for col in range(1, 4)
        for member in range(1, 3)
    },
}
EXPECTED_EDGES = set().union(*EXPECTED_BY_AXIS.values())
EXPECTED_MARKED = ((2, 1, 2), (2, 2, 2))
EXPECTED_PICTURE_OPTIONS = {
    "rows": "{wire,wire,wire}",
    "cols": "3",
    "bonds": "none",
    "west": "none",
    "east": "none",
    "north": "none",
    "south": "none",
    "frame": "{plane,basis={wireat(0,0),wireat(-3,5),wireat(-6,10)}}",
}


@dataclass(frozen=True)
class Topology:
    edges: frozenset[EDGE]
    marked: EDGE


def fail(path: Path, message: str) -> None:
    raise AssertionError(f"{path.relative_to(ROOT)}: {message}")


def compact(value: str | None) -> str:
    return re.sub(r"\s+", "", value or "")


def parse_address(path: Path, text: str) -> ADDRESS:
    match = re.fullmatch(
        r"\(\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*\)",
        text,
    )
    if match is None:
        fail(path, f"nonliteral wire endpoint {text!r}")
    return tuple(map(int, match.groups()))  # type: ignore[return-value]


def normalize_edge(left: ADDRESS, right: ADDRESS) -> EDGE:
    return tuple(sorted((left, right)))  # type: ignore[return-value]


def parse_wire(path: Path, body: str, start: int) -> tuple[EDGE, bool, int]:
    position = start + len(r"\tnwire")
    options_group = following_group_span(body, position, "[", "]")
    options = ""
    if options_group is not None:
        options, position = options_group
    left_group = following_group_span(body, position, "{", "}")
    if left_group is None:
        fail(path, "tnwire lacks its first endpoint")
    left_text, position = left_group
    right_group = following_group_span(body, position, "{", "}")
    if right_group is None:
        fail(path, "tnwire lacks its second endpoint")
    right_text, position = right_group

    parsed_options = top_level_options(options)
    marked = parsed_options == [("species", "marked")]
    if parsed_options and not marked:
        fail(path, f"unsupported wire options {parsed_options!r}")
    edge = normalize_edge(
        parse_address(path, left_text), parse_address(path, right_text)
    )
    return edge, marked, position


def compare_edges(path: Path, counts: Counter[EDGE]) -> None:
    missing = sorted(EXPECTED_EDGES - set(counts))
    extra = sorted(set(counts) - EXPECTED_EDGES)
    duplicated = sorted((edge, count) for edge, count in counts.items() if count != 1)
    if missing or extra or duplicated:
        fail(
            path,
            f"topology mismatch; missing={missing}, extra={extra}, "
            f"multiplicity={duplicated}",
        )


def inspect(path: Path) -> Topology:
    source = strip_comments(path.read_text(encoding="utf-8"))
    if len(re.findall(r"\\tenkzkernel\b", source)) != 1:
        fail(path, "expected one literal tenkzkernel switch")
    if re.search(r"\\(?:tenkzlattice|tnedge|tnsite|tnset)\b", source):
        fail(path, "legacy or per-picture metric spelling remains")
    if re.search(
        r"\\(?:def|edef|gdef|xdef|let|newcommand|renewcommand|"
        r"providecommand|NewDocumentCommand|RenewDocumentCommand)\b",
        source,
    ):
        fail(path, "local command definition or rebinding remains")
    if re.search(r"\b(?:role|sheet\s+vector|plane\s+(?:slant|rise))\s*=", source):
        fail(path, "legacy role or projection tuning remains")
    pictures = [item for item in scan_constructs(source) if item.name == "tenkz"]
    if len(pictures) != 1:
        fail(path, f"expected one tenkz picture, found {len(pictures)}")
    picture = pictures[0]
    picture_source = source[picture.start : picture.end]
    if re.search(
        r"(?<![A-Za-z])[0-9]+(?:\.[0-9]+)?\s*(?:mm|cm|pt|em|ex)\b",
        picture_source,
    ):
        fail(path, "raw TeX length remains in the picture")
    begin = re.search(r"\\begin\{tenkz\}", source[picture.start : picture.body_start])
    if begin is None:
        fail(path, "could not locate the tenkz option list")
    option_position = picture.start + begin.end()
    option_group = following_group_span(source, option_position, "[", "]")
    if option_group is None:
        fail(path, "tenkz picture lacks explicit options")
    options, _option_end = option_group
    parsed_options = top_level_options(options)
    keys = [key for key, _value in parsed_options]
    if len(keys) != len(set(keys)):
        fail(path, f"duplicate picture options {keys!r}")
    normalized_options = {key: compact(value) for key, value in parsed_options}
    if normalized_options != EXPECTED_PICTURE_OPTIONS:
        fail(
            path,
            f"picture options differ; expected={EXPECTED_PICTURE_OPTIONS}, "
            f"actual={normalized_options}",
        )

    body = picture.body
    wire_tokens = list(re.finditer(r"\\tnwire\b", source))
    body_end = picture.body_start + len(body)
    if len(wire_tokens) != 54 or any(
        not picture.body_start <= match.start() < body_end
        for match in wire_tokens
    ):
        fail(path, "expected exactly 54 tnwire tokens, all inside the picture")
    spans: list[tuple[int, int]] = []
    counts: Counter[EDGE] = Counter()
    marked_edges: list[EDGE] = []
    for match in re.finditer(r"\\tnwire\b", body):
        edge, marked, end = parse_wire(path, body, match.start())
        spans.append((match.start(), end))
        counts[edge] += 1
        if marked:
            marked_edges.append(edge)
    compare_edges(path, counts)

    addresses = {address for edge in counts for address in edge}
    if addresses != EXPECTED_ADDRESSES:
        fail(
            path,
            f"address set mismatch; missing={sorted(EXPECTED_ADDRESSES - addresses)}, "
            f"extra={sorted(addresses - EXPECTED_ADDRESSES)}",
        )
    axis_counts = {
        axis: sum(edge in expected for edge in counts)
        for axis, expected in EXPECTED_BY_AXIS.items()
    }
    if axis_counts != {"column": 18, "row": 18, "member": 18}:
        fail(path, f"axis counts differ: {axis_counts}")
    if marked_edges != [EXPECTED_MARKED]:
        fail(path, f"marked edge differs: {marked_edges}")

    residue = list(body)
    for start, end in spans:
        residue[start:end] = " " * (end - start)
    if "".join(residue).strip():
        fail(path, "picture body contains nonliteral topology or other residue")
    return Topology(frozenset(counts), marked_edges[0])


def main() -> int:
    topologies = [inspect(path) for path in SOURCES]
    if len(set(topologies)) != 1:
        raise AssertionError("cubic example and regression twins differ")
    print(
        "PASS: three cubic sources declare the same 27 sites, "
        "54 edges (18 per axis), and one middle-layer marked edge"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
