#!/usr/bin/env python3
"""Check the dyadic-geometry diagrams of the PEPS approximation chapter.

The four pictures are the normal band words of an edge operation, one stage of
a dyadic level, the central birth, and the point treatment at a true vertex.
The source checks recompute the band words from the births and deaths stated
in the chapter and compare them with the drawn contours, and check the block
labels, the band selections and the interface segments.  Use --source-only
when TeX is unavailable; the default also renders every unit with the
production renderer and requires a tenkz audit without hard findings.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch24_peps_dyadic_geometry.tex"
COLUMNS = 20  # half-unit intervals of x from -8 to 2


def entry(source: str, label: str) -> str:
    start = source.index(r"\label{" + label + "}")
    end = re.compile(r"\\end\{(definition|theorem|lemma)\}").search(source, start)
    assert end, label
    return source[start:end.start()]


def units(text: str) -> list[str]:
    return re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", text, re.S)


def column(x: float) -> int:
    """Column of the half-unit interval (x, x + 1/2)."""
    return int(2 * (x + 8)) + 1


def word_cells(word: list[tuple[str, float, float]]) -> list[str]:
    cells = [""] * COLUMNS
    for letter, a, b in word:
        for c in range(column(a), column(b)):
            cells[c - 1] = letter
    assert all(cells), word
    return cells


def recompute_words() -> list[list[str]]:
    """Seven rows from the operations of def:peps_dyadic_normal_words."""
    def paint(cells, a, b, letter):
        cells = list(cells)
        for c in range(column(a), column(b)):
            cells[c - 1] = letter
        return cells

    start = word_cells([("C", -8, 0), ("A", 0, 1), ("B", 1, 2)])
    aux = ["C"] * COLUMNS
    for letter, a, b in (("B", -6, -1), ("A", -5, -2), ("C", -4, -3)):
        aux = paint(aux, a, b, letter)
    lens = range(column(-7), column(-3.5))
    exchanged = [aux[c] if c + 1 in lens else start[c] for c in range(COLUMNS)]
    rows = [start, aux, exchanged]
    current = exchanged
    for letter, a, b in (("A", -4, 0), ("B", -5, 1), ("C", -3, 0), ("C", -6, -3)):
        current = paint(current, a, b, letter)
        rows.append(current)
    return rows


def drawn_words(unit: str) -> tuple[list[list[str]], tuple[int, int, int]]:
    rows: dict[int, list[str]] = {}
    for species, r, a, r2, b, letter in re.findall(
        r"\\tnmark\[form=enclosure, species=band(\w), tint, label pos=n\]"
        r"\{\((\d+),(\d+)\) \.\. \((\d+),(\d+)\)\}\{\$(\w)\$\}", unit
    ):
        assert species == letter and r == r2, (species, letter, r, r2)
        cells = rows.setdefault(int(r), [""] * COLUMNS)
        for c in range(int(a), int(b) + 1):
            assert not cells[c - 1], ("overlapping bands", r, c)
            cells[c - 1] = letter
    lens = re.findall(
        r"\\tnmark\[form=enclosure, species=lens, label pos=s\]"
        r"\{\((\d+),(\d+)\) \.\. \(\d+,(\d+)\)\}\{\$Y\$\}", unit
    )
    assert len(lens) == 1, lens
    ordered = [rows[r] for r in sorted(rows)]
    for cells in ordered:
        assert all(cells), "a row leaves an interval unlabelled"
    lens_row = sorted(rows).index(int(lens[0][0]))
    return ordered, (lens_row, int(lens[0][1]), int(lens[0][2]))


def check_band_words(unit: str) -> None:
    drawn, (lens_row, first, last) = drawn_words(unit)
    assert drawn == recompute_words(), "band words differ from the stated operations"
    assert lens_row == 1, "the lens is drawn on the auxiliary word"
    assert (first, last) == (column(-7), column(-3.5) - 1), "lens is not (-7,-7/2)"
    for x in range(-8, 3, 2):
        assert "{$" + str(x) + "$}" in unit, x


def check_level(unit: str) -> None:
    boxes = {
        (int(r), int(c)): (label, species)
        for r, c, species, label in re.findall(
            r"\\tn\[at=\((\d),(\d)\)(?:, name=\w+)?, skin=box(?:, species=(\w+))?\]\{([^}]+)\}",
            unit,
        )
    }
    assert set(boxes) == {(r, c) for r in range(2, 6) for c in range(2, 6)}, boxes
    placeholders = set(
        (int(r), int(c)) for r, c in re.findall(r"\\tnmark\[form=label\]\{\((\d),(\d)\)\}\{\$\\ast\$\}", unit)
    )
    assert placeholders == {(r, c) for r in range(1, 7) for c in range(1, 7)} - set(boxes)
    parents = re.findall(r"\\tnmark\[form=enclosure\]\{\((\d),(\d)\) \.\. \((\d),(\d)\)\}\{\}", unit)
    assert sorted(parents) == [("2", "2", "3", "3"), ("2", "4", "3", "5"),
                               ("4", "2", "5", "3"), ("4", "4", "5", "5")], parents
    for (r, c), (label, species) in boxes.items():
        parent = ((r - 2) // 2, (c - 2) // 2)
        if species == "repainted":
            assert parent == (0, 0) and re.fullmatch(r"B_\d", label)
        else:
            # Unrepainted blocks, the current one included, carry the parent label.
            assert label == "A_" + str(2 * parent[0] + parent[1] + 1), (r, c, label)
    current = [cell for cell, (_, species) in boxes.items() if species == "current"]
    assert current == [(2, 4)], current
    west, east, south = boxes[(2, 3)], boxes[(2, 5)], boxes[(3, 4)]
    assert west[1] == "repainted" and east[0] == south[0] == "A_2"
    assert (1, 4) in placeholders


def check_central(unit: str) -> None:
    bands = re.findall(r"species=bandA, tint\]\{\((\d),(\d)\) \.\. \((\d),(\d)\)\}\{\$A\$\}", unit)
    assert sorted(bands) == sorted([("2", "3", "2", "7"), ("8", "3", "8", "7"),
                                    ("3", "2", "7", "2"), ("3", "8", "7", "8")]), bands
    assert re.findall(r"species=bandB, tint\]\{([^}]+)\}\{\$B\$\}", unit) == ["(3,3) .. (7,7)"]
    corners = re.findall(r"\\tn\[at=\((\d),(\d)\), name=centralCorner\w+, skin=dot, species=contact\]", unit)
    assert sorted(corners) == [("2", "2"), ("2", "8"), ("8", "2"), ("8", "8")], corners
    tips = re.findall(r"\\tnwire\[kind=string, species=bandB\]\{centralTip(\w+)\}\{centralCorner(\w+)\}", unit)
    assert len(tips) == 4 and all(a == b for a, b in tips), tips
    assert unit.count(r"{$C_e$}") == 4


def segments(unit: str) -> set[frozenset[tuple[int, int]]]:
    where = {name: (int(r), int(c)) for r, c, name in re.findall(r"\\tn\[at=\((\d),(\d)\), name=(\w+)", unit)}
    found = set()
    for options, a, b in re.findall(r"\\tnwire(\[[^]]*\])?\{(\w+)\.\d+\}\{(\w+)\.\d+\}", unit):
        style = "dashed" if "stroke=dashed" in options else "solid"
        found.add((style, frozenset((where[a], where[b]))))
    return found


def expand(path, style):
    return {(style, frozenset(p)) for p in zip(path, path[1:])}


def check_point_treatment(before: str, after: str) -> None:
    v0, v1 = (5, 5), (5, 7)
    expected_before = (expand([(1, 5), (3, 5), v0, (7, 5), (9, 5)], "solid")
                       | expand([v0, (5, 7), (5, 9)], "solid")
                       | expand([(3, 5), (3, 7), (5, 7), (7, 7), (7, 5), (7, 3), (3, 3), (3, 5)], "dashed"))
    expected_after = (expand([(1, 5), (3, 5), (3, 7), v1, (7, 7), (7, 5), (9, 5)], "solid")
                      | expand([v1, (5, 9)], "solid")
                      | expand([(3, 5), (3, 3), (7, 3), (7, 5)], "dashed"))
    assert segments(before) == expected_before, "interfaces before the treatment"
    assert segments(after) == expected_after, "interfaces after the treatment"
    for unit, v in ((before, v0), (after, v1)):
        assert re.search(r"\\tn\[at=\(%d,%d\), name=\w+V, skin=dot" % v, unit)
        assert len(re.findall(r"skin=dot", unit)) == 1, "one true vertex per panel"
        assert r"species=hole, tint]{%sV}" % ("ptAfter" if v == v1 else "ptBefore") in unit
        assert "species=hole]{(%d,%d) .. (%d,%d)}" % (v[0] - 1, v[1] - 1, v[0] + 1, v[1] + 1) in unit
        for label in ("{(4,2)}{$P$}", "{(2,8)}{$A$}", "{(8,8)}{$B$}"):
            assert label in unit, label
    assert "{(5,4)}{$P$}" in after and "name=ptAfterOld, skin=ring" in after


def check_source(source: str) -> list[str]:
    d1 = units(entry(source, "def:peps_dyadic_normal_words"))
    d5 = units(entry(source, "def:peps_dyadic_block_guide"))
    d6 = units(entry(source, "thm:peps_dyadic_central_clearance"))
    d7 = units(entry(source, "lem:peps_dyadic_rim_pattern"))
    assert (len(d1), len(d5), len(d6), len(d7)) == (1, 1, 1, 2)
    check_band_words(d1[0])
    check_level(d5[0])
    check_central(d6[0])
    check_point_treatment(*d7)
    for label in ("def:peps_dyadic_normal_words", "def:peps_dyadic_block_guide",
                  "thm:peps_dyadic_central_clearance", "lem:peps_dyadic_rim_pattern"):
        text = entry(source, label)
        assert "% Source: OpenAI2026PolynomialPEPS" in text and "% Ink-to-index" in text, label
        assert not re.search(r"\\(?:begin\{tikzpicture\}|draw\b|fill\b|node\b)", text)
    return d1 + d5 + d6 + d7


def check_rejected_mutations(source: str) -> None:
    for old, new in (
        ("{(14,11) .. (14,16)}{$C$}", "{(14,10) .. (14,16)}{$C$}"),  # widen the born C band
        ("{(5,3) .. (5,9)}{$Y$}", "{(5,3) .. (5,10)}{$Y$}"),
        ("species=current]{A_2}", "species=current]{B_5}"),
        ("{(3,3) .. (7,7)}{$B$}", "{(4,4) .. (6,6)}{$B$}"),
        (r"\tnwire{ptAfterV.0}{ptAfter59.180}", r"\tnwire{ptAfter55.0}{ptAfter59.180}"),
    ):
        assert source.count(old) == 1, old
        try:
            check_source(source.replace(old, new, 1))
        except (AssertionError, KeyError, ValueError):
            continue
        raise AssertionError(("mutation accepted", old, new))


def check_render(pictures: list[str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
    names = ["band-words", "dyadic-level", "central-birth", "point-before", "point-after"]
    for name, unit in zip(names, pictures):
        svg, _ = tenkz_pic.render_unit(unit, output)
        assert svg is not None and svg.is_file(), "production SVG rendering unavailable"
        text = svg.read_text()
        assert "<path" in text, "SVG has no ink"
        # Both converters serialize the root extent in points but spell it
        # differently: dvisvgm writes ``width='95.1pt'`` while pdftocairo's
        # cairo SVG surface may drop the ``pt`` unit (a bare user-unit number,
        # still points for a PDF-sourced surface).  Accept either and fall back
        # to the viewBox width (always user units = points), as test_tenkz_pic.
        match = (re.search(r"""<svg[^>]*\swidth=["']([0-9.]+)(?:pt)?["']""", text)
                 or re.search(
                     r"""<svg[^>]*?\sviewBox=["']\s*[-0-9.eE+]+\s+[-0-9.eE+]+\s+([0-9.]+)""",
                     text))
        assert match, "SVG root carries neither a pt width nor a viewBox width"
        width = float(match.group(1))
        assert width <= 345, (name, width, "wider than the text column")
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, "complete event stream required"
        source = output / f"{name}.tex"
        source.write_text(unit + "\n")
        audit = Audit(log, source)
        audit.run()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        assert not hard, (name, hard)
        print(f"PASS: {name}, audited SVG {svg}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    source = CHAPTER.read_text()
    pictures = check_source(source)
    check_rejected_mutations(source)
    print("PASS: recomputed band words, lens, level labels, central bands, "
          "point-treatment interfaces, five rejected mutations")
    if args.source_only:
        print("NOT RUN: SVG rendering and event-stream audit (--source-only)")
    elif args.output_dir:
        output = args.output_dir.resolve()
        output.mkdir(parents=True, exist_ok=True)
        check_render(pictures, output)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_dyadic_geometry_") as tmp:
            check_render(pictures, Path(tmp).resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
