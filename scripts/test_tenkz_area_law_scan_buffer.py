#!/usr/bin/env python3
"""Check the area-law scanner and buffered-rectangle diagrams and their render.

Use --source-only when TeX is unavailable; this checks the depth partition,
fronts, charge intervals, nested contours and split supports without claiming
a render. The default also requires complete SVGs and audited event streams.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCAN = ROOT / "blueprint/src/chapter/ch24_peps_area_law_scan_histories.tex"
BUFFER = ROOT / "blueprint/src/chapter/ch24_peps_area_law_initial_buffer.tex"

# Bands g (row 2) and g+1 (row 5); column 2 is depth zero.
SCAN_ENCLOSURES = [
    ("target", "(2,2)", "X"), ("near", "(2,3) .. (2,5)", "U"),
    ("middle", "(2,6) .. (2,11)", "Y"), ("far", "(2,12) .. (2,18)", "V"),
    ("target", "(5,2)", "X"), ("near", "(5,3) .. (5,11)", "U"),
    ("middle", "(5,12) .. (5,17)", "Y"), ("far", "(5,18)", "V"),
]
# Fill arrows start at the front column (first or last column of Y).
SCAN_FRONTS = {
    "scanNearFrontG": ("(1,6)", "(1,7)", "j_P"),
    "scanFarFrontG": ("(1,11)", "(1,10)", "-j_F"),
    "scanNearFrontH": ("(4,12)", "(4,13)", "j_P"),
    "scanFarFrontH": ("(4,17)", "(4,16)", "-j_F"),
}
# Charge intervals with r_0 = D = 1 column: near [j_P-r_0, j_P+D],
# far unsigned [-j_F-D, -j_F+r_0].
SCAN_BRACKETS = ["(2,5) .. (2,7)", "(2,10) .. (2,12)",
                 "(5,11) .. (5,13)", "(5,16) .. (5,18)"]

BUFFER_CONTOURS = [
    ("(4,4) .. (5,5)", "Q_0"), ("(3,3) .. (6,6)", "Q_0^{+d}"),
    ("(2,2) .. (7,7)", "Q_0^{+d'}"), ("(1,1) .. (8,8)", "Q"),
]
BUFFER_SUPPORTS = ["(2,4), (3,4)", "(1,6), (2,6)"]


def block(source: str, start: str, end: str) -> str:
    assert start in source, start
    return source.split(start, 1)[1].split(end, 1)[0]


def units_of(entry: str) -> list[str]:
    return re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", entry, re.S)


def cell(text: str) -> tuple[int, int]:
    r, c = re.fullmatch(r"\((\d+),(\d+)\)", text.strip()).groups()
    return int(r), int(c)


def span(selector: str) -> tuple[tuple[int, int], tuple[int, int]]:
    parts = [p.strip() for p in selector.split("..")]
    return cell(parts[0]), cell(parts[-1])


def check_scan(source: str) -> str:
    entry = block(source, r"\label{def:al_scan_actual_histories}", r"\end{definition}")
    assert "u_g=8gm+m+r_g" in entry and "v_g=8gm+5m+r_g" in entry
    assert r"$X=A\cap T$" in entry and r"$U=P_0\setminus X$" in entry
    assert r"$[j-r_0,j+D]$" in entry
    assert not re.search(r"\\(?:begin\{tikzpicture\}|draw\b|fill\b|node\b)", entry)
    units = units_of(entry)
    assert len(units) == 1, "one scanner picture"
    unit = units[0]
    marks = re.findall(
        r"\\tnmark\[form=enclosure, species=(\w+), tint, label pos=n\]\{([^}]+)\}\{\$([^$]+)\$\}",
        unit)
    assert marks == SCAN_ENCLOSURES, ("depth partition changed", marks)
    for row in (2, 5):
        cols: list[int] = []
        for _, sel, _ in [m for m in marks if span(m[1])[0][0] == row]:
            (_, a), (_, b) = span(sel)
            cols.extend(range(a, b + 1))
        assert cols == list(range(2, 19)), ("parts must tile the depth row", row, cols)
    dots = set(re.findall(r"\\tn\[at=\((\d+),(\d+)\)\]\{\}", unit))
    assert dots == {(str(r), str(c)) for r in (2, 5) for c in range(2, 19)}
    wires = {name: (a, b) for name, a, b in re.findall(
        r"\\tnwire\[kind=string, dir=to, name=(\w+)\]\{([^}]+)\}\{([^}]+)\}", unit)}
    labels = dict(re.findall(
        r"\\tnmark\[form=label, label pos=n\]\{on (\w+) 0\.5\}\{\$([^$]+)\$\}", unit))
    for name, (start, end, label) in SCAN_FRONTS.items():
        assert wires.get(name) == (start, end), ("front arrow", name, wires.get(name))
        assert labels.get(name) == label, ("front label", name)
    for row, near, far in ((2, "scanNearFrontG", "scanFarFrontG"),
                           (5, "scanNearFrontH", "scanFarFrontH")):
        y = [span(s) for sp, s, _ in marks if sp == "middle" and span(s)[0][0] == row][0]
        assert cell(wires[near][0])[1] == y[0][1], "near front is the first column of Y"
        assert cell(wires[far][0])[1] == y[1][1], "far front is the last column of Y"
        assert cell(wires[near][1])[1] > cell(wires[near][0])[1], "near fill increases depth"
        assert cell(wires[far][1])[1] < cell(wires[far][0])[1], "far fill decreases depth"
    brackets = re.findall(
        r"\\tnmark\[form=bracket, species=charge, label pos=s\]\{([^}]+)\}\{\}", unit)
    assert brackets == SCAN_BRACKETS, ("charge intervals changed", brackets)
    assert "\\tnwire[kind=string, dir=to, name=scanDepthAxis]{(7,2)}{(7,18)}" in unit
    assert r"\tnmark[form=label, label pos=e]{(7,18)}{$d$}" in unit
    for phrase in ("Not to scale", "unsigned depth", "boundary signature is empty",
                   "sections/08-scanner.tex"):
        assert phrase in entry, phrase
    return unit


def check_buffer(source: str) -> str:
    entry = block(source, r"\label{thm:area_law_buffer_contours}", r"\end{theorem}")
    assert r"$R=1$, $d=1$" in entry and "$d'=2$" in entry
    assert not re.search(r"\\(?:begin\{tikzpicture\}|draw\b|fill\b|node\b)", entry)
    units = units_of(entry)
    assert len(units) == 1, "one buffer picture"
    unit = units[0]
    assert unit.count(r"\tn{}") == 64 and "bonds=none" in unit
    contours = re.findall(
        r"\\tnmark\[form=enclosure(?:, species=\w+)?(?:, tint)?, label pos=\w+\]"
        r"\{([^}]+)\}\{\$([^$]+)\$\}", unit)
    assert contours == BUFFER_CONTOURS, ("nested contours changed", contours)
    (r0, c0), (r1, c1) = span(BUFFER_CONTOURS[0][0])
    d, d_prime, radius = 1, 2, 1
    assert d + radius <= d_prime
    for (sel, _), k in zip(BUFFER_CONTOURS[1:3], (d, d_prime)):
        assert span(sel) == ((r0 - k, c0 - k), (r1 + k, c1 + k)), ("dilation", sel)
    supports = re.findall(
        r"\\tnmark\[form=enclosure, species=support, tint\]\{\{([^}]+)\}\}\{\}", unit)
    assert supports == BUFFER_SUPPORTS, ("split supports changed", supports)

    def inside(p: tuple[int, int], k: int) -> bool:
        return r0 - k <= p[0] <= r1 + k and c0 - k <= p[1] <= c1 + k

    split_counts = []
    for sup in supports:
        sites = [cell(s) for s in re.findall(r"\(\d+,\d+\)", sup)]
        a, b = sites
        assert abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1, "range-one support is an edge"
        split = [k for k in (d, d_prime) if inside(a, k) != inside(b, k)]
        assert len(split) == 1, ("each support splits exactly one contour", sup, split)
        split_counts.append(split[0])
    assert sorted(split_counts) == [d, d_prime], "one support per contour"
    for phrase in ("Not to scale", "D_0 size(Q)", "sections/02-initial.tex"):
        assert phrase in entry, phrase
    return unit


def check_rejected_mutations(scan: str, buffer: str) -> None:
    for old, new in (
        ("{(2,6) .. (2,11)}{$Y$}", "{(2,7) .. (2,11)}{$Y$}"),
        ("name=scanFarFrontG]{(1,11)}{(1,10)}", "name=scanFarFrontG]{(1,10)}{(1,11)}"),
        ("{on scanFarFrontG 0.5}{$-j_F$}", "{on scanFarFrontG 0.5}{$j_F$}"),
        ("{(2,5) .. (2,7)}{}", "{(2,6) .. (2,7)}{}"),
    ):
        assert old in scan, old
        try:
            check_scan(scan.replace(old, new, 1))
        except AssertionError:
            continue
        raise AssertionError(("scanner mutation accepted", old))
    for old, new in (
        ("{(3,3) .. (6,6)}{$Q_0^{+d}$}", "{(3,3) .. (6,7)}{$Q_0^{+d}$}"),
        ("{{(1,6), (2,6)}}", "{{(1,6), (1,7)}}"),
        ("{{(2,4), (3,4)}}", "{{(2,4), (4,4)}}"),
    ):
        assert old in buffer, old
        try:
            check_buffer(buffer.replace(old, new, 1))
        except AssertionError:
            continue
        raise AssertionError(("buffer mutation accepted", old))


def check_render(units: dict[str, str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
    for name, unit in units.items():
        svg, cold_hit = tenkz_pic.render_unit(unit, output)
        assert svg is not None and svg.is_file(), "production SVG rendering unavailable"
        assert not cold_hit and "<path" in svg.read_text(), "new SVG ink is required"
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, "complete event stream required"
        source = output / f"{name}.tex"
        source.write_text(unit + "\n")
        audit = Audit(log, source)
        audit.run()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        assert not hard, [(f.rule, f.msg) for f in hard]
        events = list(audit.events())
        signatures = [e.attrs["signature"] for e in events if e.kind == "kernel-boundary"]
        assert all(not s for s in signatures), ("geometry pictures have no open indices", signatures)
        print(f"PASS: {name}, audited SVG {svg}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    scan, buffer = SCAN.read_text(), BUFFER.read_text()
    units = {"scan-depth-partition": check_scan(scan),
             "buffer-contours": check_buffer(buffer)}
    check_rejected_mutations(scan, buffer)
    print("PASS: depth partition, fronts, charge intervals, nested dilations, "
          "split supports, seven rejected mutations")
    if args.source_only:
        print("NOT RUN: SVG rendering and event-stream audit (--source-only)")
    elif args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check_render(units, args.output_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_area_law_scan_buffer_") as tmp:
            check_render(units, Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
