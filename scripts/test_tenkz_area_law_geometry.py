#!/usr/bin/env python3
"""Check the four area-law geometry pictures and their production render.

The pictures are the dyadic layer, the primary regions of a pitch interior,
the fan of a belt cell and the active rays near an initial mark. Use
--source-only when TeX is unavailable; this checks the drawn cell sets, rays
and labels against the chapter's definitions and rejects source mutations
without claiming a render. The default also requires complete SVGs and
audited event streams with no hard finding.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter"
ENTRIES = {
    "layers": ("ch24_peps_area_law_dyadic_layers.tex",
               "def:area_law_dyadic_layers", "definition"),
    "primary": ("ch24_peps_area_law_primary_regions.tex",
                "def:area_law_primary_regions", "definition"),
    "fan": ("ch24_peps_area_law_cell_fans.tex", "def:area_law_cell_fan", "definition"),
    "rays": ("ch24_peps_area_law_initial_active_rays.tex",
             "thm:area_law_initial_active_radial", "theorem"),
}
CORNERS = {(1, 1), (1, 9), (9, 9), (9, 1)}
MIDPOINTS = {(1, 5), (5, 9), (9, 5), (5, 1)}
BEARING = {(1, 1): 135, (1, 5): 90, (1, 9): 45, (5, 9): 0,
           (9, 9): 315, (9, 5): 270, (9, 1): 225, (5, 1): 180}
PERIMETER = [(1, 1), (1, 5), (1, 9), (5, 9), (9, 9), (9, 5), (9, 1), (5, 1)]


def entry_unit(name: str, source: str | None = None) -> str:
    fname, label, env = ENTRIES[name]
    text = source if source is not None else (CHAPTER / fname).read_text()
    body = text.split(r"\label{" + label + "}", 1)[1].split(r"\end{" + env + "}", 1)[0]
    units = re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", body, re.S)
    assert len(units) == 1, (name, "one picture inside the entry", len(units))
    comments = re.findall(r"^\s*%\s*(.*)$", body, re.M)
    assert any("Source: 10-geometry.tex" in c for c in comments), (name, "source comment")
    assert any("Ink-to-index" in c for c in comments), (name, "ink comment")
    assert any("boundary signature" in c for c in comments), (name, "signature comment")
    return units[0]


def cells(a: str, b: str) -> set[tuple[int, int]]:
    (r1, c1), (r2, c2) = (tuple(map(int, x.split(","))) for x in (a, b))
    return {(r, c) for r in range(r1, r2 + 1) for c in range(c1, c2 + 1)}


def selection(text: str) -> set[tuple[int, int]]:
    terms = [t.strip() for t in text.split(" - ")]
    out = set()
    for i, term in enumerate(terms):
        m = re.fullmatch(r"\((\d+,\d+)\) \.\. \((\d+,\d+)\)", term)
        assert m, term
        block = cells(m[1], m[2])
        out = block if i == 0 else out - block
    return out


def enclosures(unit: str) -> list[tuple[str, bool, set[tuple[int, int]], str]]:
    found = []
    for opts, target, label in re.findall(
            r"\\tnmark\[form=enclosure,([^]]*)\]\{([^{}]*)\}\{((?:[^{}]|\{[^{}]*\})*)\}",
            unit):
        species = re.search(r"species=([\w-]+)", opts)[1]
        found.append((species, "tint" in opts, selection(target), label))
    return found


def check_layers(unit: str) -> None:
    # Scale-k cells: row r and column c carry the index (r, c), so parents
    # pair the columns (2m, 2m+1).
    marks = enclosures(unit)
    occupied = re.findall(r"\\tn\[at=\((\d+),(\d+)\), skin=dot, species=endpoint\]", unit)
    assert occupied == [("5", "5")], occupied
    z = (5, 5)  # index of the occupied cell
    C0 = 1
    pk = {(a, b) for a in range(z[0] - C0, z[0] + C0 + 1) for b in range(z[1] - C0, z[1] + C0 + 1)}
    pz = (z[0] // 2, z[1] // 2)
    pk1 = {(a, b) for a in range(pz[0] - C0, pz[0] + C0 + 1)
           for b in range(pz[1] - C0, pz[1] + C0 + 1)}
    nk = pk
    nk1 = {(r, c) for a, b in pk1 for r in (2 * a, 2 * a + 1) for c in (2 * b, 2 * b + 1)}
    tinted = {sp: sel for sp, tint, sel, _ in marks if tint}
    assert tinted == {"selected": nk, "secondary": nk1 - nk}, "N_k and the ring D_k"
    parents = [sel for sp, tint, sel, _ in marks if sp == "complement"]
    expected = [{(r, c) for r in (2 * a, 2 * a + 1) for c in (2 * b, 2 * b + 1)}
                for a, b in sorted(pk1)]
    assert sorted(map(sorted, parents)) == sorted(map(sorted, expected)), "nine parent cells"
    assert set().union(*parents) == nk1
    assert re.search(r"form=bracket[^]]*\]\{\(2,2\) \.\. \(7,7\)\}\{\$N_\{k\+1\}\$\}", unit)
    for label in (r"$D_k$", r"$N_k$"):
        assert unit.count("{" + label + "}") == 1, label
    assert r"\tnwire" not in unit


def check_primary(unit: str) -> None:
    # Fine squares of side t; columns = first coordinate index, rows 4..1 =
    # second coordinate index 0..3; s = 4t, r = 2t, shifts a = b = 0.
    def fine(col: int, row: int) -> tuple[int, int]:
        return (4 - row, col)

    belt = {(r, c) for r in range(1, 5) for c in range(1, 9)
            if (c - 1) % 4 == 0 or (4 - r) % 4 == 0}
    interiors = {j: {(r, c) for r in range(1, 5) for c in range(1, 9)
                     if (r, c) not in belt and (c - 1) // 4 == j} for j in (0, 1)}
    marks = enclosures(unit)
    assert [sel for sp, t, sel, _ in marks if sp == "belt"] == [belt], "belt strips"
    assert [(sel, lab) for sp, t, sel, lab in marks if sp == "selected"] == [
        (interiors[0], "$U_j$"), (interiors[1], "$U_{j'}$")], "pitch interiors"
    layer_cells = [{(1, 3), (1, 4), (2, 3), (2, 4)}, {(3, 3), (3, 4), (4, 3), (4, 4)},
                   {(1, 5), (1, 6), (2, 5), (2, 6)}]
    for cell in layer_cells:  # every drawn r-cell is aligned to the 2t mesh
        cols = sorted({c for _, c in cell}); rows = sorted({fine(c, r)[0] for r, c in cell})
        assert (cols[0] - 1) % 2 == 0 and rows[0] % 2 == 0, cell
    fragments = sorted(map(sorted, (cell & interiors[j] for cell in layer_cells for j in (0, 1)
                                    if cell & interiors[j])))
    drawn = sorted(map(sorted, (sel for sp, t, sel, _ in marks if sp == "layer")))
    assert drawn == fragments and all(t for sp, t, _, _ in marks if sp == "layer"), drawn
    dashed = [sel for sp, t, sel, _ in marks if sp == "complement"]
    assert sorted(map(sorted, dashed)) == sorted(map(sorted, layer_cells[1:])), "straddling cells"
    assert unit.count("{$R_j$}") == 2 and unit.count("{$R_{j'}$}") == 1


def rays(unit: str, centre: str) -> dict[tuple[int, int], str]:
    names = {n: (int(r), int(c)) for r, c, n in
             re.findall(r"\\tn\[at=\((\d+),(\d+)\), name=(\w+)", unit)}
    assert names[centre] == (5, 5)
    assert set(names.values()) == CORNERS | MIDPOINTS | {(5, 5)}, "the nine marks"
    out = {}
    sides = []
    for opts, a, pa, b, pb in re.findall(
            r"\\tnwire\[([^]]*)\]\{(\w+)\.(\d+)\}\{(\w+)\.(\d+)\}", unit):
        if a == centre:
            p = names[b]
            assert int(pa) == BEARING[p] and int(pb) == (BEARING[p] + 180) % 360, (a, b)
            stroke = re.search(r"stroke=(\w+)", opts)
            out[p] = stroke[1] if stroke else "solid"
        else:
            sides.append((names[a], names[b]))
    expected = [(PERIMETER[i], PERIMETER[(i + 1) % 8]) for i in range(8)]
    assert sides == expected, "the eight half sides of the square"
    return out


def check_fan(unit: str) -> None:
    drawn = rays(unit, "fanc")
    # Upper and right sides halved; lower and left sides whole.
    assert drawn == {p: "solid" for p in CORNERS | {(1, 5), (5, 9)}}, drawn
    assert 4 <= len(drawn) <= 8 and len(drawn) == 6
    for cell, label in (((1, 1), "a_e"), ((1, 5), "b_e"), ((5, 5), "c"),
                        ((3, 4), "P_e"), ((8, 5), "P_{e'}"), ((9, 9), "Q")):
        assert re.search(r"\\tnmark\[form=label[^]]*\]\{\(%d,%d\)\}\{\$%s\$\}"
                         % (cell[0], cell[1], re.escape(label)), unit), label


def check_rays(unit: str) -> None:
    drawn = rays(unit, "starc")
    sectors = [(p, re.search(r"\{\((%d),(%d)\)\}\{\$(i_\d)\$\}" % cell, unit)[3])
               for p, cell in enumerate([(3, 4), (3, 6), (4, 8), (7, 8),
                                         (8, 6), (8, 4), (7, 2), (4, 2)])]
    ids = [i for _, i in sectors]
    # Sector s spans PERIMETER[s] -> PERIMETER[s+1]; ray to PERIMETER[s+1]
    # separates sector s from sector s+1 and is active iff identifiers differ.
    for s in range(8):
        endpoint = PERIMETER[(s + 1) % 8]
        active = ids[s] != ids[(s + 1) % 8]
        assert drawn[endpoint] == ("solid" if active else "dashed"), (endpoint, ids)
    # Colors alternate across active rays, so the number of transitions is
    # even. One identifier may recur in separate runs, and a single identifier
    # on all eight sectors (no active ray) is allowed.
    runs = sum(ids[s] != ids[(s + 1) % 8] for s in range(8))
    assert runs % 2 == 0, ids


CHECKS = {"layers": check_layers, "primary": check_primary, "fan": check_fan, "rays": check_rays}


def check_source() -> dict[str, str]:
    units = {}
    for name, check in CHECKS.items():
        units[name] = entry_unit(name)
        check(units[name])
    return units


def check_rejected_mutations(units: dict[str, str]) -> int:
    mutations = [
        ("layers", "(4,4) .. (6,6)}{}", "(3,3) .. (5,5)}{}"),
        ("layers", "{(6,6) .. (7,7)}{}", "{(5,5) .. (6,6)}{}"),
        ("primary", "{(3,3) .. (3,4)}{}", "{(3,3) .. (4,4)}{}"),
        ("primary", "- (1,6) .. (3,8)}{}", "- (1,6) .. (4,8)}{}"),
        ("fan", "{fanc.90}{fann.270}", "{fanc.270}{fans.90}"),
        ("fan", "{$P_e$}", "{$P_{e'}$}"),
        ("rays", "stroke=dashed, name=starrayn]", "name=starrayn]"),
        ("rays", "{(8,4)}{$i_3$}", "{(8,4)}{$i_2$}"),
    ]
    for name, old, new in mutations:
        unit = units[name]
        assert old in unit, (name, old)
        try:
            CHECKS[name](unit.replace(old, new, 1))
        except (AssertionError, KeyError, TypeError):
            continue
        raise AssertionError(("semantic mutation was accepted", name, old, new))
    return len(mutations)


def check_render(units: dict[str, str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
    for name, unit in units.items():
        svg, _ = tenkz_pic.render_unit(unit, output)
        assert svg is not None and svg.is_file(), "production SVG rendering unavailable"
        assert "<path" in svg.read_text(), "SVG ink is required"
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, "complete event stream required"
        source = output / f"area-law-{name}.tex"
        source.write_text(unit + "\n")
        audit = Audit(log, source)
        audit.run()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        assert not hard, [(f.rule, f.msg) for f in hard]
        print(f"PASS: {name} picture, audited SVG {svg}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    units = check_source()
    count = check_rejected_mutations(units)
    print(f"PASS: layer ring, pitch fragments, fan rays, active rays; {count} rejected mutations")
    if args.source_only:
        print("NOT RUN: SVG rendering and event-stream audit (--source-only)")
    elif args.output_dir:
        output = args.output_dir.resolve()
        output.mkdir(parents=True, exist_ok=True)
        check_render(units, output)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_area_law_geometry_") as tmp:
            check_render(units, Path(tmp).resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
