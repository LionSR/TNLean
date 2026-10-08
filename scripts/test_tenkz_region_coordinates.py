#!/usr/bin/env python3
"""Check the regional basis-relabelling diagram and its production render.

Use --source-only when TeX is unavailable; this checks incidence, mathematical
scope, declaration placement, and rejected source mutations without claiming a
render. The default also requires complete SVGs and audited event streams.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REGIONAL = ROOT / "blueprint/src/chapter/ch24_peps_g_isometric_regional_parents.tex"
MARGINAL = ROOT / "blueprint/src/chapter/ch24_peps_regularized_patch_stationarity.tex"
GENERIC_DECLS = {
    "dependentRegionFinEquiv", "dependentGlobalFinEquiv",
    "dependentGlobalFinIsometry", "dependentGlobalFinIsometry_apply",
    "reindex_dependentRegionOperatorLift", "dependentGlobalFinIsometry_lift",
    "reindex_reducedPure_eq_regionState",
}
EXPECTED_ATOMS = [
    {
        "regionbasis": ("1,1", "E_X"),
        "regionmatrix": ("1,3", "K"),
        "regioninverse": ("1,5", "E_X^*"),
        "complementbasis": ("2,1", "E_C"),
        "complementidentity": ("2,3", "I_C"),
        "complementinverse": ("2,5", "E_C^*"),
    },
    {"relabelledmatrix": ("1,1", "K'"), "relabelledidentity": ("2,1", "I'_C")},
]
EXPECTED_WIRES = [
    [
        ("open w", "regionbasis.180"),
        ("regionbasis.0", "regionmatrix.180"),
        ("regionmatrix.0", "regioninverse.180"),
        ("regioninverse.0", "open e"),
        ("open w", "complementbasis.180"),
        ("complementbasis.0", "complementidentity.180"),
        ("complementidentity.0", "complementinverse.180"),
        ("complementinverse.0", "open e"),
    ],
    [
        ("open w", "relabelledmatrix.180"),
        ("relabelledmatrix.0", "open e"),
        ("open w", "relabelledidentity.180"),
        ("relabelledidentity.0", "open e"),
    ],
]


def entry(source: str, title: str) -> str:
    return source.split(r"\begin{theorem}[" + title + "]", 1)[1].split(
        r"\end{proof}", 1
    )[0]


def check_source(generic: str, marginal: str) -> list[str]:
    tags = set(re.findall(r"TNLean\.PEPS\.(\w+)", generic))
    assert tags == GENERIC_DECLS, ("generic declaration ownership", tags)
    assert set(re.findall(r"TNLean\.PEPS\.(\w+)", marginal)) == {
        "reindex_normalizedRegularizedPatchMarginal"
    }, "the final-state entry must remain a thin consequence"
    assert r"\uses{def:peps_regional_operator_extension}" in generic
    assert "def:peps_patch" not in generic and "thm:peps_patch" not in generic
    assert "thm:peps_regional_basis_relabelling" in marginal
    assert r"\ketbra{\xi}{\xi}E_X^*" in generic
    assert r"\ketbra{E_V\xi}{E_V\xi}" in generic
    assert r"\ketbra{E_V\phi}{E_V\phi}" in marginal
    for phrase in (
        "No Hermiticity or normalization", "empty regions, empty alphabets, and empty site sets",
        "same vector", "same operator after a change of coordinate labels",
        r"E_V=E_X\otimes E_C", r"K'=E_XKE_X^*",
    ):
        assert phrase in generic, phrase
    assert "unit-norm hypotheses" in marginal and "same final vector" in marginal
    assert r"\begin{tenkzequation}" in generic
    assert not re.search(r"\\(?:begin\{tikzpicture\}|draw\b|fill\b|node\b)", generic)
    units = re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", generic, re.S)
    assert len(units) == 2, "one two-panel coordinate identity"
    for index, unit in enumerate(units):
        atoms = {}
        for options, label in re.findall(r"\\tn\[([^]]+)\]\{([^}]+)\}", unit, re.S):
            name = re.search(r"\bname=(\w+)", options)
            position = re.search(r"\bat=\(([^)]+)\)", options)
            assert name and position, options
            assert name[1] not in atoms, name[1]
            assert "ports={180:physical, 0:physical}" in options
            atoms[name[1]] = (position[1], label)
        assert atoms == EXPECTED_ATOMS[index], ("regional/complementary tensor labels", atoms)
        wires = re.findall(r"\\tnwire(?:\[[^]]*\])?\{([^}]+)\}\{([^}]+)\}", unit)
        assert wires == EXPECTED_WIRES[index], ("factor order or row incidence changed", wires)
        marks = re.findall(r"\\tnmark\[[^]]*\]\{on (\w+) 0\.5\}\{\$([^$]+)\$\}", unit)
        prefix = "relabelled" if index else ""
        assert dict(marks) == {
            prefix + "regionout": "i", prefix + "regionin": "j",
            prefix + "complementout": r"\alpha", prefix + "complementin": r"\beta",
        }, ("the same four open coordinates are required", marks)
    return units


def check_rejected_mutations(generic: str, marginal: str) -> None:
    for old, new in (
        ("{regionmatrix.180}", "{complementidentity.180}"),
        ("{E_C^*}", "{E_C}"),
        ("{I_C}", "{K}"),
        ("{K'}", "{K}"),
        ("{open e}", "{open w}"),
        (r"\ketbra{E_V\xi}{E_V\xi}", r"\ketbra{E_V\eta}{E_V\eta}"),
    ):
        assert old in generic, old
        try:
            check_source(generic.replace(old, new, 1), marginal)
        except AssertionError:
            continue
        raise AssertionError(("semantic mutation was accepted", old, new))


def check_coefficients() -> None:
    """Exact complex-arithmetic examples include zero-dimensional factors."""
    for regional_dim, complement_dim in ((3, 2), (2, 3), (1, 6), (6, 1), (0, 2), (2, 0), (0, 0), (1, 1)):
        # A non-Hermitian K and an unnormalized vector; all entries are Gaussian integers.
        p = lambda i: (i + 1) % regional_dim
        q = lambda a: (a + 1) % complement_dim
        k = lambda i, j: complex(2 * i - j + 1, i + 3 * j + 2)
        psi = lambda i, a: complex(i + 2 * a + 1, 3 * i - a)
        for i in range(regional_dim):
            for j in range(regional_dim):
                reduced = sum(psi(p(i), a) * psi(p(j), a).conjugate() for a in range(complement_dim))
                relabelled = sum(psi(p(i), q(a)) * psi(p(j), q(a)).conjugate() for a in range(complement_dim))
                assert reduced == relabelled, "partial trace must use the same vector"
                for a in range(complement_dim):
                    for b in range(complement_dim):
                        assert k(p(i), p(j)) * (q(a) == q(b)) == k(p(i), p(j)) * (a == b)


def check_render(units: list[str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
    for index, unit in enumerate(units):
        svg, cold_hit = tenkz_pic.render_unit(unit, output)
        assert svg is not None and svg.is_file(), "production SVG rendering unavailable"
        assert not cold_hit and "<path" in svg.read_text(), "new SVG ink is required"
        stamp = svg.stat().st_mtime_ns
        again, warm_hit = tenkz_pic.render_unit(unit, output)
        assert again == svg and warm_hit and svg.stat().st_mtime_ns == stamp
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, "complete event stream required"
        source = output / f"region-coordinates-{index}.tex"
        source.write_text(unit + "\n")
        audit = Audit(log, source)
        audit.run()
        assert not [f for f in audit.findings if f.severity == "HARD"], audit.findings
        events = list(audit.events())
        assert sum(e.kind == "atom" for e in events) == len(EXPECTED_ATOMS[index])
        assert sum(e.kind == "wire" for e in events) == len(EXPECTED_WIRES[index])
        signatures = [e.attrs["signature"] for e in events if e.kind == "kernel-boundary"]
        assert len(signatures) == 1
        assert Counter(signatures[0].split(", ")) == Counter(["phys:w", "phys:e"] * 2), signatures
        print(f"PASS: panel {index + 1}, four open physical indices, audited SVG {svg}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    generic = entry(REGIONAL.read_text(), "Local basis relabelling")
    marginal = entry(MARGINAL.read_text(), "Relabelling the final-state marginal")
    units = check_source(generic, marginal)
    check_rejected_mutations(generic, marginal)
    check_coefficients()
    print("PASS: declaration placement, same-vector marginal, diagram incidence, six rejected mutations, coefficient checks")
    if args.source_only:
        print("NOT RUN: SVG rendering and event-stream audit (--source-only)")
    elif args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        check_render(units, args.output_dir)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_region_coordinates_") as tmp:
            check_render(units, Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
