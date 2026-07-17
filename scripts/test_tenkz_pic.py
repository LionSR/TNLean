#!/usr/bin/env python3
r"""Standalone test harness for the tenkz plasTeX SVG pipeline.

Exercises the compile+cache core of ``blueprint/src/Packages/tenkz_pic.py``
**without plasTeX**: the module defers its plasTeX imports, so importing it
here only loads the pure compile machinery.  Verbatim units from the
spec's benchmark corpus (a ``tenkz`` grid, a ``tenkzlattice`` window, a
``tenkzplanes`` double layer, and a ``\tnpic`` sandwich atom) are rendered
standalone; the harness asserts that

  1. each SVG materializes with real drawing ink and a plausible extent
     (a silently ink-stripped render collapses to the text glyphs' bbox —
     the failure mode the module's route canary exists to catch);
  2. re-rendering every unit is a pure cache hit (file untouched);
  3. editing one body invalidates exactly that unit's SVG (new content
     hash), leaving the other cached SVGs in place.

Run:  python3 scripts/test_tenkz_pic.py
"""

from __future__ import annotations

import re
import shutil
import sys
import tempfile
import time
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_REPO_ROOT / "blueprint/src/Packages"))

import tenkz_pic

# Spec benchmark bodies (B1, B6, B8 of tenkz_final_spec.md §3), with the
# minimum width (pt) a faithful render must exceed: an ink-stripped SVG of
# B1 measures ~12pt (three letters), a real one ~95pt at 11mm pitch.
UNITS: dict[str, tuple[str, float]] = {
    "B1 tenkz grid": (
        r"""\begin{tenkz}[periodic, physical=up, bond label={$D$ at 1-2}]
  \tn[up=$i_1$]{A} & \tn[up=$i_2$]{A} & \tn[up=$i_3$]{A}
\end{tenkz}""",
        60.0,
    ),
    "B6 tenkzlattice": (
        r"""\begin{tenkzlattice}[rows=4, cols=4, boundary legs]
  \tnregion[slot=selected, name=R, label=$R$]{(1-3, 1-3)}
  \tnregion[slot=secondary, outline, label=$S$, label at=south west]{R - (2,2)}
  \tnedge[distinguished]{(2,3)-(2,4)}
  \tnsite[removed]{(2,2)}
\end{tenkzlattice}""",
        70.0,
    ),
    "planes double layer": (
        r"""\begin{tenkzplanes}[rows=2, cols=3, open={(1,2)}]
\end{tenkzplanes}""",
        40.0,
    ),
    "B8 tnpic sandwich": (
        r"\tnpic[sandwich, inline]{\tn{A} \\ \tn*{A}}",
        12.0,
    ),
}

_WIDTH_PATTERN = re.compile(r"""<svg[^>]*\swidth=["']([0-9.]+)pt["']""")


def _svg_width_pt(svg_text: str) -> float:
    match = _WIDTH_PATTERN.search(svg_text)
    assert match, "SVG root carries no pt width"
    return float(match.group(1))


def main() -> int:
    chain = tenkz_pic.toolchain()
    if chain is None:
        print("FAIL: no SVG toolchain (need xelatex plus dvisvgm or pdftocairo)")
        return 1
    print(f"toolchain: route={chain.route} engine={chain.xelatex} "
          f"converter={chain.converter}")

    svg_dir = Path(tempfile.mkdtemp(prefix="tenkz_svg_test_"))
    rendered: dict[str, Path] = {}
    try:
        # 1. Cold renders: SVGs materialize with ink and plausible extent.
        for name, (unit, min_width) in UNITS.items():
            start = time.monotonic()
            svg_path, hit = tenkz_pic.render_unit(unit, svg_dir)
            elapsed = time.monotonic() - start
            assert svg_path is not None, f"{name}: toolchain vanished mid-run"
            assert not hit, f"{name}: cold render reported a cache hit"
            assert svg_path.is_file() and svg_path.stat().st_size > 0, (
                f"{name}: SVG did not materialize"
            )
            text = svg_path.read_text(encoding="utf-8", errors="replace")
            assert "<svg" in text, f"{name}: not an SVG"
            assert "<path" in text, f"{name}: SVG carries no drawing ink"
            width = _svg_width_pt(text)
            assert width > min_width, (
                f"{name}: width {width}pt <= {min_width}pt — ink was stripped?"
            )
            rendered[name] = svg_path
            print(f"PASS cold  {name}: {svg_path.name} "
                  f"({width:.1f}pt wide, {elapsed:.1f}s)")

        # 2. Warm renders: byte-identical cache hits, files untouched.
        before = {name: path.stat().st_mtime_ns for name, path in rendered.items()}
        for name, (unit, _) in UNITS.items():
            start = time.monotonic()
            svg_path, hit = tenkz_pic.render_unit(unit, svg_dir)
            elapsed = time.monotonic() - start
            assert hit, f"{name}: warm render missed the cache"
            assert svg_path == rendered[name], f"{name}: cache path changed"
            assert svg_path.stat().st_mtime_ns == before[name], (
                f"{name}: cache hit rewrote the SVG"
            )
            print(f"PASS warm  {name}: cache hit ({elapsed*1000:.0f}ms)")

        # 3. Per-figure invalidation: one edited body, one new SVG.
        grid_unit, _ = UNITS["B1 tenkz grid"]
        edited = grid_unit.replace("$i_2$", "$j_2$")
        assert tenkz_pic.unit_hash(edited) != tenkz_pic.unit_hash(grid_unit)
        edited_path, hit = tenkz_pic.render_unit(edited, svg_dir)
        assert edited_path is not None and not hit
        assert edited_path.name != rendered["B1 tenkz grid"].name, (
            "edited body reused the old content hash"
        )
        survivors = {path.name for path in svg_dir.glob("tenkz-*.svg")}
        expected = {path.name for path in rendered.values()} | {edited_path.name}
        assert survivors == expected, (
            f"cache set drifted: {survivors ^ expected}"
        )
        print(f"PASS edit  one body edit invalidated exactly one SVG "
              f"({edited_path.name})")
    except AssertionError as failure:
        print(f"FAIL: {failure}")
        print(f"artifacts kept for inspection in {svg_dir}")
        return 1
    except RuntimeError as failure:
        # A unit failed to compile or convert — typically a tex/tenkz
        # library defect, not a pipeline one; the message names the
        # compile log kept in blueprint/src/.tenkz_svg_cache/.
        print(f"FAIL (library or toolchain): {failure}")
        return 1
    shutil.rmtree(svg_dir, ignore_errors=True)
    print("all tenkz pipeline checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
