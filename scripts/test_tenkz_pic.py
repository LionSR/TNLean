#!/usr/bin/env python3
r"""Standalone test harness for the tenkz plasTeX SVG pipeline.

Exercises the compile+cache core of ``blueprint/src/Packages/tenkz_pic.py``
**without plasTeX**: the module defers its plasTeX imports, so importing it
here only loads the pure compile machinery.  Verbatim units spelled on the
kernel surface (a chain with labelled physical ports and a sandwich
picture) are rendered standalone; the harness asserts that

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

_PLACEHOLDER_WORKFLOWS = (
    _REPO_ROOT / ".github/workflows/blueprint.yml",
    _REPO_ROOT / ".github/workflows/docgen.yml",
)
_SLIDE_PREAMBLE = _REPO_ROOT / "docs/slides/preamble.tex"
_SLIDE_THEME = _REPO_ROOT / "docs/slides/tn_library_dark.tex"
_TENKZ_CORE = _REPO_ROOT / "tex/tenkz/tenkz-core.code.tex"

_COLORLET_PATTERN = re.compile(
    r"^\s*\\colorlet\{(tenkz[A-Za-z]+)\}\{([^}]*)\}\s*$", re.MULTILINE
)
_THEME_GEOMETRY_PATTERN = re.compile(
    r"(?:baseline|scale|xshift|yshift|shape|font|line width|"
    r"minimum (?:width|height|size)|inner sep|outer sep|rounded corners)\s*=",
    re.IGNORECASE,
)

# Kernel-surface benchmark bodies (the spec's B1 and B8 subjects respelled
# onto the load-time kernel surface), with the minimum width (pt) a
# faithful render must exceed: an ink-stripped SVG of the chain measures
# ~12pt (three letters), a real one ~95pt at the default pitch.
UNITS: dict[str, tuple[str, float]] = {
    "B1 tenkz chain": (
        r"""\begin{tenkz}[cols=3, boundary=periodic, physical=up]
  \tn[ports={90:physical:$i_1$}]{A} & \tn[ports={90:physical:$i_2$}]{A} &
  \tn[ports={90:physical:$i_3$}]{A}
\end{tenkz}""",
        60.0,
    ),
    "B8 sandwich": (
        r"""\begin{tenkz}[cols=1, sandwich]
  \tn[at=(1,1)]{A} \tn[at=(2,1)]{A}
\end{tenkz}""",
        12.0,
    ),
}

# Both converters serialize the root extent in points, but spell it
# differently: dvisvgm writes ``width="95.1pt"`` while pdftocairo's cairo
# SVG surface may drop the explicit ``pt`` unit (a bare user-unit number,
# which for a PDF-sourced surface is still points).  Accept either spelling,
# and fall back to the viewBox width (always in user units = points) so the
# smoke test tracks the rendered extent rather than one toolchain's unit
# string.
_WIDTH_PATTERN = re.compile(r"""<svg[^>]*\swidth=["']([0-9.]+)(?:pt)?["']""")
_VIEWBOX_PATTERN = re.compile(
    r"""<svg[^>]*?\sviewBox=["']\s*[-0-9.eE+]+\s+[-0-9.eE+]+\s+([0-9.]+)"""
)


def _svg_width_pt(svg_text: str) -> float:
    match = _WIDTH_PATTERN.search(svg_text) or _VIEWBOX_PATTERN.search(svg_text)
    assert match, "SVG root carries neither a pt width nor a viewBox width"
    return float(match.group(1))


def _without_tex_comments(source: str) -> str:
    return re.sub(r"(?<!\\)%.*$", "", source, flags=re.MULTILINE)


def _palette(source: str) -> dict[str, str]:
    entries = _COLORLET_PATTERN.findall(_without_tex_comments(source))
    palette = dict(entries)
    assert len(palette) == len(entries), "palette contains duplicate semantic keys"
    return palette


def _assert_dark_theme_contract(core_source: str, theme_source: str) -> None:
    core_palette = _palette(core_source)
    theme_palette = _palette(theme_source)
    assert core_palette, "native tenkz core declares no semantic palette"
    assert theme_palette.keys() == core_palette.keys(), (
        "slide theme semantic keys differ from the native tenkz core"
    )
    assert not _THEME_GEOMETRY_PATTERN.search(_without_tex_comments(theme_source)), (
        "slide theme must change colours only, not geometry or typography"
    )


def _assert_contract_rejects(core_source: str, theme_source: str, defect: str) -> None:
    try:
        _assert_dark_theme_contract(core_source, theme_source)
    except AssertionError:
        return
    raise AssertionError(f"slide theme contract accepted {defect}")


def main() -> int:
    missing_html = tenkz_pic._missing_tools_html(r"\tn{A}")
    sentinel = tenkz_pic.MISSING_SVG_SENTINEL
    assert sentinel in missing_html, "missing-tool HTML lost its stable sentinel"
    for workflow in _PLACEHOLDER_WORKFLOWS:
        workflow_text = workflow.read_text(encoding="utf-8")
        assert f'grep -R "{sentinel}"' in workflow_text, (
            f"{workflow}: placeholder guard drifted from the renderer sentinel"
        )
    print(f"PASS placeholder sentinel: {sentinel!r}")

    slide_preamble = _SLIDE_PREAMBLE.read_text(encoding="utf-8")
    package_loader = r"\usepackage{tenkz}"
    dark_palette = r"\input{tn_library_dark}"
    assert package_loader in slide_preamble, "slides lost the native tenkz package"
    assert dark_palette in slide_preamble, "slides lost the native dark palette"
    assert slide_preamble.index(package_loader) < slide_preamble.index(dark_palette), (
        "slide dark palette must load after the native tenkz package"
    )
    core_source = _TENKZ_CORE.read_text(encoding="utf-8")
    theme_source = _SLIDE_THEME.read_text(encoding="utf-8")
    _assert_dark_theme_contract(core_source, theme_source)
    _assert_contract_rejects(
        core_source,
        theme_source.replace("\\colorlet{tenkzOperator}{softred}\n", ""),
        "a missing semantic colour",
    )
    custom_theme = theme_source.replace("orange!80!white", "black")
    assert custom_theme != theme_source, "custom-hue fixture did not change the theme"
    _assert_dark_theme_contract(core_source, custom_theme)
    _assert_contract_rejects(
        core_source,
        theme_source + "\\tikzset{every node/.style={minimum size=9mm}}\n",
        "a geometry assignment",
    )
    print("PASS slide palette: native dark theme preserves colours-only contract")

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
        grid_unit, _ = UNITS["B1 tenkz chain"]
        edited = grid_unit.replace("$i_2$", "$j_2$")
        assert tenkz_pic.unit_hash(edited) != tenkz_pic.unit_hash(grid_unit)
        edited_path, hit = tenkz_pic.render_unit(edited, svg_dir)
        assert edited_path is not None and not hit
        assert edited_path.name != rendered["B1 tenkz chain"].name, (
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
