#!/usr/bin/env python3
"""Render and compare the approved tensor-network topology references."""

from __future__ import annotations

import argparse
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

from PIL import Image, ImageChops, ImageDraw, ImageOps, ImageStat


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "blueprint/src"
RENDERER = SRC / "Packages/tn_diagrams.py"
REFERENCES = ROOT / "docs/tn_reference"
COMPARISON_SHEET = ROOT / "output/tn_reference_before_after.png"

REFERENCE_CALLS = {
    "straight_purification": (
        r"\begin{TNDiagram}[compact]"
        r"\TNPurificationSite{p}{(0,0)}{A}{\overline A}"
        r"\TNOpenPhysicalNorth{pKet}\TNOpenPhysicalSouth{pBra}"
        r"\end{TNDiagram}"
    ),
    "horizontal_periodic_mpo_word": r"\TNMPOChain{A}{i_1}{j_1}{i_N}{j_N}{N}",
    "stacked_mpo_zipper": r"\TNMPDOUnweightedZipperReconstruction",
    "compact_trace_cell": (
        r"\begin{TNDiagram}[compact]"
        r"\TNCompactTraceCell{c}{(0,0)}{M_\alpha}{X}{M_\alpha(X)}"
        r"\end{TNDiagram}"
    ),
    "rotated_vertical_word": (
        r"\begin{TNDiagram}[compact]"
        r"\TNVerticalWord{w}{(0,0)}{M_\alpha}{closed}"
        r"\end{TNDiagram}"
    ),
    "dense_fusion_tree": (
        r"\begin{TNEquationRow}[normal]"
        r"\TNTerm[normal]{"
        r"\TNMPDOLeftCofusionTree{ffLeft}{at=origin}"
        r"{U_{\alpha,\beta}^{\delta}}"
        r"{U_{\delta,\gamma}^{\varepsilon}}"
        r"{\alpha}{\beta}{\gamma}{\varepsilon}"
        r"{((\alpha\beta)\gamma)}}"
        r"\TNRelation{\xleftrightarrow{F_{\varepsilon}^{\alpha\beta\gamma}}}"
        r"\TNTerm[normal]{"
        r"\TNMPDORightCofusionTree{ffRight}{at=origin}"
        r"{U_{\beta,\gamma}^{\eta}}"
        r"{U_{\alpha,\eta}^{\varepsilon}}"
        r"{\alpha}{\beta}{\gamma}{\varepsilon}"
        r"{(\alpha(\beta\gamma))}}"
        r"\end{TNEquationRow}"
    ),
    "parallel_sector_buses": (
        r"\begin{TNDiagram}[normal]"
        r"\TNSectorBus{a}{(-1.5,0)}{(1.5,0)}{\alpha}"
        r"\TNParallelSectorBus{b}{a}{0.5}{\beta}"
        r"\end{TNDiagram}"
    ),
    "peps_three_site": r"\TNPEPSEdgeBlockingReduction",
}

EXPECTED_CONNECTIONS = {
    "straight_purification": {
        ("physical", "straight", "pKetAncilla", "pBraAncilla"),
    },
    "horizontal_periodic_mpo_word": {
        ("virtual", "trace-below", "tnLW", "tnRE"),
    },
}


def load_renderer():
    sys.path.insert(0, str(RENDERER.parent))
    spec = importlib.util.spec_from_file_location("tn_reference_renderer", RENDERER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {RENDERER}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def rasterize(svg: Path, png: Path) -> None:
    subprocess.run(
        [
            "rsvg-convert",
            "--background-color=white",
            "--zoom=2",
            "-o",
            str(png),
            str(svg),
        ],
        check=True,
    )


def assert_margin(image: Image.Image, name: str) -> None:
    rgba = image.convert("RGBA")
    background = Image.new("RGBA", rgba.size, "white")
    difference = ImageChops.difference(rgba, background).convert("L")
    bounding_box = difference.getbbox()
    if bounding_box is None:
        raise RuntimeError(f"{name}: raster contains no visible ink")
    left, top, right, bottom = bounding_box
    width, height = difference.size
    # dvisvgm adds 3 pt and rsvg-convert rasterizes at zoom 2.  At the SVG
    # reference density this is eight pixels; allow one pixel for antialiasing.
    clear_margin = min(left, top, width - right, height - bottom)
    if clear_margin < 7:
        raise RuntimeError(
            f"{name}: clear raster margin is {clear_margin}px, below 3pt"
        )


def connection_events(event_log: Path) -> set[tuple[str, str, str, str]]:
    """Read typed connection events emitted by the tensor-network calculus."""

    events = set()
    for line in event_log.read_text(encoding="utf-8").splitlines():
        parts = line.split("|")
        if not parts or parts[0] != "connection":
            continue
        fields = dict(part.split("=", 1) for part in parts[1:] if "=" in part)
        events.add(
            (fields["type"], fields["route"], fields["from"], fields["to"])
        )
    return events


def assert_connections(renderer, stem: str, name: str) -> None:
    """Require the approved reference to retain its canonical typed connection."""

    expected = EXPECTED_CONNECTIONS.get(name)
    if expected is None:
        return
    event_log = renderer._CACHE_DIR / f"{stem}.tnlog"
    actual = connection_events(event_log)
    missing = expected - actual
    if missing:
        raise RuntimeError(f"{name}: missing canonical connections {sorted(missing)}")


def difference_score(actual: Image.Image, expected: Image.Image) -> float:
    if actual.size != expected.size:
        return 1.0
    difference = ImageChops.difference(
        actual.convert("RGB"), expected.convert("RGB")
    )
    return sum(ImageStat.Stat(difference).mean) / (3 * 255)


def write_comparison_sheet(
    comparisons: list[tuple[str, Image.Image, Image.Image, float]],
) -> None:
    """Write one publication-review sheet, one row per compared reference."""

    width, row_height = 1600, 430
    sheet = Image.new("RGB", (width, row_height * len(comparisons)), "white")
    draw = ImageDraw.Draw(sheet)
    for index, (name, before, after, score) in enumerate(comparisons):
        top = index * row_height
        draw.text((24, top + 18), name, fill="black")
        draw.text((770, top + 18), f"difference={score:.4f}", fill="black")
        draw.text((24, top + 46), "before", fill="black")
        draw.text((824, top + 46), "after", fill="black")
        for left, image in ((24, before), (824, after)):
            panel = ImageOps.contain(image.convert("RGB"), (740, row_height - 88))
            x = left + (740 - panel.width) // 2
            y = top + 74 + (row_height - 88 - panel.height) // 2
            sheet.paste(panel, (x, y))
        draw.line((0, top + row_height - 1, width, top + row_height - 1), fill="#cccccc")
    COMPARISON_SHEET.parent.mkdir(parents=True, exist_ok=True)
    sheet.save(COMPARISON_SHEET)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--update",
        action="store_true",
        help="replace approved references after explicit visual approval",
    )
    parser.add_argument(
        "--all-registered",
        action="store_true",
        help="render every registered diagram and reject boundary contact",
    )
    parser.add_argument(
        "--margins-only",
        action="store_true",
        help="check crop margins without comparing approved reference pixels",
    )
    parser.add_argument(
        "--comparison-sheet",
        action="store_true",
        help="write a before-and-after sheet for visual approval",
    )
    args = parser.parse_args()
    renderer = load_renderer()
    REFERENCES.mkdir(parents=True, exist_ok=True)
    comparisons: list[tuple[str, Image.Image, Image.Image, float]] = []
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="tn-reference-") as directory:
        temporary = Path(directory)
        for name, call in REFERENCE_CALLS.items():
            svg = temporary / f"{name}.svg"
            stem = f"tn-reference-{name}"
            if renderer._compile_svg(call, stem, svg) is None:
                raise RuntimeError("LaTeX and dvisvgm are required")
            assert_connections(renderer, stem, name)
            actual_path = temporary / f"{name}.png"
            rasterize(svg, actual_path)
            actual = Image.open(actual_path)
            assert_margin(actual, name)
            expected_path = REFERENCES / f"{name}.png"
            if args.update:
                actual.save(expected_path)
                continue
            if args.margins_only:
                continue
            if not expected_path.exists():
                raise RuntimeError(f"Missing approved reference {expected_path}")
            expected = Image.open(expected_path)
            score = difference_score(actual, expected)
            comparisons.append((name, expected.copy(), actual.copy(), score))
            if score > 0.012:
                failures.append(f"{name}: {score:.4f}")
                continue
            print(f"{name}: {score:.4f}")
        if args.all_registered:
            rendered = renderer._smoke_render(
                declaration.name
                for declaration in renderer.diagram_declarations()
            )
            for svg in rendered:
                name = svg.stem.removeprefix("tn-smoke-")
                png = temporary / f"registered-{name}.png"
                rasterize(svg, png)
                assert_margin(Image.open(png), name)
            print(f"registered boundary checks: {len(rendered)}")
    if args.comparison_sheet:
        write_comparison_sheet(comparisons)
        print(COMPARISON_SHEET)
    if failures:
        raise RuntimeError(
            "Raster differences exceed 0.012 pending visual approval: "
            + ", ".join(failures)
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
