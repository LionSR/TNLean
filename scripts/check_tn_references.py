#!/usr/bin/env python3
"""Render and compare the approved tensor-network topology references."""

from __future__ import annotations

import argparse
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

from PIL import Image, ImageChops, ImageStat


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "blueprint/src"
RENDERER = SRC / "Packages/tn_diagrams.py"
REFERENCES = ROOT / "docs/tn_reference"

REFERENCE_CALLS = {
    "straight_purification": (
        r"\begin{TNDiagram}[compact]"
        r"\TNPurificationSite{p}{(0,0)}{A}{\overline A}"
        r"\TNOpenPhysicalNorth{pKet}\TNOpenPhysicalSouth{pBra}"
        r"\end{TNDiagram}"
    ),
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
    "dense_fusion_tree": r"\TNMPDOFixedFinalFusionBracketings",
    "parallel_sector_buses": (
        r"\begin{TNDiagram}[normal]"
        r"\TNSectorBus{a}{(-1.5,0)}{(1.5,0)}{\alpha}"
        r"\TNParallelSectorBus{b}{a}{0.5}{\beta}"
        r"\end{TNDiagram}"
    ),
    "peps_three_site": r"\TNPEPSEdgeBlockingReduction",
}


def load_renderer():
    sys.path.insert(0, str(RENDERER.parent))
    spec = importlib.util.spec_from_file_location("tn_reference_renderer", RENDERER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {RENDERER}")
    module = importlib.util.module_from_spec(spec)
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
    width, height = difference.size
    boundary = Image.new("L", difference.size)
    boundary.paste(difference.crop((0, 0, width, 1)), (0, 0))
    boundary.paste(difference.crop((0, height - 1, width, height)), (0, height - 1))
    boundary.paste(difference.crop((0, 0, 1, height)), (0, 0))
    boundary.paste(difference.crop((width - 1, 0, width, height)), (width - 1, 0))
    if boundary.getbbox() is not None:
        raise RuntimeError(f"{name}: ink touches the raster boundary")


def difference_score(actual: Image.Image, expected: Image.Image) -> float:
    if actual.size != expected.size:
        return 1.0
    difference = ImageChops.difference(
        actual.convert("RGB"), expected.convert("RGB")
    )
    return sum(ImageStat.Stat(difference).mean) / (3 * 255)


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
    args = parser.parse_args()
    renderer = load_renderer()
    REFERENCES.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="tn-reference-") as directory:
        temporary = Path(directory)
        for name, call in REFERENCE_CALLS.items():
            svg = temporary / f"{name}.svg"
            if renderer._compile_svg(call, f"tn-reference-{name}", svg) is None:
                raise RuntimeError("LaTeX and dvisvgm are required")
            actual_path = temporary / f"{name}.png"
            rasterize(svg, actual_path)
            actual = Image.open(actual_path)
            assert_margin(actual, name)
            expected_path = REFERENCES / f"{name}.png"
            if args.update:
                actual.save(expected_path)
                continue
            if not expected_path.exists():
                raise RuntimeError(f"Missing approved reference {expected_path}")
            score = difference_score(actual, Image.open(expected_path))
            if score > 0.012:
                raise RuntimeError(f"{name}: raster difference {score:.4f} exceeds 0.012")
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
