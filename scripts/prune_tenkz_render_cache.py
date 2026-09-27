#!/usr/bin/env python3
"""Remove tenkz pictures that no generated blueprint page references.

The web build names every picture by the content hash of its source
(``blueprint/src/Packages/tenkz_pic.py``), and CI carries the pictures from
one build to the next so that an unchanged figure is not compiled again.  A
figure that was edited or deleted leaves its old picture behind.  This script
keeps exactly the pictures the current pages reference, both the SVG under
the web output and the per-picture compile products beside the sources, so
the published site and the carried cache hold no figures that were edited
away.

Usage:
  prune_tenkz_render_cache.py [--web-root DIR] [--compile-cache DIR]
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PICTURE = re.compile(r"tenkz-[0-9a-f]{16}")


def referenced_pictures(web_root: Path) -> set[str]:
    names: set[str] = set()
    for page in web_root.rglob("*.html"):
        names.update(PICTURE.findall(page.read_text(encoding="utf-8", errors="replace")))
    return names


def prune(directory: Path, keep: set[str]) -> int:
    """Delete every hash-named file in ``directory`` whose picture is unused."""
    removed = 0
    if not directory.is_dir():
        return removed
    for path in directory.iterdir():
        found = PICTURE.match(path.name)
        if path.is_file() and found and found.group(0) not in keep:
            path.unlink()
            removed += 1
    return removed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--web-root", type=Path, default=ROOT / "blueprint" / "web")
    parser.add_argument(
        "--compile-cache", type=Path,
        default=ROOT / "blueprint" / "src" / ".tenkz_svg_cache")
    args = parser.parse_args()

    keep = referenced_pictures(args.web_root)
    if not keep:
        raise SystemExit(f"no page under {args.web_root} references a tenkz picture")
    svgs = prune(args.web_root / "tenkz_svg", keep)
    products = prune(args.compile_cache, keep)
    print(f"kept {len(keep)} pictures; removed {svgs} SVGs and {products} compile products")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
