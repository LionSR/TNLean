#!/usr/bin/env python3
"""Check that the documentation build pins the same dependencies as TNLean.

`docbuild/` shares `../.lake/packages` with the root project, and its own
manifest decides which revision of each shared package is checked out when the
API docs are built. A root dependency bump that leaves `docbuild/lake-manifest.json`
behind makes the docs build check out old revisions, so every module importing
newer upstream files fails with `bad import` and the Pages site stops updating.
Regenerate with `lake update` inside `docbuild/` when this check fails.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def package_revs(manifest: Path) -> dict[str, str | None]:
    data = json.loads(manifest.read_text(encoding="utf-8"))
    return {p["name"]: p.get("rev") for p in data["packages"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args()

    root = package_revs(args.root / "lake-manifest.json")
    docs = package_revs(args.root / "docbuild" / "lake-manifest.json")

    problems = []
    for name, rev in sorted(root.items()):
        if name not in docs:
            problems.append(f"{name}: pinned at {rev} by TNLean, missing from docbuild")
        elif docs[name] != rev:
            problems.append(f"{name}: TNLean pins {rev}, docbuild pins {docs[name]}")

    if problems:
        print("docbuild/lake-manifest.json is out of date with lake-manifest.json:")
        for line in problems:
            print(f"  {line}")
        print("Regenerate it with `lake update` inside docbuild/.")
        return 1
    print(f"docbuild manifest agrees with TNLean on {len(root)} packages.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
