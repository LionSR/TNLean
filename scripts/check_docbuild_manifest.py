#!/usr/bin/env python3
"""Check that the documentation build pins the same dependencies as TNLean.

`docbuild/` shares `../.lake/packages` with the root project, and its own
manifest decides which revision of each shared package is checked out when the
API docs are built. A root dependency bump that leaves `docbuild/lake-manifest.json`
behind makes the docs build check out old revisions, so every module importing
newer upstream files fails with `bad import` and the Pages site stops updating.
It also checks that every requirement of `docbuild/lakefile.toml` pinned by
`rev` (such as doc-gen4) is recorded in the docbuild manifest with that input
revision. Regenerate with `lake update` inside `docbuild/` when this check fails.
"""

from __future__ import annotations

import argparse
import json
import sys
import tomllib
from pathlib import Path


def manifest_packages(manifest: Path) -> dict[str, dict]:
    data = json.loads(manifest.read_text(encoding="utf-8"))
    # Lake writes non-identifier names with guillemets, e.g. `«doc-gen4»`.
    return {p["name"].strip("«»"): p for p in data["packages"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args()

    root = manifest_packages(args.root / "lake-manifest.json")
    docs = manifest_packages(args.root / "docbuild" / "lake-manifest.json")
    lakefile = tomllib.loads((args.root / "docbuild" / "lakefile.toml").read_text(encoding="utf-8"))

    problems = []
    for name, pkg in sorted(root.items()):
        rev = pkg.get("rev")
        if name not in docs:
            problems.append(f"{name}: pinned at {rev} by TNLean, missing from docbuild")
        elif docs[name].get("rev") != rev:
            problems.append(f"{name}: TNLean pins {rev}, docbuild pins {docs[name].get('rev')}")
    for req in lakefile.get("require", []):
        name, want = req["name"], req.get("rev")
        if want is None:
            continue
        if name not in docs:
            problems.append(f"{name}: required at {want} by docbuild/lakefile.toml, missing from its manifest")
        elif docs[name].get("inputRev") != want:
            problems.append(
                f"{name}: docbuild/lakefile.toml requires {want}, "
                f"its manifest records {docs[name].get('inputRev')}"
            )

    if problems:
        print("docbuild/lake-manifest.json is out of date:")
        for line in problems:
            print(f"  {line}")
        print("Regenerate it with `lake update` inside docbuild/.")
        return 1
    print(f"docbuild manifest agrees with TNLean on {len(root)} packages and with its lakefile.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
