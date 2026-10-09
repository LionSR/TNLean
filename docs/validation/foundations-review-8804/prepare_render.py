#!/usr/bin/env python3
"""Prepare a focused renderer from immutable Git inputs, without Lean/Lake."""

import argparse
import hashlib
import importlib.metadata
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile


LEAVES = (
    "ch34_area_law_graph_foundations.tex",
    "ch34_area_law_diamond_counting.tex",
)
MODULES = (
    "GraphInteractionBudget", "GraphInteractionChain",
    "GraphInteractionDiamondCounting", "GraphInteractionSeries",
    "GraphInteractionTarget", "GraphLatticeDiamond", "GraphLatticeDistance",
)
SCRIPTS = (
    "blueprint_lean_sync.py", "test_blueprint_web_render.py",
    "test_tenkz_equation_web.py", "tenkz_paths.py",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root, out = args.root.resolve(), args.out.resolve()
    if out == root or root in out.parents or out.exists():
        parser.error("--out must be a new directory outside the source checkout")
    revision = subprocess.check_output(
        ["git", "rev-parse", f"{args.revision}^{{commit}}"], cwd=root, text=True,
    ).strip()
    selected = ["blueprint/src", "texra-blueprint.toml", "tenkz.toml"]
    selected += [f"scripts/{name}" for name in SCRIPTS]
    selected += [f"TNLean/PEPS/AreaLaw/{name}.lean" for name in MODULES]
    archive = subprocess.check_output(["git", "archive", revision, *selected], cwd=root)
    snapshot = out / "source"
    manifest = {}
    # Copy only selected, regular text inputs. No checkout files or build caches
    # are read; the snapshot also preserves all TeX for global ownership checks.
    with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
        for entry in stream:
            if not entry.isfile() or entry.name.endswith(".pdf"):
                continue
            path = Path(entry.name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError(f"unsafe archive path: {path}")
            data = stream.extractfile(entry).read()
            target = snapshot / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            manifest[entry.name] = hashlib.sha256(data).hexdigest()
    src = out / "blueprint/src"
    src.mkdir(parents=True)
    for path in (snapshot / "blueprint/src").iterdir():
        if path.name in ("chapter", "appendix"):
            continue
        if path.is_dir():
            shutil.copytree(path, src / path.name)
        else:
            shutil.copy2(path, src / path.name)
    (src / "chapter").mkdir()
    for name in LEAVES:
        shutil.copy2(snapshot / "blueprint/src/chapter" / name, src / "chapter" / name)
    (src / "content.tex").write_text(
        "\\input{chapter/ch34_area_law_graph_foundations}\n"
    )
    config = (snapshot / "texra-blueprint.toml").read_text()
    subset = ('[blueprint.graphs.subsets]\n'
              'ft_equal_gauge = { ancestors_of = "thm:sector_bnt_equal_global_gauge", '
              'title = "Fundamental-theorem gauge cone" }\n')
    if config.count(subset) != 1:
        raise ValueError("focused graph-subset fixture no longer matches source")
    (out / "texra-blueprint.toml").write_text(config.replace(subset, ""))
    shutil.copy2(snapshot / "tenkz.toml", out / "tenkz.toml")
    (out / "scripts").mkdir()
    shutil.copy2(snapshot / "scripts/tenkz_paths.py", out / "scripts/tenkz_paths.py")
    record = {
        "source_revision": revision,
        "source_tree": subprocess.check_output(
            ["git", "rev-parse", f"{revision}^{{tree}}"], cwd=root, text=True,
        ).strip(),
        "target_leaves": {
            name: manifest[f"blueprint/src/chapter/{name}"] for name in LEAVES
        },
        "production_modules": [f"TNLean/PEPS/AreaLaw/{name}.lean" for name in MODULES],
        "snapshot_inputs": manifest,
        "fixture_only_changes": [
            "Replace content.tex by a router including only the two target leaves.",
            "Remove the unrelated Fundamental-Theorem graph subset from fixture configuration.",
        ],
        "tools": {
            name: importlib.metadata.version(name)
            for name in ("texra-blueprint", "plasTeX", "leanblueprint")
        },
    }
    (out / "focus-manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: record[key] for key in (
        "source_revision", "target_leaves", "tools",
    )}, indent=2))


if __name__ == "__main__":
    main()
