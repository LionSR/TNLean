#!/usr/bin/env python3
"""Audit the new SCP10 three-block intersection declarations and blueprint owners.

This focused check never edits shared routers or declaration indexes. Optional
Lean checking requires the caller's already warmed, source-audited LEAN_PATH;
no dependency downloads or package builds are attempted.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from blueprint_lean_sync import (
    _strip_tex_comments,
    collect_blueprint_entries,
    collect_blueprint_lean_refs,
    collect_file_lean_decls,
)

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "TNLean.PEPS.DependentPartialAverageSupport",
    "TNLean.PEPS.DependentOpenBondSupport",
    "TNLean.PEPS.DependentOpenCutIntersection",
    "TNLean.PEPS.DependentLiftedCut",
    "TNLean.PEPS.DependentLiftedCutReconstruction",
    "TNLean.PEPS.DependentLiftedCutIntersection",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockDependentCutIntersection",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockPhysicalExtension",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryLocalization",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryContraction",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockOpenBoundaryRegional",
    "TNLean.PEPS.ParentHamiltonian.ThreeBlockGInjectiveIntersection",
]
FRAGMENTS = {
    "ch24_peps_dependent_open_intersection.tex",
    "ch24_peps_general_three_block_intersection.tex",
}
INVENTORY = ROOT / "docs/audits/2026-10-05_scp10_three_block_blueprint_inventory.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-inventory", action="store_true")
    parser.add_argument("--lean-check", action="store_true")
    args = parser.parse_args()
    declarations = [
        d for mod in MODULES
        for d in collect_file_lean_decls(
            ROOT / Path(*mod.split(".")).with_suffix(".lean"), ROOT / "TNLean"
        ) if not d.is_private
    ]
    assert len(declarations) == 161, len(declarations)
    src = ROOT / "blueprint/src"
    entries = collect_blueprint_entries(src)
    refs = collect_blueprint_lean_refs(src)
    counts = Counter(r.lean_decl for r in refs)
    owners = {d.fqn: [e for e in entries if e.lean_decl == d.fqn] for d in declarations}
    rows = []
    for d in declarations:
        assert counts[d.fqn] == 1, (d.fqn, "owner count", counts[d.fqn])
        assert len(owners[d.fqn]) == 1, (d.fqn, "theorem-like owner missing")
        e = owners[d.fqn][0]
        text = "\n".join((ROOT / "blueprint" / e.file).read_text().splitlines()[e.line - 1:])
        text = text.split("\\end{" + e.env_type + "}", 1)[0]
        label = re.search(r"\\label\{([^}]+)\}", text)
        assert label and e.has_leanok, (d.fqn, "unlabelled or unchecked owner")
        if e.env_type in {"theorem", "lemma", "corollary"}:
            assert e.proof_has_leanok, (d.fqn, "missing checked proof")
        assert Path(e.file).name in FRAGMENTS, (d.fqn, "unexpected owner", e.file)
        rows.append({
            "declaration": d.fqn, "kind": d.kind, "source": d.file, "line": d.line,
            "owner": label.group(1), "blueprint": "blueprint/" + e.file,
        })
    label_counts = Counter(
        label for p in src.rglob("*.tex")
        for label in re.findall(r"\\label\{([^}]+)\}", _strip_tex_comments(p.read_text()))
    )
    for name in FRAGMENTS:
        text = _strip_tex_comments((src / "chapter" / name).read_text())
        for label in re.findall(r"\\label\{([^}]+)\}", text):
            assert label_counts[label] == 1, (name, "duplicate label", label)
        for body in re.findall(r"\\(?:uses|ref)\{([^}]+)\}", text):
            for label in body.split(","):
                assert label_counts[label.strip()] == 1, (name, "unresolved reference", label)
    if args.lean_check:
        with tempfile.TemporaryDirectory(prefix="three-block-declarations-") as temporary:
            check = Path(temporary) / "Check.lean"
            check.write_text("\n".join("import " + mod for mod in MODULES) + "\n" +
                             "\n".join("#check " + d.fqn for d in declarations) + "\n")
            subprocess.run(["lean", str(check)], cwd=ROOT, check=True, capture_output=True)
    result = {
        "source_theorem": "SCP10 Theorem 5.4",
        "modules": MODULES,
        "sources": [
            {"module": mod, "sha256": hashlib.sha256(
                (ROOT / Path(*mod.split(".")).with_suffix(".lean")).read_bytes()
            ).hexdigest()} for mod in MODULES
        ],
        "declarations": rows,
    }
    if args.write_inventory:
        INVENTORY.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Verified {len(declarations)} unique declaration owners across {len(MODULES)} modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
