#!/usr/bin/env python3
"""Audit declaration owners and references for the SCP10 four-cut packet.

This focused check deliberately does not edit the shared blueprint routers or
lean_decls file. With --lean-check, the caller must provide the already warmed
LEAN_PATH and pinned Lean executable; no package build or download is attempted.
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
FRAGMENTS = [
    "ch24_peps_four_cut_labelled_geometry.tex",
    "ch24_peps_dependent_networks.tex",
    "ch24_peps_dependent_projectors.tex",
    "ch24_peps_dependent_bond_support.tex",
    "ch24_peps_full_four_cut_closure.tex",
    "ch24_peps_four_cut_diagrams.tex",
    "ch24_peps_four_cut_common_boundaries.tex",
    "ch24_peps_four_cut_common_projectors.tex",
    "ch24_peps_four_cut_common_reconstruction.tex",
]
INVENTORY = ROOT / "docs/audits/2026-10-05_scp10_four_cut_blueprint_inventory.json"
PRIMARY_LABELS = (
    "thm:2d:closure", "eq:2d:closure-intersection", "eq:2d:closure-inv",
    "eq:2d:close-in-in", "eq:2d-ug-sym", "eq:2d-linv",
    "lemma:noninj:semireg-trace-ug-delta", "eq:2d:move-strings",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-inventory", action="store_true")
    parser.add_argument("--lean-check", action="store_true")
    args = parser.parse_args()
    # The original packet was assembled with local cherry-picks. Those commit
    # objects need not exist in a shallow clone or after squash publication.
    # The committed inventory is the portable source snapshot, not Git history.
    expected = json.loads(INVENTORY.read_text())
    paths = [item["path"] for item in expected["source_modules"]]
    assert len(paths) == len(set(paths)), "Repeated source path in inventory"
    for path in paths:
        resolved = (ROOT / path).resolve()
        assert resolved.is_relative_to((ROOT / "TNLean").resolve()), path
        assert resolved.suffix == ".lean" and resolved.is_file(), path
    source_modules = [{"path": path,
                       "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
                      for path in paths]
    unchanged_source = source_modules == expected["source_modules"]
    if not args.write_inventory:
        assert unchanged_source, "Changed source snapshot; inspect before --write-inventory"
    declarations = [
        d for p in paths
        for d in collect_file_lean_decls(ROOT / p, ROOT / "TNLean")
        if not d.is_private
    ]
    if not args.write_inventory:
        assert len(declarations) == len(expected["declarations"]), "Changed declaration count"
    paper = (ROOT / "Papers/1001.3807/paper_v3.tex").read_text()
    for label in PRIMARY_LABELS:
        assert len(re.findall(r"\\label\{\s*" + re.escape(label) + r"\s*\}", paper)) == 1, label
    src = ROOT / "blueprint/src"
    entries = collect_blueprint_entries(src)
    refs = collect_blueprint_lean_refs(src)
    owners = {d.fqn: [e for e in entries if e.lean_decl == d.fqn] for d in declarations}
    counts = Counter(r.lean_decl for r in refs)
    rows = []
    for d in declarations:
        assert counts[d.fqn] == 1, (d.fqn, "owner count", counts[d.fqn])
        assert len(owners[d.fqn]) == 1, (d.fqn, "theorem-like owner missing")
        e = owners[d.fqn][0]
        owner_text = "\n".join((ROOT / "blueprint" / e.file).read_text().splitlines()[e.line - 1:])
        owner_text = owner_text.split("\\end{" + e.env_type + "}", 1)[0]
        label = re.search(r"\\label\{([^}]+)\}", owner_text)
        assert label and e.has_leanok, (d.fqn, "unlabelled or unchecked owner")
        if e.env_type in {"theorem", "lemma", "corollary"}:
            assert e.proof_has_leanok, (d.fqn, "missing checked proof")
        assert Path(e.file).name in FRAGMENTS, (d.fqn, "unexpected owner", e.file)
        rows.append({"declaration": d.fqn, "kind": d.kind,
                     "source": d.file, "line": d.line,
                     "owner": label.group(1), "blueprint": "blueprint/" + e.file})
    all_tex = list(src.rglob("*.tex"))
    label_counts = Counter(
        label for p in all_tex
        for label in re.findall(r"\\label\{([^}]+)\}", _strip_tex_comments(p.read_text()))
    )
    packet_names = {d.fqn for d in declarations}
    packet_refs = [r for r in refs if Path(r.file).name in FRAGMENTS]
    assert {r.lean_decl for r in packet_refs} == packet_names, "Unexpected or absent packet tags"
    bibliography = (src / "references.bib").read_text()
    for fragment in FRAGMENTS:
        p = src / "chapter" / fragment
        clean = _strip_tex_comments(p.read_text())
        for label in re.findall(r"\\label\{([^}]+)\}", clean):
            assert label_counts[label] == 1, (fragment, "duplicate label", label)
        for match in re.finditer(r"\\(?:uses|ref|eqref|proves)\{([^}]+)\}", clean):
            for label in match.group(1).split(","):
                label = label.strip()
                assert label_counts[label] == 1, (fragment, "unresolved/duplicate reference", label)
        for citation in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", clean):
            for key in citation.split(","):
                assert re.search(r"@\w+\{\s*" + re.escape(key.strip()) + r"\s*,", bibliography), key
    inventory = {
        "source_commit": expected["source_commit"] if unchanged_source else "working-tree",
        "primary_source_labels": list(PRIMARY_LABELS),
        "base_commit": expected["base_commit"],
        "source_modules": source_modules,
        "fragment_order": ["blueprint/src/chapter/" + f for f in FRAGMENTS],
        "declarations": rows,
    }
    if args.write_inventory:
        INVENTORY.write_text(json.dumps(inventory, indent=2) + "\n")
    else:
        assert json.loads(INVENTORY.read_text()) == inventory, "Inventory differs; inspect before regenerating"
    if args.lean_check:
        with tempfile.TemporaryDirectory(prefix="tnlean_four_cut_references_") as tmp:
            lean = Path(tmp) / "FourCutBlueprintReferences.lean"
            imports = ["import " + p.removesuffix(".lean").replace("/", ".") for p in paths]
            # Resolve each quoted constant in the compiled environment without
            # introducing hash commands, which the standard linter rejects.
            names = ",\n    ".join("``" + d.fqn.removeprefix("TNLean.PEPS.") for d in declarations)
            check = ("run_elab do\n  let env ← Lean.getEnv\n  for name in [\n    " + names
                     + "] do\n    unless env.contains name do\n"
                     + "      throwError \"Unknown compiled declaration {name}\"\n")
            lean.write_text("\n".join(imports) + "\n\nopen TNLean.PEPS\n\n" + check)
            result = subprocess.run([
                "lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                "-DmaxSynthPendingDepth=3", "-Dlinter.mathlibStandardSet=true", "-DwarningAsError=true", str(lean)
            ], cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
            assert result.returncode == 0, "Compiled declaration check failed"
    print(f"PASS: {len(declarations)} unique public owners across {len(paths)} source modules; "
          f"{len(FRAGMENTS)} fragments have exact source/reference coverage"
          + ("; all compiled names resolve" if args.lean_check else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
