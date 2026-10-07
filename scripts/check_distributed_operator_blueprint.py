#!/usr/bin/env python3
"""Check operator-contraction coverage and immutable manuscript anchors.

This checks source, blueprint, axiom-script and provenance inventories. It does
not certify source faithfulness or complete the circuit compression theorem.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

from blueprint_lean_sync import (
    collect_blueprint_entries,
    collect_blueprint_lean_refs,
    collect_file_lean_decls,
)

ROOT = Path(__file__).resolve().parents[1]
PIN = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
PAPER = (
    "preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-"
    "September-24-2026/build/sections/04-compression.tex"
)
MODULE = "TNLean/PEPS/Approximation/DistributedOperatorContraction.lean"
FRAGMENT = "ch24_peps_distributed_operator.tex"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-root", type=Path, required=True)
    args = parser.parse_args()
    declarations = [
        declaration
        for declaration in collect_file_lean_decls(ROOT / MODULE, ROOT / "TNLean")
        if not declaration.is_private
    ]
    names = {declaration.fqn for declaration in declarations}
    assert len(names) == len(declarations) == 49, "Unexpected public declaration inventory"
    entries = collect_blueprint_entries(ROOT / "blueprint/src")
    counts = Counter(ref.lean_decl for ref in collect_blueprint_lean_refs(ROOT / "blueprint/src"))
    for name in sorted(names):
        owners = [entry for entry in entries if entry.lean_decl == name]
        assert len(owners) == counts[name] == 1, (name, "unique blueprint owner")
        owner = owners[0]
        assert Path(owner.file).name == FRAGMENT and owner.has_leanok, name
        if owner.env_type == "theorem":
            assert owner.proof_has_leanok, (name, "checked proof marker")
    audit = (ROOT / "scripts/distributed_operator_contraction_axioms.lean").read_text()
    audit_names = re.findall(r"^#print axioms\s+(\S+)$", audit, flags=re.M)
    assert set(audit_names) == names and len(audit_names) == 49, "Axiom audit coverage"
    shard = json.loads((ROOT / "docs/provenance/openai-math.d/8769-operator.json").read_text())
    assert {entry["downstream"]["declaration"] for entry in shard["entries"]} == names
    assert len(shard["entries"]) == 49, "Provenance coverage"
    manuscript = subprocess.check_output(
        ["git", "-C", str(args.upstream_root), "show", f"{PIN}:{PAPER}"]
    )
    text = manuscript.decode()
    labels = sorted({label for entry in shard["entries"]
                     for source in entry["paper_sources"] for label in source["labels"]})
    for label in labels:
        assert len(re.findall(r"\\label\s*\{\s*" + re.escape(label) + r"\s*\}", text)) == 1
    print(f"PASS: {len(names)} public declarations; unique checked blueprint owners;")
    print("complete axiom-script and provenance coverage.")
    print(f"Paper: openai/math@{PIN}:{PAPER}")
    print(f"Paper SHA-256: {hashlib.sha256(manuscript).hexdigest()}")
    print("Verified paper labels: " + ", ".join(labels))
    print("Scope: exact contraction of supplied local operators, including density-label pairs.")
    print("Open: actual circuit-to-local-operator identification and uniform polynomial labels.")
    for name in sorted(names):
        print("Public declaration: " + name)
    print("--- Immutable manuscript lines 565-588 ---")
    for line, content in enumerate(text.splitlines()[564:588], 565):
        print(f"{line}: {content}".rstrip())


if __name__ == "__main__":
    main()
