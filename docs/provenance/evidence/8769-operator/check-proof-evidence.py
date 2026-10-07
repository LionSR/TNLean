#!/usr/bin/env python3
"""Check immutable proof bytes, log hashes and complete source/kernel name parity."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
EVIDENCE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "scripts"))
from blueprint_lean_sync import collect_file_lean_decls

PROOF_REVISION = "a89886d64e31b363c8dde1411410af3cd9b5ef66"
ORIGINAL_REVISION = "ac065a663f42d97e160a223b868ce162fe0c7d7f"
MODULE = "TNLean/PEPS/Approximation/DistributedOperatorContraction.lean"


def main() -> None:
    source = (ROOT / MODULE).read_bytes()
    committed = subprocess.check_output(
        ["git", "show", f"{PROOF_REVISION}:{MODULE}"], cwd=ROOT
    )
    assert source == committed, "Current proof bytes differ from recorded proof revision"
    original = subprocess.check_output(
        ["git", "show", f"{ORIGINAL_REVISION}:{MODULE}"], cwd=ROOT
    )
    restored, notice_count = re.subn(
        rb"/\- TNLean\.PEPS\.Approximation\.DistributedOperatorContraction\.[^\n]+\n"
        rb"Provenance-ID: [^\n]+\n"
        rb"Source: September 24, 2026; thm:compression; no upstream Lean proof text reused\."
        rb" \-/\n\n", b"", source
    )
    assert notice_count == 49 and restored == original
    assert not re.search(rb"\b(sorry|admit|native_decide|unsafeCast|axiom)\b", restored)
    checks = json.loads((EVIDENCE / "checks.json").read_text())
    for check in checks["checks"]:
        assert check["exit_code"] == check["warnings"] == 0
        assert hashlib.sha256((ROOT / check["log"]).read_bytes()).hexdigest() == check["sha256"]
    names = {
        decl.fqn for decl in collect_file_lean_decls(ROOT / MODULE, ROOT / "TNLean")
        if not decl.is_private
    }
    audit = (ROOT / "scripts/distributed_operator_contraction_axioms.lean").read_text()
    script_names = re.findall(r"^#print axioms\s+(\S+)$", audit, flags=re.M)
    output = (EVIDENCE / "axioms.log").read_text()
    records = re.findall(
        r"^'([^']+)' (depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)",
        output, flags=re.M
    )
    assert len(names) == len(script_names) == len(records) == 49
    assert names == set(script_names) == {name for name, _ in records}
    for name, record in records:
        match = re.search(r"\[([^]]*)\]", record)
        axioms = {item.strip() for item in match.group(1).split(",")} if match else set()
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, (name, axioms)
    owner = json.loads((EVIDENCE / "original-ac065a6/owner-report.json").read_text())
    assert owner["proof_commit"] == ORIGINAL_REVISION and set(owner["public_names"]) == names
    assert owner["proof_sha256"] == hashlib.sha256(original).hexdigest()
    for check in owner["checks"]:
        data = (EVIDENCE / f'original-ac065a6/{check["name"]}.log').read_bytes()
        assert hashlib.sha256(data).hexdigest() == check["sha256"]
    print("PASS: all49 exact source, audit-script and compiled audit names match.")
    print("Axioms: propext, Classical.choice, Quot.sound only.")
    print("Proof revision: " + PROOF_REVISION)
    print("Proof SHA-256: " + hashlib.sha256(source).hexdigest())
    print("Source lines: " + str(len(source.splitlines())))
    print("Original reviewed mathematical source is unchanged after removing49 notices.")
    print("Original revision: " + ORIGINAL_REVISION)
    print("Original proof SHA-256: " + hashlib.sha256(original).hexdigest())
    print("All recorded final checks and original five log byte streams match their hashes.")


if __name__ == "__main__":
    main()
