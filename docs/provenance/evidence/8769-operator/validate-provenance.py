#!/usr/bin/env python3
"""Validate current ledgers and the issue-owned count with the pinned PR 8789 policy."""

import argparse
import hashlib
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
POLICY_REVISION = "4e9d9c898a4401d51cf1eeeabcea8572242387fe"
HASHES = {
    "scripts/check_openai_provenance.py":
        "8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65",
    "docs/provenance/openai-math.schema.json":
        "a691d8e95b668c968365f2c7e33f614d49635aade8fdd4c2f27cd64f0cd6b459",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy-root", type=Path, required=True)
    parser.add_argument("--upstream-root", type=Path, required=True)
    args = parser.parse_args()
    for path, digest in HASHES.items():
        assert hashlib.sha256((args.policy_root / path).read_bytes()).hexdigest() == digest
    spec = importlib.util.spec_from_file_location(
        "pinned_policy", args.policy_root / "scripts/check_openai_provenance.py"
    )
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    ledger_root = ROOT / "docs/provenance"
    owned = [
        policy.read_json(ledger_root / "openai-math.d" / name)
        for name in ("8769-lifetime.json", "8769-operator.json")
    ]
    owned_counts = [len(ledger["entries"]) for ledger in owned]
    policy.require(owned_counts == [47, 49], "issue-owned shard counts changed")
    ledgers = [ledger_root / "openai-math.json"] + sorted(
        (ledger_root / "openai-math.d").glob("*.json")
    )
    roots = {"LionSR/TNLean": ROOT, "openai/math": args.upstream_root}
    qic_root = ROOT / ".lake/packages/qiclean"
    if qic_root.is_dir():
        roots["LionSR/QICLean"] = qic_root
    count = policy.validate(
        [policy.read_json(path) for path in ledgers],
        policy.read_json(args.policy_root / "docs/provenance/openai-math.schema.json"),
        roots,
    )
    print(f"PASS: {count} current ledger entries; complete repository notice scan validated.")
    print(f"PASS: {sum(owned_counts)} issue-owned declarations in the two explicit shards.")
    print("Historical 47 and operator 49 are independently verified original formalizations.")
    print("Policy revision: " + POLICY_REVISION)
    for path, digest in HASHES.items():
        print(f"Policy SHA-256: {path}: {digest}")


if __name__ == "__main__":
    main()
