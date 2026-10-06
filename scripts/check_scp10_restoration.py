#!/usr/bin/env python3
"""Verify archive provenance and require a complete local TNLean source closure.

This is a source preflight, never evidence of Lean compilation or source faithfulness.
Missing source cannot be satisfied by cached oleans. No network access is performed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from lean_import_syntax import MODULE_NAME, strip_lean_comments

ARCHIVE = "ca5273cd335633e0aea2e4930c897d732b8260de"
ARCHIVE_ROOT = "docs/recovery/scp10-20261005/"
EXCLUDED = "TNLean/PEPS/TorusCorrelatedChargePairCreation.lean"
IMPORT = re.compile(rf"(?m)^\s*(?:public\s+)?import\s+({MODULE_NAME})\s*$")


def archive_read(root: Path, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "show", f"{ARCHIVE}:{ARCHIVE_ROOT}{path}"], cwd=root
    )


def verify_archive(root: Path) -> list[dict]:
    manifest = json.loads(archive_read(root, "manifest.json"))
    originals = json.loads(archive_read(root, "historical-reviewed-source-sha256.json"))
    files = manifest["files"]
    if len(files) != 20 or len({f["path"] for f in files}) != 20:
        raise ValueError("Unexpected archive inventory")
    for entry in files:
        path = entry["path"]
        if not path.startswith("source/") or ".." in Path(path).parts:
            raise ValueError(f"Invalid source path: {path}")
        digest = hashlib.sha256(archive_read(root, path)).hexdigest()
        if digest != entry["sha256"]:
            raise ValueError(f"Archive hash mismatch: {path}")
        if entry["recovery_status"] == "historical_source_sha256_match":
            recorded = originals.get(path.removeprefix("source/"))
            if recorded is not None and recorded != digest:
                raise ValueError(f"Historical hash mismatch: {path}")
            entry["historical_digest_table_match"] = recorded == digest
    return [entry for entry in files if entry["path"] != "source/" + EXCLUDED]


def source_closure(root: Path, targets: list[str]) -> tuple[list[str], list[str]]:
    pending = list(targets)
    visited: set[str] = set()
    missing: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        path = root / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            missing.add(module)
            continue
        source, error = strip_lean_comments(path.read_text())
        if error:
            raise ValueError(f"{path}: {error}")
        for line in source.splitlines():
            if not re.match(r"^\s*(?:public\s+)?import\b", line):
                continue
            match = IMPORT.fullmatch(line)
            if match is None:
                raise ValueError(f"Unsupported import syntax in {path}: {line}")
            name = match.group(1)
            if name.startswith(("TNLean.", "TNLeanTest.")):
                pending.append(name)
    return sorted(visited), sorted(missing)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    entries = verify_archive(args.root)
    targets = [
        entry["path"].removeprefix("source/").removesuffix(".lean").replace("/", ".")
        for entry in entries if entry["path"].endswith(".lean")
    ]
    targets += ["TNLeanTest.CommutingMatrixProjectionProduct"]
    visited, missing = source_closure(args.root, targets)
    report = {
        "archive": ARCHIVE,
        "archive_hashes_verified": 20,
        "restoration_files": len(entries),
        "manifest_claimed_historical_original_matches_in_scope": sum(
            entry["recovery_status"] == "historical_source_sha256_match" for entry in entries
        ),
        "independently_matched_historical_digest_table_entries": sum(
            entry.get("historical_digest_table_match", False) for entry in entries
        ),
        "manifest_original_match_claim_without_digest_table_entry": [
            entry["path"].removeprefix("source/") for entry in entries
            if entry.get("historical_digest_table_match") is False
        ],
        "visited_tn_source_modules": len(visited),
        "missing_tn_source_modules": missing,
        "lean_compilation": "not_checked_by_this_script",
        "external_dependency_closure": "requires_pinned_Lake_build",
    }
    print(json.dumps(report, indent=2))
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
