#!/usr/bin/env python3
"""Regression checks for independent tenkz corpus metadata invariants."""

from __future__ import annotations

import csv
import os
import subprocess
import tempfile
from pathlib import Path

from tenkz_audit import Audit
from tenkz_rmp import (
    ink_environment_problems,
    rendered_ink_environment_families,
    structural_capability_problems,
)
from tenkzlib.tnlog import parse_log


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "tenkz_corpus.sh"
PROVENANCE = ROOT / "tests" / "tenkz" / "PROVENANCE.tsv"


def write_rows(path: Path, rows: list[list[str]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        csv.writer(stream, dialect="excel-tab", lineterminator="\n").writerows(rows)


def validate(path: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["TENKZ_CORPUS_PROVENANCE"] = str(path)
    env["TENKZ_CORPUS_VALIDATE_ONLY"] = "1"
    return subprocess.run(
        ["bash", str(DRIVER)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )


def test_kernel_capability_owner() -> None:
    kernel_body = r"\tenkzkernel{\begin{tenkz} A \end{tenkz}}"
    if structural_capability_problems("good", ("kernel",), kernel_body):
        raise AssertionError("exclusive kernel owner tag was rejected")

    missing = structural_capability_problems("missing", ("grid",), kernel_body)
    if not any("capability 'kernel' is missing" in problem for problem in missing):
        raise AssertionError("nested grid tag hid a missing kernel owner tag")
    if not any("exclusive owner tag 'kernel'" in problem for problem in missing):
        raise AssertionError("kernel picture retained the nested grid tag")

    mixed = structural_capability_problems(
        "mixed", ("kernel", "grid"), kernel_body
    )
    if not any("exclusive owner tag 'kernel'" in problem for problem in mixed):
        raise AssertionError("kernel picture accepted both structural owner tags")

    bare_grid = r"\begin{tenkz} A \end{tenkz}"
    if structural_capability_problems("grid", ("grid",), bare_grid):
        raise AssertionError("bare grid owner tag was rejected")


def test_ink_environment_owner() -> None:
    log = "\n".join(
        (
            "picture|id=1|lang=grid",
            "picture|id=2|lang=cd",
            "picture|id=3|lang=free",
            "picture|id=4|lang=lattice",
            "picture|id=5|lang=lattice",
            "surface|picture=5|name=tenkzplanes",
            "picture|id=k1|lang=kernel",
            "tree|picture=0|id=1|style=wire|leaves=2|vertices=1|"
            "topology=(1,2)|role=none|species=none",
            "",
        )
    )
    parsed = parse_log(log, source_name="ink-owner-test.tnlog")
    used = rendered_ink_environment_families(parsed)
    expected = {"tenkz", "tenkzfree", "tenkzlattice", "tenkzplanes", "kernel"}
    if used != expected:
        raise AssertionError(f"compiled Ink owners disagree: {used!r}")
    with tempfile.TemporaryDirectory(prefix="tenkz-ink-owner-") as tmp:
        log_path = Path(tmp) / "ink-owner-test.tnlog"
        log_path.write_text(log, encoding="utf-8")
        audit = Audit(log_path, None)
        audit.parse_log()
        audit.check_dialects()
        mismatches = [
            finding for finding in audit.findings
            if finding.rule == "dialect-mismatch"
        ]
        if mismatches:
            raise AssertionError(
                "compiled Ink owner metadata was foreign to its picture dialect: "
                + "; ".join(finding.msg for finding in mismatches)
            )
    ink = "Canonical tenkz, tenkzfree, tenkzlattice, tenkzplanes, and kernel."
    if ink_environment_problems("good", ink, used):
        raise AssertionError("accurate compiled Ink owners were rejected")
    mismatch = ink_environment_problems(
        "wrong", "Canonical tenkzfree environment.", {"kernel"}
    )
    if not any("Ink names tenkzfree" in problem for problem in mismatch):
        raise AssertionError("stale Ink family was accepted")
    if not any("uses kernel but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("compiled kernel owner was omitted")


def main() -> int:
    test_kernel_capability_owner()
    test_ink_environment_owner()
    with PROVENANCE.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, dialect="excel-tab"))

    with tempfile.TemporaryDirectory(prefix="tenkz-provenance-") as tmp:
        work = Path(tmp)

        reordered = work / "reordered.tsv"
        write_rows(reordered, [rows[0], *reversed(rows[1:])])
        reordered_run = validate(reordered)
        if reordered_run.returncode:
            raise AssertionError(
                "canonical source-name digest depended on TSV row order:\n"
                + reordered_run.stdout
                + reordered_run.stderr
            )

        mutated_rows = [row.copy() for row in rows]
        excluded = next(row for row in mutated_rows[1:] if row[1] == "excluded")
        excluded[0] = "mutated-excluded-source.tex"
        mutated = work / "mutated.tsv"
        write_rows(mutated, mutated_rows)
        mutated_run = validate(mutated)
        if (mutated_run.returncode == 0
                or "source-file census SHA-256" not in mutated_run.stderr):
            raise AssertionError(
                "source-name invariant accepted an excluded-name swap:\n"
                + mutated_run.stdout
                + mutated_run.stderr
            )

        missing = work / "missing.tsv"
        missing_run = validate(missing)
        if (missing_run.returncode == 0
                or f"cannot read {missing}:" not in missing_run.stderr):
            raise AssertionError(
                "read failure did not identify the overridden provenance path:\n"
                + missing_run.stdout
                + missing_run.stderr
            )

    print("PASS: tenkz provenance source-name invariant")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
