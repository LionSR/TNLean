#!/usr/bin/env python3
"""Regression checks for independent tenkz corpus metadata invariants."""

from __future__ import annotations

import csv
import os
import subprocess
import tempfile
from pathlib import Path

from tenkz_rmp import ink_environment_problems, structural_capability_problems


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
    cases = (
        ("Canonical public tenkzfree environment.", r"\begin{tenkzfree}"),
        ("Canonical public tenkzlattice environment.", r"\begin{tenkzlattice}"),
        ("Canonical public tenkzplanes environment.", r"\begin{tenkzplanes}"),
        ("Canonical public tenkz composition.", r"\tntree{}"),
        ("Canonical public tenkz diagram.", r"\begin{tenkzcd}"),
        ("Canonical public kernel records.", r"\tenkzkernel\begin{tenkz}"),
    )
    for ink, body in cases:
        if ink_environment_problems("good", ink, body):
            raise AssertionError(f"Ink family rejected its body: {ink!r}")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public tenkzfree environment.", r"\tenkzkernel"
    )
    if not any("Ink names tenkzfree" in problem for problem in mismatch):
        raise AssertionError("stale Ink family was accepted")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public tenkzlattice environment.", r"\begin{tenkzfree}"
    )
    if not any("Ink names tenkzlattice" in problem for problem in mismatch):
        raise AssertionError("wrong Ink environment family was accepted")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public tenkz equation.", r"\begin{tenkzfree}"
    )
    if not any("Ink names tenkz" in problem for problem in mismatch):
        raise AssertionError("plain tenkz Ink claim accepted a free body")
    mismatch = ink_environment_problems(
        "wrong",
        "Canonical public tenkz composition.",
        r"\tenkzkernel\begin{tenkz}",
    )
    if not any("uses kernel but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("plain tenkz Ink claim accepted a kernel body")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public composition.", r"\tenkzkernel\begin{tenkz}"
    )
    if not any("uses kernel but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("unlisted kernel owner was accepted")
    mismatch = ink_environment_problems(
        "wrong",
        "Canonical public tenkzfree expression.",
        r"\begin{tenkzfree}\end{tenkzfree}\begin{tenkz}\end{tenkz}",
    )
    if not any("uses tenkz but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("unlisted mixed-family owner was accepted")
    mismatch = ink_environment_problems(
        "wrong",
        "Canonical public tenkz expression.",
        "\\begin{tenkz}\\end{tenkz}\n"
        "\\begin \n {tenkzfree}\\end \n {tenkzfree}",
    )
    if not any("uses tenkzfree but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("whitespace hid an unlisted mixed-family owner")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public kernel records.", r"\begin{tenkz}"
    )
    if not any("Ink names kernel" in problem for problem in mismatch):
        raise AssertionError("kernel Ink claim accepted the grid surface")
    mixed = (
        r"{\tenkzkernel\begin{tenkz}\end{tenkz}}"
        r"\begin{tenkz}\end{tenkz}"
    )
    if ink_environment_problems(
        "good", "Canonical public kernel and tenkz pictures.", mixed
    ):
        raise AssertionError("scoped mixed kernel and tenkz pictures were rejected")
    mismatch = ink_environment_problems(
        "wrong", "Canonical public kernel picture.", mixed
    )
    if not any("uses tenkz but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("unlisted plain picture after kernel scope was accepted")
    escaped_scope_tokens = (
        r"{\tenkzkernel\begin{tenkz}\{\end{tenkz}}"
        "\\\\[1em]\n"
        r"\begin{tenkz}\end{tenkz}"
    )
    if ink_environment_problems(
        "good",
        "Canonical public kernel and tenkz pictures.",
        escaped_scope_tokens,
    ):
        raise AssertionError("escaped braces or line spacing corrupted Ink scope")
    dollar_scopes = (
        r"$\tenkzkernel\begin{tenkz}\end{tenkz}$"
        r"\[\begin{tenkz}\end{tenkz}\]"
        r"$$\tenkzkernel\begin{tenkz}\end{tenkz}$$"
        r"\begin{tenkz}\end{tenkz}"
    )
    if ink_environment_problems(
        "good", "Canonical public kernel and tenkz pictures.", dollar_scopes
    ):
        raise AssertionError("dollar-delimited math leaked the kernel owner")


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
