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
    AUTHOR_SOURCE_HASHES,
    DEFAULT_MANIFEST,
    RMPError,
    ink_environment_problems,
    load_author_source_hashes,
    load_manifest,
    rendered_ink_environment_families,
    sha256,
    structural_capability_problems,
    verify_author_source_tree,
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
    expected = {
        "tenkz",
        "tenkzcd",
        "tenkzfree",
        "tenkzlattice",
        "tenkzplanes",
        "kernel",
    }
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
    ink = (
        "Canonical tenkz, tenkzcd, tenkzfree, tenkzlattice, tenkzplanes, "
        "and kernel."
    )
    if ink_environment_problems("good", ink, used):
        raise AssertionError("accurate compiled Ink owners were rejected")
    cd_only = parse_log(
        "picture|id=1|lang=cd\n", source_name="ink-cd-owner-test.tnlog"
    )
    cd_used = rendered_ink_environment_families(cd_only)
    if cd_used != {"tenkzcd"}:
        raise AssertionError(f"tenkzcd was collapsed into another owner: {cd_used!r}")
    cd_mismatch = ink_environment_problems(
        "cd-as-tenkz", "Canonical public tenkz environment.", cd_used
    )
    if not (
        any("Ink names tenkz" in problem for problem in cd_mismatch)
        and any("uses tenkzcd" in problem for problem in cd_mismatch)
    ):
        raise AssertionError("plain tenkz Ink was accepted for a tenkzcd picture")
    tree_only = parse_log(
        "tree|picture=0|id=1|style=wire|leaves=2|vertices=1|"
        "topology=(1,2)|role=none|species=none\n",
        source_name="ink-tree-owner-test.tnlog",
    )
    tree_used = rendered_ink_environment_families(tree_only)
    if tree_used != {"tenkz"}:
        raise AssertionError(f"standalone tree lost its tenkz owner: {tree_used!r}")
    cd_tree = parse_log(
        "picture|id=1|lang=cd\n"
        "tree|picture=1|id=1|style=wire|leaves=2|vertices=1|"
        "topology=(1,2)|role=none|species=none\n",
        source_name="ink-cd-tree-owner-test.tnlog",
    )
    cd_tree_used = rendered_ink_environment_families(cd_tree)
    if cd_tree_used != {"tenkzcd"}:
        raise AssertionError(
            f"tree inside tenkzcd gained a second owner: {cd_tree_used!r}"
        )
    mismatch = ink_environment_problems(
        "wrong", "Canonical tenkzfree environment.", {"kernel"}
    )
    if not any("Ink names tenkzfree" in problem for problem in mismatch):
        raise AssertionError("stale Ink family was accepted")
    if not any("uses kernel but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("compiled kernel owner was omitted")


def test_rmp_author_source_identity() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    cited = sorted(
        {
            target.author_source
            for target in targets
            if target.author_source is not None
        },
        key=lambda path: path.as_posix(),
    )
    committed = sorted(
        load_author_source_hashes(AUTHOR_SOURCE_HASHES),
        key=lambda path: path.as_posix(),
    )
    if committed != cited:
        raise AssertionError(
            "committed author-source hashes disagree with manifest.toml"
        )
    with tempfile.TemporaryDirectory(prefix="tenkz-rmp-author-source-") as tmp:
        work = Path(tmp)
        source_root = work / "RMP_TIKZ_SOURCE_CODE"
        for index, source in enumerate(cited, 1):
            candidate = source_root / source
            candidate.parent.mkdir(parents=True, exist_ok=True)
            candidate.write_text(f"author source {index}\n", encoding="utf-8")
        hashes = work / "author-source.sha256"
        hashes.write_text(
            "".join(
                f"{sha256(source_root / source)}  {source.as_posix()}\n"
                for source in cited
            ),
            encoding="utf-8",
        )
        verified = verify_author_source_tree(
            targets, source_root, hashes_path=hashes
        )
        if verified != len(cited):
            raise AssertionError("author-source verifier lost a cited source")

        changed = source_root / cited[0]
        original = changed.read_text(encoding="utf-8")
        changed.write_text("different authority\n", encoding="utf-8")
        try:
            verify_author_source_tree(targets, source_root, hashes_path=hashes)
        except RMPError as exc:
            if "author source hash mismatch" not in str(exc):
                raise AssertionError(
                    f"changed author source produced the wrong failure: {exc}"
                ) from exc
        else:
            raise AssertionError("changed author source passed identity verification")

        changed.write_text(original, encoding="utf-8")
        hashes.write_text(
            hashes.read_text(encoding="utf-8")
            + f"{'0' * 64}  uncited.tex\n",
            encoding="utf-8",
        )
        try:
            verify_author_source_tree(targets, source_root, hashes_path=hashes)
        except RMPError as exc:
            if "uncited: uncited.tex" not in str(exc):
                raise AssertionError(
                    f"uncited hash entry produced the wrong failure: {exc}"
                ) from exc
        else:
            raise AssertionError("uncited author-source hash entry was accepted")


def main() -> int:
    test_kernel_capability_owner()
    test_ink_environment_owner()
    test_rmp_author_source_identity()
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
