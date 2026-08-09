#!/usr/bin/env python3
"""Contract tests for the CTAN staging tree and its checks.

Each test seeds the defect the corresponding check exists to catch, so a
check that stopped catching it fails here rather than passing quietly at a
release. The end-to-end run against the real tree is the last test.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/tenkz_ctan.py"

sys.path.insert(0, str(ROOT / "scripts"))
import tenkz_ctan  # noqa: E402


STAGE_CONTRACT = (
    "% Input: nothing\n"
    "% Output: nothing\n"
    "% Owned state: none\n"
    "% Invariants: none\n"
    "% Next stage: none\n"
    "% SPDX-License-Identifier: Apache-2.0\n"
    "% Copyright the TNLean project; see LICENSE for the full terms.\n"
)


def fake_source(room: Path) -> Path:
    """A source directory shaped like `tex/tenkz`, with a two-stage load graph."""

    source = room / "tex"
    source.mkdir(parents=True)
    (source / "tenkz.sty").write_text(
        STAGE_CONTRACT
        + "\\ProvidesPackage{tenkz}[2026/07/22 v0.7 Declarative diagrams]\n"
        "\\RequirePackage{tikz}\n"
        "\\usetikzlibrary{calc,\n  hobby}\n"
        "% \\input{tenkz-tombstone.code.tex}\n"
        "\\input{tenkz-stage.code.tex}\n",
        encoding="utf-8",
    )
    (source / "tenkz-stage.code.tex").write_text(
        STAGE_CONTRACT + "\\input{tenkz-leaf.code.tex}\n", encoding="utf-8"
    )
    (source / "tenkz-leaf.code.tex").write_text(STAGE_CONTRACT, encoding="utf-8")
    return source


def test_closure_reads_the_load_graph_and_not_the_prose() -> None:
    with tempfile.TemporaryDirectory() as directory:
        source = fake_source(Path(directory))
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
    assert closure.files == [
        "tenkz.sty",
        "tenkz-stage.code.tex",
        "tenkz-leaf.code.tex",
    ], closure.files
    assert closure.packages == ["tikz"]
    assert closure.libraries == ["calc", "hobby"], closure.libraries


def test_closure_agrees_with_the_pinned_manifest() -> None:
    report = tenkz_ctan.check_closure(
        tenkz_ctan.walk_closure(), tenkz_ctan.read_manifest()
    )
    assert not report.failures, report.failures


def test_a_source_file_outside_the_load_graph_fails_the_check() -> None:
    with tempfile.TemporaryDirectory() as directory:
        source = fake_source(Path(directory))
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
        manifest = {"source_tree": {"excluded": []}}
        assert not tenkz_ctan.check_source_tree(closure, manifest, source).failures
        (source / "tenkz-orphan.code.tex").write_text("% nothing\n", encoding="utf-8")
        (source / "tenkz.log").write_text("a compilation leftover\n", encoding="utf-8")
        failures = tenkz_ctan.check_source_tree(closure, manifest, source).failures
    assert any("tenkz-orphan.code.tex" in reason for reason in failures), failures
    assert any("leftover" in reason for reason in failures), failures


def test_an_unlicensed_runtime_file_fails_the_header_audit() -> None:
    with tempfile.TemporaryDirectory() as directory:
        source = fake_source(Path(directory))
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
        assert not tenkz_ctan.check_headers(closure, source).failures
        stripped = (source / "tenkz-leaf.code.tex").read_text(encoding="utf-8")
        (source / "tenkz-leaf.code.tex").write_text(
            stripped.replace(tenkz_ctan.LICENSE_MARKER, "% none of your business"),
            encoding="utf-8",
        )
        failures = tenkz_ctan.check_headers(closure, source).failures
    assert any("tenkz-leaf.code.tex" in reason for reason in failures), failures


def test_the_version_comes_from_one_declaration_or_from_none() -> None:
    with tempfile.TemporaryDirectory() as directory:
        entry = Path(directory) / "tenkz.sty"
        entry.write_text(
            "\\ProvidesPackage{tenkz}[2026/07/22 v0.7 Declarative diagrams]\n",
            encoding="utf-8",
        )
        release = tenkz_ctan.read_release(entry)
        assert (release.version, release.date) == ("0.7", "2026-07-22")
        assert release.archive_stem == "tenkz-0.7"

        entry.write_text(
            "\\ProvidesPackage{tenkz}[2026/07/22 v0.7 One]\n"
            "\\ProvidesPackage{tenkz}[2026/07/23 v0.8 Two]\n",
            encoding="utf-8",
        )
        assert _refuses(entry, "exactly one")

        entry.write_text("\\ProvidesPackage{tenkz}[whenever v0.7]\n", encoding="utf-8")
        assert _refuses(entry, "not\nspelled".replace("\n", " "))


def _refuses(entry: Path, fragment: str) -> bool:
    try:
        tenkz_ctan.read_release(entry)
    except SystemExit as refusal:
        return fragment in str(refusal)
    return False


def test_a_stated_version_other_than_the_declared_one_fails() -> None:
    manifest = tenkz_ctan.read_manifest()
    assert not tenkz_ctan.check_version(tenkz_ctan.read_release(), manifest).failures
    invented = tenkz_ctan.Release(version="9.9", date="1999-01-01")
    failures = tenkz_ctan.check_version(invented, manifest).failures
    assert len(failures) == 4, failures


def test_the_archive_is_a_function_of_the_files_it_carries() -> None:
    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        subject = room / "tenkz.sty"
        subject.write_text("% one\n", encoding="utf-8")
        release = tenkz_ctan.Release(version="0.7", date="2026-07-22")
        digests = []
        for label in ("first", "second"):
            destination = room / label
            destination.mkdir()
            archive = tenkz_ctan.write_archive(
                destination, release, release.epoch, {"tenkz.sty": subject}
            )
            digests.append(archive.read_bytes())
        assert digests[0] == digests[1]

        subject.write_text("% two\n", encoding="utf-8")
        destination = room / "third"
        destination.mkdir()
        changed = tenkz_ctan.write_archive(
            destination, release, release.epoch, {"tenkz.sty": subject}
        )
        assert changed.read_bytes() != digests[0]


def test_staging_ignores_the_builders_file_creation_mask() -> None:
    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        subject = room / "tenkz.sty"
        subject.write_text("% one\n", encoding="utf-8")
        previous = os.umask(0o077)
        try:
            tree = tenkz_ctan.stage(room / "out", 1000000, {"tenkz.sty": subject})
        finally:
            os.umask(previous)
        assert (tree / "tenkz.sty").stat().st_mode & 0o777 == 0o644
        assert tree.stat().st_mode & 0o777 == 0o755
        assert (tree / "tenkz.sty").stat().st_mtime == 1000000


def test_the_environment_may_fix_the_timestamp() -> None:
    release = tenkz_ctan.Release(version="0.7", date="2026-07-22")
    previous = os.environ.get("SOURCE_DATE_EPOCH")
    os.environ["SOURCE_DATE_EPOCH"] = "1600000000"
    try:
        assert tenkz_ctan.chosen_epoch(release) == 1600000000
    finally:
        if previous is None:
            del os.environ["SOURCE_DATE_EPOCH"]
        else:
            os.environ["SOURCE_DATE_EPOCH"] = previous
    assert tenkz_ctan.chosen_epoch(release) == release.epoch


def test_names_outside_the_invariant_subset_fail() -> None:
    accidental = Path("/dev/null")
    report = tenkz_ctan.check_names(
        {
            "tenkz.sty": accidental,
            "tenkz-café.tex": accidental,
            "-tenkz.tex": accidental,
            "TENKZ.STY": accidental,
        }
    )
    assert len(report.failures) == 3, report.failures
    assert any("café" in reason for reason in report.failures)
    assert any("differ only in case" in reason for reason in report.failures)


def test_the_staged_tree_carries_no_compilation_leftovers() -> None:
    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / "tenkz"
        tree.mkdir()
        (tree / "tenkz.sty").write_text("% one\n", encoding="utf-8")
        assert not tenkz_ctan.check_debris(tree).failures
        (tree / "tenkz.log").write_text("a compilation leftover\n", encoding="utf-8")
        failures = tenkz_ctan.check_debris(tree).failures
    assert any("would ship" in reason for reason in failures), failures


def test_check_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "check"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
