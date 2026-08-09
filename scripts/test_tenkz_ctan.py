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
PACKAGE_DIR = "tenkz"

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


def test_closure_reads_tex_spacing_before_arguments() -> None:
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        (source / "tenkz.sty").write_text(
            STAGE_CONTRACT
            + "\\RequirePackage [draft] {tikz}\n"
            "\\usetikzlibrary\n  {calc}\n"
            "\\input % the stage below\n  {tenkz-stage.code.tex}\n",
            encoding="utf-8",
        )
        (source / "tenkz-stage.code.tex").write_text(STAGE_CONTRACT, encoding="utf-8")
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
    assert closure.files == ["tenkz.sty", "tenkz-stage.code.tex"], closure.files
    assert closure.packages == ["tikz"], closure.packages
    assert closure.libraries == ["calc"], closure.libraries


def test_a_runtime_file_that_is_not_utf8_is_refused_by_name() -> None:
    with tempfile.TemporaryDirectory() as directory:
        source = fake_source(Path(directory))
        (source / "tenkz-leaf.code.tex").write_bytes(
            STAGE_CONTRACT.encode("utf-8") + b"% \xff\xfe not text\n"
        )
        try:
            tenkz_ctan.walk_closure(source, "tenkz.sty")
        except SystemExit as refusal:
            assert "tenkz-leaf.code.tex is not UTF-8" in str(refusal), str(refusal)
        else:
            raise AssertionError("a file that is not UTF-8 was walked")


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
        assert _refuses(entry, "not spelled")

        # A dotted run of digits is not a version. Each of these would
        # otherwise become an archive name and three citation strings.
        for typo in ("v1..0", "v1.", "v.1", "v..."):
            entry.write_text(
                f"\\ProvidesPackage{{tenkz}}[2026/07/22 {typo} Diagrams]\n",
                encoding="utf-8",
            )
            assert _refuses(entry, "not spelled"), typo

        # A date of the right shape that no calendar has.
        entry.write_text(
            "\\ProvidesPackage{tenkz}[2026/02/31 v0.7 Diagrams]\n", encoding="utf-8"
        )
        assert _refuses(entry, "is not a calendar date")

        # An empty description, which the release harness's own assertion
        # rejects; the two gates read the same declaration and must agree.
        entry.write_text(
            "\\ProvidesPackage{tenkz}[2026/07/22 v0.7 ]\n", encoding="utf-8"
        )
        assert _refuses(entry, "not spelled")


def test_a_manifest_that_would_write_the_wrong_file_is_refused() -> None:
    closure = tenkz_ctan.walk_closure()
    for material, fragment in (
        ({"tenkz.sty": "LICENSE"}, "runtime name"),
        ({"../outside.md": "LICENSE"}, "will not be written"),
        ({"README.md": "LICENSE", "readme.md": "LICENSE"}, "differ only in case"),
    ):
        try:
            tenkz_ctan.staged_content({"material": material}, closure)
        except SystemExit as refusal:
            assert fragment in str(refusal), (material, str(refusal))
        else:
            raise AssertionError(f"{material} was staged rather than refused")


def _refuses(entry: Path, fragment: str) -> bool:
    try:
        tenkz_ctan.read_release(entry)
    except SystemExit as refusal:
        return fragment in str(refusal)
    return False


def test_a_stated_version_other_than_the_declared_one_fails() -> None:
    manifest = tenkz_ctan.read_manifest()
    assert not tenkz_ctan.check_version(tenkz_ctan.read_release(), manifest).failures
    invented = tenkz_ctan.Release(version="9.9", date="1999-02-01")
    failures = tenkz_ctan.check_version(invented, manifest).failures
    assert len(failures) == 6, failures
    assert any("year 1999" in reason for reason in failures), failures
    assert any("month 2" in reason for reason in failures), failures


def test_absent_material_is_reported_rather_than_raised() -> None:
    manifest = {
        "material": {
            "README.md": "docs/tenkz/ctan/nothing-here.md",
            "CITATION.cff": "docs/tenkz/ctan/nothing-here.cff",
            "tenkz.bib": "docs/tenkz/ctan/nothing-here.bib",
        }
    }
    report = tenkz_ctan.check_version(tenkz_ctan.read_release(), manifest)
    assert len(report.failures) == 6, report.failures

    material = tenkz_ctan.check_material(manifest)
    assert any("LICENSE" in reason for reason in material.failures), material.failures
    assert any("CHANGES.md" in reason for reason in material.failures), material.failures

    encoding = tenkz_ctan.check_encoding(
        {name: ROOT / relative for name, relative in manifest["material"].items()}
    )
    assert len(encoding.failures) == 3, encoding.failures


def test_the_whole_check_reports_a_missing_file_rather_than_raising() -> None:
    """The command itself, not one check in isolation: a manifest that names a
    file which is not there must print its report and exit 1."""

    original = (ROOT / "docs/tenkz/ctan/MANIFEST.toml").read_text(encoding="utf-8")
    broken = original.replace(
        '"CITATION.cff" = "docs/tenkz/ctan/CITATION.cff"',
        '"CITATION.cff" = "docs/tenkz/ctan/nothing-here.cff"',
    )
    assert broken != original
    with tempfile.TemporaryDirectory() as directory:
        manifest = Path(directory) / "MANIFEST.toml"
        manifest.write_text(broken, encoding="utf-8")
        finished = subprocess.run(
            [sys.executable, str(SCRIPT), "check"],
            capture_output=True,
            text=True,
            env={**os.environ, "TENKZ_CTAN_MANIFEST": str(manifest)},
        )
    assert finished.returncode == 1, finished.stdout + finished.stderr
    assert "Traceback" not in finished.stderr, finished.stderr
    assert "nothing-here.cff is declared and missing" in finished.stdout, finished.stdout
    assert "SKIP clean-install" in finished.stdout, finished.stdout


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
        assert not tenkz_ctan.check_permissions(tree).failures
        tree.chmod(0o700)
        failures = tenkz_ctan.check_permissions(tree).failures
        tree.chmod(0o755)
    assert any("700" in reason for reason in failures), failures


def test_the_environment_may_fix_the_timestamp() -> None:
    release = tenkz_ctan.Release(version="0.7", date="2026-07-22")
    previous = os.environ.get("SOURCE_DATE_EPOCH")
    try:
        os.environ["SOURCE_DATE_EPOCH"] = "1600000000"
        assert tenkz_ctan.chosen_epoch(release) == 1600000000
        # A zip date counts in two-second steps, so an odd second stamped on
        # the tree would arrive in the archive as the second before it.
        os.environ["SOURCE_DATE_EPOCH"] = "1600000001"
        assert tenkz_ctan.chosen_epoch(release) == 1600000000
        # A zip entry carries no date before 1980, and 0 is the value the
        # reproducibility convention hands out most often.
        os.environ["SOURCE_DATE_EPOCH"] = "0"
        assert tenkz_ctan.chosen_epoch(release) == tenkz_ctan.ZIP_EPOCH_FLOOR
        # Past the format's ceiling is a mistake, not a convention, so it is
        # refused rather than clamped; nonsense is refused by its own message.
        for value, fragment in (
            ("9999999999", "later than the last moment"),
            ("not-a-number", "not a number of seconds"),
        ):
            os.environ["SOURCE_DATE_EPOCH"] = value
            try:
                tenkz_ctan.chosen_epoch(release)
            except SystemExit as refusal:
                assert fragment in str(refusal), str(refusal)
            else:
                raise AssertionError(f"{value} was accepted")
        os.environ["SOURCE_DATE_EPOCH"] = "0"
        with tempfile.TemporaryDirectory() as directory:
            room = Path(directory)
            subject = room / "tenkz.sty"
            subject.write_text("% one\n", encoding="utf-8")
            archive = tenkz_ctan.write_archive(
                room, release, tenkz_ctan.chosen_epoch(release), {"tenkz.sty": subject}
            )
            assert archive.is_file()
    finally:
        if previous is None:
            del os.environ["SOURCE_DATE_EPOCH"]
        else:
            os.environ["SOURCE_DATE_EPOCH"] = previous
    assert tenkz_ctan.chosen_epoch(release) == release.epoch


def test_the_clean_install_check_reads_where_the_runtime_came_from() -> None:
    with tempfile.TemporaryDirectory() as directory:
        record = Path(directory) / "smoke.fls"
        record.write_text(
            "PWD /work\n"
            "INPUT /work/tenkz/tenkz.sty\n"
            "INPUT /usr/share/texmf/tex/latex/tikz/tikz.sty\n"
            "INPUT tenkz/tenkz-render.code.tex\n"
            "OUTPUT /work/smoke.pdf\n",
            encoding="utf-8",
        )
        opened = tenkz_ctan.resolved_runtime_files(record)
    assert opened == ["/work/tenkz/tenkz.sty", "tenkz/tenkz-render.code.tex"], opened

    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory).resolve()
        unpacked = room / "tenkz"
        unpacked.mkdir()
        installed = room / "texmf"
        installed.mkdir()
        strangers = tenkz_ctan.foreign_runtime_files(
            [
                str(unpacked / "tenkz.sty"),
                "tenkz/tenkz-render.code.tex",
                str(installed / "tenkz-kernel.code.tex"),
            ],
            room,
            unpacked,
        )
    assert strangers == [str(installed / "tenkz-kernel.code.tex")], strangers


def test_names_outside_the_invariant_subset_fail() -> None:
    accidental = Path("/dev/null")
    report = tenkz_ctan.check_names(
        {
            "tenkz.sty": accidental,
            "tenkz-café.tex": accidental,
            "-tenkz.tex": accidental,
            "TENKZ.STY": accidental,
            "README.": accidental,
            "NUL": accidental,
            "com1.tex": accidental,
        }
    )
    assert len(report.failures) == 6, report.failures
    assert any("café" in reason for reason in report.failures)
    assert any("differ only in case" in reason for reason in report.failures)
    assert any("ends in a dot" in reason for reason in report.failures)
    assert sum("reserved device name" in reason for reason in report.failures) == 2


def test_the_staged_tree_carries_no_compilation_leftovers() -> None:
    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / "tenkz"
        tree.mkdir()
        (tree / "tenkz.sty").write_text("% one\n", encoding="utf-8")
        assert not tenkz_ctan.check_debris(tree).failures
        (tree / "tenkz.log").write_text("a compilation leftover\n", encoding="utf-8")
        failures = tenkz_ctan.check_debris(tree).failures
    assert any("would ship" in reason for reason in failures), failures


def test_an_output_directory_loses_only_this_tools_artifacts() -> None:
    with tempfile.TemporaryDirectory() as directory:
        out = Path(directory) / "out"
        out.mkdir()
        (out / PACKAGE_DIR).mkdir()
        (out / "tenkz-0.7.zip").write_text("old\n", encoding="utf-8")
        tenkz_ctan.clear_destination(out)
        assert list(out.iterdir()) == []

        (out / "somebody-elses-notes.txt").write_text("keep me\n", encoding="utf-8")
        try:
            tenkz_ctan.clear_destination(out)
        except SystemExit as refusal:
            assert "somebody-elses-notes.txt" in str(refusal), str(refusal)
        else:
            raise AssertionError("a directory this tool does not own was emptied")
        assert (out / "somebody-elses-notes.txt").is_file()

    try:
        tenkz_ctan.clear_destination(ROOT)
    except SystemExit as refusal:
        assert "is not an output directory" in str(refusal), str(refusal)
    else:
        raise AssertionError("the repository was accepted as an output directory")

    # `tex/` holds a directory called `tenkz`, and it is the package's own
    # sources. Recognizing artifacts by name cannot be the only guard.
    try:
        tenkz_ctan.clear_destination(ROOT / "tex")
    except SystemExit as refusal:
        assert "outside build/" in str(refusal), str(refusal)
    else:
        raise AssertionError("the source directory was accepted as an output directory")
    assert (ROOT / "tex/tenkz/tenkz.sty").is_file()


def test_a_material_name_pointed_at_the_wrong_file_is_reported() -> None:
    manifest = tenkz_ctan.read_manifest()
    swapped = {
        "material": dict(
            manifest["material"],
            **{
                "LICENSE": manifest["material"]["CHANGES.md"],
                "CHANGES.md": manifest["material"]["LICENSE"],
            },
        )
    }
    report = tenkz_ctan.check_material(swapped)
    assert any("staged as LICENSE" in reason for reason in report.failures), report.failures


def test_material_from_outside_the_repository_is_refused() -> None:
    closure = tenkz_ctan.walk_closure()
    for value in ("/etc/hosts", "../outside-the-tree"):
        try:
            tenkz_ctan.staged_content({"material": {"LICENSE": value}}, closure)
        except SystemExit as refusal:
            assert "outside the" in str(refusal), str(refusal)
        else:
            raise AssertionError(f"{value} was staged")


def test_the_write_path_refuses_incomplete_material() -> None:
    manifest = tenkz_ctan.read_manifest()
    tenkz_ctan.require_complete_material(manifest)
    thinned = {"material": {k: v for k, v in manifest["material"].items() if k != "LICENSE"}}
    try:
        tenkz_ctan.require_complete_material(thinned)
    except SystemExit as refusal:
        assert "LICENSE" in str(refusal), str(refusal)
    else:
        raise AssertionError("an archive without a licence was allowed")


def test_the_clean_install_failure_paths_report_what_went_wrong() -> None:
    """The two branches no engine reaches on a healthy tree."""

    class Bounced:
        returncode = 3
        stdout = "! LaTeX Error: File `tenkz.sty' not found.\n"
        stderr = "the engine's own complaint\n"

    with tempfile.TemporaryDirectory() as directory:
        archive, _, _ = tenkz_ctan.build(Path(directory) / "out")
        engine = tenkz_ctan.shutil.which
        runner = tenkz_ctan.subprocess.run
        try:
            tenkz_ctan.shutil.which = lambda _name: "/somewhere/xelatex"
            tenkz_ctan.subprocess.run = lambda *a, **k: Bounced()
            failed = tenkz_ctan.check_smoke(archive, required=True)

            def expire(*_args, **_kwargs):
                raise subprocess.TimeoutExpired(cmd="xelatex", timeout=120)

            tenkz_ctan.subprocess.run = expire
            timed_out = tenkz_ctan.check_smoke(archive, required=True)
        finally:
            tenkz_ctan.shutil.which = engine
            tenkz_ctan.subprocess.run = runner
    assert any("exit 3" in reason for reason in failed.failures), failed.failures
    assert any(
        "the engine's own complaint" in reason for reason in failed.failures
    ), failed.failures
    assert any("120 seconds" in reason for reason in timed_out.failures), timed_out.failures


def test_the_release_report_survives_an_absent_artifact() -> None:
    """It is printed after the findings, so it must not replace them."""

    release = tenkz_ctan.read_release()
    root = tenkz_ctan.ROOT
    try:
        with tempfile.TemporaryDirectory() as directory:
            tenkz_ctan.ROOT = Path(directory)
            rows = tenkz_ctan.release_sync(release)
    finally:
        tenkz_ctan.ROOT = root
    assert [artifact for artifact, _ in rows] == [
        "tex/tenkz/tenkz.sty",
        "docs/tenkz/manual2.tex",
        "docs/tenkz/CHANGES.md",
        "docs/tenkz/TNLOG.md",
    ], rows
    assert dict(rows)["docs/tenkz/CHANGES.md"] == "absent", rows


def test_check_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "check"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
