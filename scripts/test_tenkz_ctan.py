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
import zipfile
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


def test_a_load_spelled_as_text_is_not_a_load() -> None:
    """`\\\\usepackage` in a macro body is the control symbol and then
    ordinary characters. Recording it would refuse a release over a
    definition, so the closure blanks the pairs as the arXiv readings do."""

    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        (source / "tenkz.sty").write_text(
            STAGE_CONTRACT + "\\def\\showload{\\\\usepackage{tikz-cd}}\n",
            encoding="utf-8",
        )
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
    assert closure.packages == [], closure.packages
    assert not tenkz_ctan.check_dependencies(closure, _ownership([], [], [])).failures


def test_closure_reads_the_unbraced_input() -> None:
    """Plain TeX's `\\input` takes a file name with no braces, reading to the
    next space. A walk that read only the braced form would let a stage module
    reach an upload without reaching the pin, and the load it brought with it
    would go unread."""

    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        (source / "tenkz.sty").write_text(
            STAGE_CONTRACT + "\\input tenkz-stage.code.tex\n", encoding="utf-8"
        )
        (source / "tenkz-stage.code.tex").write_text(
            STAGE_CONTRACT + "\\usepackage{tikz-cd}\n", encoding="utf-8"
        )
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
        assert closure.files == ["tenkz.sty", "tenkz-stage.code.tex"], closure.files
        assert closure.packages == ["tikz-cd"], closure.packages
        # Web2C's quoted form, which may follow the control word with no
        # space, and expl3's own file input.
        for spelling in ('\\input"tenkz-stage.code.tex"',
                         '\\input {"tenkz-stage.code.tex"}',
                         '\\file_input:n {tenkz-stage.code.tex}'):
            (source / "tenkz.sty").write_text(
                STAGE_CONTRACT + spelling + "\n", encoding="utf-8"
            )
            quoted = tenkz_ctan.walk_closure(source, "tenkz.sty")
            assert quoted.files == ["tenkz.sty", "tenkz-stage.code.tex"], spelling


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
    """The write path stops on an unwritable name; the report names it and
    keeps going, and both readings come from the one check."""

    closure = tenkz_ctan.walk_closure()
    for material, fragment in (
        ({"tenkz.sty": "LICENSE"}, "runtime name"),
        ({"../outside.md": "LICENSE"}, "will not be written"),
        ({"README.md": "LICENSE", "readme.md": "LICENSE"}, "differ only in case"),
    ):
        manifest = {"material": material}
        content = tenkz_ctan.staged_content(manifest, closure)
        report = tenkz_ctan.check_names(content, manifest, closure)
        assert report.failures, material
        try:
            tenkz_ctan.require_writable_names(manifest, closure, content)
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
    release = tenkz_ctan.Release(version="0.7", date="2026-07-22")
    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        subject = room / "tenkz.sty"
        subject.write_text("% one\n", encoding="utf-8")
        previous = os.umask(0o077)
        try:
            tree = tenkz_ctan.stage(
                room / "out", release, 1000000, {"tenkz.sty": subject}
            )
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
    release = tenkz_ctan.read_release()
    with tempfile.TemporaryDirectory() as directory:
        out = Path(directory) / "out"
        out.mkdir()
        (out / PACKAGE_DIR).mkdir()
        (out / f"{release.archive_stem}.zip").write_text("old\n", encoding="utf-8")
        tenkz_ctan.clear_destination(out, release)
        assert list(out.iterdir()) == []

        (out / "somebody-elses-notes.txt").write_text("keep me\n", encoding="utf-8")
        try:
            tenkz_ctan.clear_destination(out, release)
        except SystemExit as refusal:
            assert "somebody-elses-notes.txt" in str(refusal), str(refusal)
        else:
            raise AssertionError("a directory this tool does not own was emptied")
        assert (out / "somebody-elses-notes.txt").is_file()

        # An archive of another release, and a plain file wearing the staged
        # tree's name: both are somebody else's, whatever they are called.
        (out / "somebody-elses-notes.txt").unlink()
        (out / "tenkz-0.1.zip").write_text("an older release\n", encoding="utf-8")
        try:
            tenkz_ctan.clear_destination(out, release)
        except SystemExit as refusal:
            assert "tenkz-0.1.zip" in str(refusal), str(refusal)
        else:
            raise AssertionError("an archive this run does not write was removed")
        (out / "tenkz-0.1.zip").unlink()
        (out / PACKAGE_DIR).write_text("not the staged tree\n", encoding="utf-8")
        try:
            tenkz_ctan.clear_destination(out, release)
        except SystemExit as refusal:
            assert PACKAGE_DIR in str(refusal), str(refusal)
        else:
            raise AssertionError("a file wearing the tree's name was removed")

    try:
        tenkz_ctan.clear_destination(ROOT, release)
    except SystemExit as refusal:
        assert "is not an output directory" in str(refusal), str(refusal)
    else:
        raise AssertionError("the repository was accepted as an output directory")

    # `tex/` holds a directory called `tenkz`, and it is the package's own
    # sources. Recognizing artifacts by name cannot be the only guard.
    try:
        tenkz_ctan.clear_destination(ROOT / "tex", release)
    except SystemExit as refusal:
        assert "outside build/" in str(refusal), str(refusal)
    else:
        raise AssertionError("the source directory was accepted as an output directory")
    assert (ROOT / "tex/tenkz/tenkz.sty").is_file()


def _without_table(manifest: str, table: str) -> str:
    """The manifest with one table and its sub-tables taken out."""

    kept: list[str] = []
    dropping = False
    for line in manifest.splitlines(keepends=True):
        header = line.strip()
        if header.startswith("["):
            dropping = header == f"[{table}]" or header.startswith(f"[{table}.")
        if not dropping:
            kept.append(line)
    return "".join(kept)


def test_a_manifest_without_its_tables_is_named_rather_than_raised() -> None:
    """A parseable manifest that is not a staging manifest says which table it
    is missing, instead of failing as a key error inside whichever check
    reached it first."""

    original = (ROOT / "docs/tenkz/ctan/MANIFEST.toml").read_text(encoding="utf-8")
    for table, fragment in (
        ("runtime", "no [runtime] table"),
        ("material", "no [material] table"),
        ("source_tree", "no [source_tree] table"),
    ):
        with tempfile.TemporaryDirectory() as directory:
            broken = Path(directory) / "MANIFEST.toml"
            broken.write_text(_without_table(original, table), encoding="utf-8")
            completed = subprocess.run(
                [sys.executable, str(ROOT / "scripts/tenkz_ctan.py"), "check"],
                capture_output=True,
                text=True,
                env={**os.environ, "TENKZ_CTAN_MANIFEST": str(broken)},
            )
        assert completed.returncode != 0, table
        assert fragment in completed.stdout + completed.stderr, (
            table,
            completed.stdout,
            completed.stderr,
        )


def test_a_record_stating_its_version_twice_fails() -> None:
    """A release edit that leaves the previous line standing beside the new one
    has stated two versions, and a citation record states one."""

    manifest = tenkz_ctan.read_manifest()
    release = tenkz_ctan.read_release()
    citation = ROOT / manifest["material"]["CITATION.cff"]
    original = citation.read_text(encoding="utf-8")
    stale = original.replace(
        f'version: "{release.version}"',
        f'version: "0.1"\nversion: "{release.version}"',
        1,
    )
    try:
        citation.write_text(stale, encoding="utf-8")
        failures = tenkz_ctan.check_version(release, manifest).failures
    finally:
        citation.write_text(original, encoding="utf-8")
    assert any("once" in reason for reason in failures), failures


def test_a_commented_version_does_not_answer_for_the_record() -> None:
    """A BibTeX comment holding the right year beside a live field holding the
    wrong one is a stale record, and it reads as one."""

    manifest = tenkz_ctan.read_manifest()
    release = tenkz_ctan.read_release()
    bibliography = ROOT / manifest["material"]["tenkz.bib"]
    original = bibliography.read_text(encoding="utf-8")
    year = release.date.split("-")[0]
    stale = original.replace(f"year         = {{{year}}}", "year         = {1999}")
    stale = f"% year = {{{year}}}, version {release.version}\n" + stale
    try:
        bibliography.write_text(stale, encoding="utf-8")
        failures = tenkz_ctan.check_version(release, manifest).failures
    finally:
        bibliography.write_text(original, encoding="utf-8")
    assert any(f"year {year}" in reason for reason in failures), failures


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
    assert any(
        "LICENSE is staged from" in reason for reason in report.failures
    ), report.failures
    assert any(
        "CHANGES.md is staged from" in reason for reason in report.failures
    ), report.failures

    # The three recognized by content rather than by canonical path: the
    # citation record staged from the BibTeX record and back.
    crossed = {
        "material": dict(
            manifest["material"],
            **{
                "CITATION.cff": manifest["material"]["tenkz.bib"],
                "tenkz.bib": manifest["material"]["CITATION.cff"],
            },
        )
    }
    report = tenkz_ctan.check_material(crossed)
    assert any(
        "staged as CITATION.cff does not read as one" in reason
        for reason in report.failures
    ), report.failures


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
    tenkz_ctan.require_sound_material(manifest)
    thinned = {"material": {k: v for k, v in manifest["material"].items() if k != "LICENSE"}}
    try:
        tenkz_ctan.require_sound_material(thinned)
    except SystemExit as refusal:
        assert "LICENSE" in str(refusal), str(refusal)
    else:
        raise AssertionError("an archive without a licence was allowed")

    # Both writing commands, not only the reporting one.
    good = (ROOT / "docs/tenkz/ctan/MANIFEST.toml").read_text(encoding="utf-8")
    without = good.replace('"LICENSE" = "LICENSE"\n', "")
    assert without != good
    with tempfile.TemporaryDirectory() as directory:
        broken = Path(directory) / "MANIFEST.toml"
        broken.write_text(without, encoding="utf-8")
        for command in ("stage", "archive"):
            finished = subprocess.run(
                [sys.executable, str(SCRIPT), command, "--out", f"{directory}/out"],
                capture_output=True,
                text=True,
                env={**os.environ, "TENKZ_CTAN_MANIFEST": str(broken)},
            )
            assert finished.returncode != 0, (command, finished.stdout)
            assert "LICENSE" in finished.stderr, (command, finished.stderr)


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


def test_the_manifest_declares_the_schema_and_the_package() -> None:
    good = (ROOT / "docs/tenkz/ctan/MANIFEST.toml").read_text(encoding="utf-8")
    for edit, fragment in (
        (("schema = 1", "schema = 999"), "this tool reads schema 1"),
        (('package = "tenkz"', 'package = "not-tenkz"'), "not 'tenkz'"),
    ):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "MANIFEST.toml"
            manifest.write_text(good.replace(*edit), encoding="utf-8")
            finished = subprocess.run(
                [sys.executable, str(SCRIPT), "check"],
                capture_output=True,
                text=True,
                env={**os.environ, "TENKZ_CTAN_MANIFEST": str(manifest)},
            )
        assert finished.returncode != 0, finished.stdout
        assert "Traceback" not in finished.stderr, finished.stderr
        assert fragment in finished.stderr, finished.stderr


def test_a_runtime_source_outside_the_repository_is_refused() -> None:
    try:
        tenkz_ctan.inside_repository("tenkz.sty", Path("/etc/hosts"))
    except SystemExit as refusal:
        assert "outside the repository" in str(refusal), str(refusal)
    else:
        raise AssertionError("a source outside the tree was staged")
    assert tenkz_ctan.inside_repository(
        "tenkz.sty", ROOT / "tex/tenkz/tenkz.sty"
    ) == (ROOT / "tex/tenkz/tenkz.sty").resolve()


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


def _ownership(placement: list[str], ink: list[str], unconsumed: list[str]) -> dict:
    """A manifest holding one library classification and nothing else."""

    return {
        "runtime": {
            "requires": {
                "packages": ["tikz"],
                "libraries": sorted(placement + ink + unconsumed),
                "ownership": {
                    "placement": placement,
                    "ink": ink,
                    "unconsumed": unconsumed,
                },
            }
        }
    }


def test_a_loaded_library_without_a_consumer_class_is_caught() -> None:
    """A list of library names is not a dependency report. A library that
    entered or left the load list without being traced to the code that reads
    it fails here, which is what stops the report from going stale."""

    closure = tenkz_ctan.Closure(libraries=["calc", "hobby"], packages=["tikz"])
    missing = tenkz_ctan.check_dependencies(
        closure, _ownership(["calc"], [], [])
    )
    assert any("loads" in reason for reason in missing.failures), missing.failures
    invented = tenkz_ctan.check_dependencies(
        closure, _ownership(["calc", "hobby"], ["spath3"], [])
    )
    assert invented.failures, "a class naming a library nothing loads passed"
    twice = tenkz_ctan.check_dependencies(
        closure, _ownership(["calc", "hobby"], ["hobby"], [])
    )
    assert any(
        "more than one consumer class" in reason for reason in twice.failures
    ), twice.failures
    sound = tenkz_ctan.check_dependencies(closure, _ownership(["calc"], ["hobby"], []))
    assert not sound.failures, sound.failures


def test_a_manifest_with_no_classification_at_all_is_named() -> None:
    manifest = {"runtime": {"requires": {"packages": ["tikz"], "libraries": []}}}
    report = tenkz_ctan.check_dependencies(tenkz_ctan.Closure(), manifest)
    assert any("ownership" in reason for reason in report.failures), report.failures


def test_a_class_left_out_or_stated_twice_is_caught() -> None:
    """A class omitted reads as one nobody considered, and a library named
    twice inside one class reads as more consumers than were traced. Neither
    is caught by the cover comparison, which goes through a set."""

    closure = tenkz_ctan.Closure(libraries=["calc"], packages=["tikz"])
    dropped = _ownership(["calc"], [], [])
    del dropped["runtime"]["requires"]["ownership"]["unconsumed"]
    missing = tenkz_ctan.check_dependencies(closure, dropped)
    assert any("unconsumed" in reason for reason in missing.failures), missing.failures
    repeated = tenkz_ctan.check_dependencies(closure, _ownership(["calc", "calc"], [], []))
    assert any(
        "more than once" in reason for reason in repeated.failures
    ), repeated.failures


def test_a_package_load_is_read_in_both_of_its_spellings() -> None:
    """A `.sty` writes `\\RequirePackage`, but nothing stops a staged runtime
    file from writing `\\usepackage`, and the two load the same package. A walk
    that read only the first would report a retired front end absent while it
    was being loaded."""

    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        for spelling in ("usepackage", "RequirePackage", "RequirePackageWithOptions"):
            (source / "tenkz.sty").write_text(
                STAGE_CONTRACT + f"\\{spelling}{{tikz-cd}}\n", encoding="utf-8"
            )
            closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
            assert closure.packages == ["tikz-cd"], (spelling, closure.packages)
            report = tenkz_ctan.check_dependencies(closure, _ownership([], [], []))
            assert any("tikz-cd" in r for r in report.failures), (spelling, report.failures)


def test_a_retired_front_end_vendored_as_a_file_is_caught() -> None:
    """A retired front end can arrive as a package load, a library load, or a
    file the entry point inputs. The third reaches the closure only as a file
    name, so the reading compares stems as well."""

    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        (source / "tenkz.sty").write_text(
            STAGE_CONTRACT + "\\input{tikz-cd.sty}\n", encoding="utf-8"
        )
        (source / "tikz-cd.sty").write_text(STAGE_CONTRACT, encoding="utf-8")
        closure = tenkz_ctan.walk_closure(source, "tenkz.sty")
    assert closure.files == ["tenkz.sty", "tikz-cd.sty"], closure.files
    report = tenkz_ctan.check_dependencies(closure, _ownership([], [], []))
    assert any("tikz-cd" in reason for reason in report.failures), report.failures
    # A TikZ library vendored as a file goes by its conventional file name, so
    # the reading strips the prefix and the suffix a load carries.
    assert tenkz_ctan.load_names("tikzlibrarytikzcd.code.tex") >= {"tikzcd"}
    assert tenkz_ctan.load_names("tenkz-core.code.tex") >= {"tenkz-core"}
    # A load may carry a directory, and the basename is what the prefix and
    # the suffix are stripped from.
    assert tenkz_ctan.load_names("vendor/tikzlibrarytikzcd.code.tex") >= {"tikzcd"}
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "tex"
        source.mkdir()
        (source / "tenkz.sty").write_text(
            STAGE_CONTRACT + "\\input{tikzlibrarytikzcd.code.tex}\n", encoding="utf-8"
        )
        (source / "tikzlibrarytikzcd.code.tex").write_text(STAGE_CONTRACT, encoding="utf-8")
        vendored = tenkz_ctan.walk_closure(source, "tenkz.sty")
    library = tenkz_ctan.check_dependencies(vendored, _ownership([], [], []))
    assert any("tikzcd" in reason for reason in library.failures), library.failures


def test_a_retired_front_end_load_fails_the_dependency_check() -> None:
    """The removed front ends each brought a load. The walk blanks comments
    before it reads one, so a retired name in the closure is a surviving load
    rather than the sentence in `tenkz.sty` that mentions tikz-cd."""

    closure = tenkz_ctan.Closure(packages=["tikz", "tikz-cd"], libraries=[])
    report = tenkz_ctan.check_dependencies(closure, _ownership([], [], []))
    assert any("tikz-cd" in reason for reason in report.failures), report.failures
    walked = tenkz_ctan.walk_closure()
    loaded = set(walked.packages) | set(walked.libraries)
    assert not loaded & set(tenkz_ctan.RETIRED_DEPENDENCIES), sorted(loaded)


def test_the_real_classification_covers_the_real_load_list() -> None:
    report = tenkz_ctan.check_dependencies(
        tenkz_ctan.walk_closure(), tenkz_ctan.read_manifest()
    )
    assert not report.failures, report.failures


def _loaded(*names: str) -> "tenkz_ctan.Closure":
    """A closure that loads exactly the named files, for the arXiv reading."""

    return tenkz_ctan.Closure(files=list(names))


def test_a_tree_arxiv_would_have_to_build_or_shell_out_for_fails() -> None:
    """The submission reading of the same files: flat, already the runtime,
    naming no path on the machine that wrote it, calling no shell."""

    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / PACKAGE_DIR
        (tree / "nested").mkdir(parents=True)
        (tree / "tenkz.sty").write_text("% a runtime file\n", encoding="utf-8")
        # Upper case is the same docstrip run: a file system that preserves
        # case hands the suffix back as it was typed.
        (tree / "tenkz.INS").write_text("% a docstrip run\n", encoding="utf-8")
        (tree / "loud.sty").write_text("\\immediate \\write 18{rm -rf /}\n", encoding="utf-8")
        (tree / "elsewhere.sty").write_text(
            "\\input{/Users/somebody/tenkz-core.code.tex}\n", encoding="utf-8"
        )
        report = tenkz_ctan.check_arxiv(
            tree, _loaded("tenkz.sty", "loud.sty", "elsewhere.sty")
        )
    findings = " ".join(report.failures)
    assert "nested" in findings, report.failures
    assert "tenkz.INS" in findings, report.failures
    # The spaced spelling opens the same stream as the compact one, and TeX
    # reads the number either way.
    assert "write 18" in findings, report.failures
    assert "absolute path" in findings, report.failures


def test_every_spelling_of_stream_eighteen_is_the_shell_escape_stream() -> None:
    """TeX scans the stream as an integer, so leading zeros and the `"` and
    `'` prefixes for hexadecimal and octal all reach stream 18. The constant is
    evaluated rather than matched against one way of writing it."""

    for call in (r"\write18{x}", r"\write 18{x}", r"\immediate \write 18{x}",
                 r"\write018{x}", '\\write"12{x}', r"\write'22{x}",
                 r"\write+18{x}", r"\write--18{x}", r"\ShellEscape{x}"):
        assert tenkz_ctan.shell_escape_call(call), call
    # The gate fails closed, so a stream the reading cannot evaluate is a
    # finding on its own: a character constant, an integer expression, a
    # stream the file never allocated.
    for unread in (r"\write`^^R{x}", r"\write\numexpr18\relax{x}",
                   r"\write \myout{x}"):
        assert tenkz_ctan.shell_escape_call(unread), unread
    # A stream the same file allocated is a file stream by construction, which
    # is how the package writes its event stream.
    allocated = "\\newwrite\\tenkz@log\n\\immediate\\write\\tenkz@log{#1}\n"
    assert not tenkz_ctan.shell_escape_call(allocated), allocated
    assert tenkz_ctan.shell_escape_call(
        "\\immediate\\write\\tenkz@log{#1}\n"
    ), "a stream nothing allocated passed"
    # A control word that merely begins with the primitive's letters is a name,
    # not the primitive: `@` is a letter in a package and `_` and `:` are
    # letters under `\ExplSyntaxOn`, so refusing these would block a release
    # over a spelling.
    for name in (r"\write@event{x}", r"\write:nn {x}{y}", r"\write_stuff{x}"):
        assert not tenkz_ctan.shell_escape_call(name), name
    # The one assembled spelling that is still readable from the text.
    assert tenkz_ctan.shell_escape_call(r"\csname write\endcsname18{x}")
    # The named ways to reach a shell that are not a write at all. A file
    # under `\ExplSyntaxOn` would use the expl3 interface in preference to
    # either primitive.
    # Web2C runs a file name opening with a pipe, which names no stream and
    # no API.
    # The bar is a command only in a file name, so the reading is scoped to
    # one: two characters in a macro body or in prose execute nothing.
    # The stream operand is a control sequence or a number, and the equals
    # sign is optional: that is TeX's syntax, not a house spelling.
    for piped in ('\\openin\\stream="|uname -a"', r"\input{|cmd}", r'\input "|cmd"',
                  '\\openout1="|cmd"', '\\openin1="|cmd"'):
        assert tenkz_ctan.shell_escape_call(piped), piped
    # Only the primitives that open a file are read: `\\write` and `\\read` take
    # a stream already open and a token list that is data, so a token list
    # beginning with a bar is text.
    for plain in ('\\openin\\stream="plain.tex"', r'\def\separator{"|}',
                  'the sequence "| in prose',
                  "\\newwrite\\out\n\\write\\out{|literal}\n"):
        assert not tenkz_ctan.shell_escape_call(plain), plain
    # A name the same file redefines is no longer the stream it was allocated
    # as, so the allocation ground does not carry it.
    assert not tenkz_ctan.shell_escape_call(
        "\\newwrite\\out\n\\immediate\\write\\out{x}\n"
    )
    for overwritten in ("\\newwrite\\out\n\\def\\out{18}\n\\write\\out{x}\n",
                        "\\newwrite\\out\n\\chardef\\out=18\n\\write\\out{x}\n",
                        "\\newwrite\\out\n\\cs_gset:Npn \\out {18}\n\\write\\out{x}\n"):
        assert tenkz_ctan.shell_escape_call(overwritten), overwritten
    for named in (r"\sys_shell_now:n {ls}", r"\sys_shell_shipout:x {ls}",
                  r"\sys_get_shell:nnN {x}{y}\z", r"\ior_shell_open:Nn \x {ls}",
                  r"\iow_shell_open:Nn \x {ls}", r"\DelayedShellEscape{ls}"):
        assert tenkz_ctan.shell_escape_call(named), named
    # Asking whether the engine has a shell runs nothing. Reading these as
    # calls would refuse a file for putting the question.
    for asks in (r"\tex_shellescape:D", r"\sys_if_shell:TF {y}{n}",
                 r"\sys_shell_open:Nn \x {ls}"):
        assert not tenkz_ctan.shell_escape_call(asks), asks
    # A longer control word that merely starts with an executor's letters is a
    # different macro, on the same boundary rule the write gate uses.
    for longer in (r"\ShellEscape@status", r"\ShellEscaped{x}",
                   r"\sys_shell_now:n_aux {x}"):
        assert not tenkz_ctan.shell_escape_call(longer), longer
    # A backslash preceded by a backslash does not start a control sequence:
    # `\\write18` is the control symbol and then ordinary characters, and a
    # gate that read it as the primitive would refuse a package for
    # typesetting the spelling.
    # It is the parity of the run that decides, not whether one backslash
    # precedes: `\\\write18` is that control symbol and then the primitive.
    for typeset in (r"\\write18{x}", r"\\ShellEscape{x}", r"\\\\write18{x}"):
        assert not tenkz_ctan.shell_escape_call(typeset), typeset
    for odd in (r"\\\write18{x}", r"\\\ShellEscape{x}"):
        assert tenkz_ctan.shell_escape_call(odd), odd
    # Numbers that are not 18 in the base their prefix names, an odd run of
    # minus signs, and a control sequence that merely starts with the same
    # letters.
    for quiet in (r"\write17{x}", r"\write180{x}", '\\write"18{x}',
                  r"\write-18{x}", r"\write+-18{x}", r"\writer{x}",
                  r"\iow_now:Nn \g_out {x}"):
        assert not tenkz_ctan.shell_escape_call(quiet), quiet


def test_a_closure_file_the_archive_forgot_stays_in_the_reading() -> None:
    """`carried` comes from the load graph and is not narrowed to what the
    archive staged. A file the archive omitted has to stay in the reading, or
    an installed copy answering for it would resolve outside the room and never
    be looked at."""

    (ROOT / "build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as directory:
        room = Path(directory)
        # The production reading, not a local rebuild of it: narrowing this
        # again is what the test exists to catch.
        carried = tenkz_ctan.carried_runtime()
        forgotten = "tenkz-string.code.tex"
        assert forgotten in carried, sorted(carried)
        # The engine answered it from an installation instead of the flat.
        installed = "/usr/local/texlive/tex/latex/tenkz/" + forgotten
        runtime = [path for path in [installed] if Path(path).name in carried]
        assert runtime == [installed], runtime
        assert tenkz_ctan.foreign_runtime_files(runtime, room, room.resolve())
        # The check's own driver files are not on the load graph, so they never
        # stand in for a runtime file the run never opened.
        assert "tenkz-offline-flat.tex" not in carried


def test_a_loaded_source_is_read_whatever_it_is_called() -> None:
    """The scan follows the load graph rather than a list of suffixes, so a
    runtime file added later as a class or a configuration is read because it
    is loaded, and reader-facing material is not read at all."""

    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / PACKAGE_DIR
        tree.mkdir(parents=True)
        (tree / "tenkz.cfg").write_text("\\write18{uname -a}\n", encoding="utf-8")
        (tree / "CHANGES.md").write_text(
            "The package calls no \\write18 and loads no /absolute path.\n",
            encoding="utf-8",
        )
        scanned = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.cfg"))
        unscanned = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
    assert any("write18" in reason for reason in scanned.failures), scanned.failures
    assert not unscanned.failures, unscanned.failures


def test_an_unbraced_absolute_input_is_an_absolute_path() -> None:
    """Plain TeX's `\\input` takes a filename with no braces, reading to the
    next space. A gate that only read the braced spelling would pass a staged
    file that loads from the machine it was written on."""

    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / PACKAGE_DIR
        tree.mkdir(parents=True)
        (tree / "tenkz.sty").write_text(
            "\\input /Users/somebody/tenkz-core.code.tex\n", encoding="utf-8"
        )
        unbraced = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
        # A starred form puts its star between the command and its arguments,
        # and LaTeX's star test skips a space before it. A conditional loader
        # is a loader: a runtime whose behaviour depends on a machine-local
        # file is not submittable even when the file's absence is handled.
        for load in (r"\includegraphics*{/Users/somebody/figure.pdf}",
                     r"\includegraphics *{/Users/somebody/figure.pdf}",
                     r"\InputIfFileExists{/Users/somebody/local.cfg}{}{}",
                     r"\IfFileExists{/Users/somebody/local.cfg}{}{}",
                     r"\file_input:n { /Users/somebody/local.tex }",
                     r"\openin\src=/Users/somebody/data.tex",
                     r"\openin1 /Users/somebody/data.tex",
                     r"\openout\log=/Users/somebody/run.log",
                     r"\graphicspath{{/Users/somebody/figures/}}",
                     # Every directory in the list, not only the first.
                     r"\graphicspath{{figures/}{/Users/somebody/more/}}",
                     # A path holding a space is written quoted, braced or not.
                     '\\input{"/Users/somebody/My Documents/f.tex"}'):
            (tree / "tenkz.sty").write_text(load + "\n", encoding="utf-8")
            found = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
            assert any("absolute path" in r for r in found.failures), (load, found.failures)
        (tree / "tenkz.sty").write_text("\\input tenkz-core.code.tex\n", encoding="utf-8")
        relative = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
    assert any("absolute path" in reason for reason in unbraced.failures), unbraced.failures
    assert not relative.failures, relative.failures


def test_an_archive_that_does_not_open_is_a_report_line() -> None:
    """The tool's contract is that every finding is a printed line. An archive
    that is not one, or that does not hold the directory an upload is judged
    on, has to arrive as a failed check rather than as a traceback."""

    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        torn = room / "torn.zip"
        torn.write_bytes(b"not a zip file at all")
        engine = tenkz_ctan.shutil.which
        try:
            tenkz_ctan.shutil.which = lambda _name: "/somewhere/xelatex"
            report = tenkz_ctan.check_offline(torn, required=True)
        finally:
            tenkz_ctan.shutil.which = engine
    assert report.status == "FAIL", report
    assert any("does not open" in reason for reason in report.failures), report.failures


def test_a_temporary_directory_inside_the_repository_is_not_a_leak() -> None:
    """`tempfile` puts the room wherever `TMPDIR` says, and a runner that puts
    it inside the workspace would otherwise make every file the flat archive
    itself answered look like one the repository answered."""

    (ROOT / "build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as directory:
        room = Path(directory)
        (room / "tenkz.sty").write_text("% the staged runtime\n", encoding="utf-8")
        assert room.resolve().is_relative_to(ROOT), room
        # The reading the offline check performs, on a room the repository
        # contains. Both halves have to survive it: the runtime one, which asks
        # where a tenkz file resolved, and the repository one, which asks
        # whether anything at all came from the checkout.
        assert not tenkz_ctan.foreign_runtime_files(
            ["./tenkz.sty", "tenkz.sty"], room, room.resolve()
        )
        assert not tenkz_ctan.repository_inputs(
            ["./tenkz.sty", "tenkz.sty"], room, room.resolve()
        )
        # A file the repository really did answer is still found, so the room
        # exclusion narrows the reading rather than emptying it.
        assert tenkz_ctan.repository_inputs(
            [str(ROOT / "tex/tenkz/tenkz.sty")], room, room.resolve()
        ) == [str(ROOT / "tex/tenkz/tenkz.sty")]


def test_a_commented_shell_call_is_not_a_shell_call() -> None:
    """Comments are blanked before the reading, as everywhere else here: a
    sentence about `\\write18` is prose, and refusing it would be refusing the
    file that documents why the package does not call it."""

    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / PACKAGE_DIR
        tree.mkdir(parents=True)
        # A comment, and text that typesets the spellings rather than using
        # them: `\\\\input` is the control symbol and then ordinary characters.
        (tree / "tenkz.sty").write_text(
            "% tenkz never calls \\write18, and never loads {/absolute}.\n"
            "The spelling \\\\input{/absolute/path} is text, not a load.\n",
            encoding="utf-8",
        )
        report = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
    assert not report.failures, report.failures


def test_an_interposed_tool_records_its_own_call_and_fails() -> None:
    """The offline claim is read from whether an installer ran, so the shims
    have to record. A shim that silently succeeded would let a run repair an
    incomplete environment and still report that nothing was fetched."""

    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        shims = room / "shims"
        tenkz_ctan.write_shims(shims)
        tripwire = room / "reached-for.txt"
        assert sorted(path.name for path in shims.iterdir()) == sorted(
            tenkz_ctan.INTERPOSED_TOOLS
        )
        called = subprocess.run(
            [str(shims / "tlmgr"), "install", "tenkz"],
            capture_output=True,
            text=True,
            env={**os.environ, "TENKZ_OFFLINE_TRIPWIRE": str(tripwire)},
        )
        assert called.returncode != 0, called.stdout
        assert tripwire.is_file(), "the shim ran and recorded nothing"
        assert "tlmgr" in tripwire.read_text(encoding="utf-8")


def test_the_offline_environment_inherits_nothing_that_could_answer() -> None:
    """A user tree, a repository on the search path, or an on-demand font
    builder would each let a run pass while proving less than it claims."""

    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        environment = tenkz_ctan.offline_environment(
            room / "submission", room / "shims", room / "tripwire", room / "home"
        )
    assert environment["TEXINPUTS"] == ".:", environment["TEXINPUTS"]
    assert str(ROOT) not in environment["TEXINPUTS"]
    assert environment["PATH"].startswith(str(room / "shims"))
    for tree in ("TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG", "HOME"):
        assert environment[tree].startswith(str(room / "home")), tree
    for generator in ("MKTEXTFM", "MKTEXPK", "MKTEXMF", "MKTEXFMT"):
        assert environment[generator] == "0", generator


def test_the_offline_cases_are_the_picture_classes_and_still_say_so() -> None:
    """The corpus owns the cases, so this reads them rather than copying
    them: a case that moved, or that stopped drawing the class it was chosen
    for, is caught without an engine."""

    classes = {case.picture_class for case in tenkz_ctan.OFFLINE_CASES}
    assert classes == {
        "flat", "plane", "circle", "string/crossing", "enclosure", "equation"
    }, sorted(classes)
    assert any(
        case.source.startswith("tests/tenkz/kernel/")
        for case in tenkz_ctan.OFFLINE_CASES
    ), "no self-contained kernel probe is compiled"
    names = [case.name for case in tenkz_ctan.OFFLINE_CASES]
    assert len(set(names)) == len(names), names
    for case in tenkz_ctan.OFFLINE_CASES:
        source = ROOT / case.source
        assert source.is_file(), case.source
        assert case.declares in source.read_text(encoding="utf-8"), case.name


def test_the_offline_check_says_so_when_there_is_no_engine() -> None:
    engine = tenkz_ctan.shutil.which
    try:
        tenkz_ctan.shutil.which = lambda _name: None
        skipped = tenkz_ctan.check_offline(Path("unread.zip"), required=False)
        refused = tenkz_ctan.check_offline(Path("unread.zip"), required=True)
    finally:
        tenkz_ctan.shutil.which = engine
    assert skipped.status == "SKIP", skipped
    assert refused.failures, refused


def test_a_note_never_contradicts_the_finding_printed_beside_it() -> None:
    """A closing note states what the check found, so it is written only when
    the check held. A line claiming no retired load, printed above the line
    reporting one, is worse than no line at all."""

    closure = tenkz_ctan.Closure(packages=["tikz", "tikz-cd"], libraries=[])
    caught = tenkz_ctan.check_dependencies(closure, _ownership([], [], []))
    assert caught.failures, caught
    assert not caught.notes, caught.notes
    with tempfile.TemporaryDirectory() as directory:
        tree = Path(directory) / PACKAGE_DIR
        tree.mkdir(parents=True)
        (tree / "tenkz.sty").write_text("\\write18{uname -a}\n", encoding="utf-8")
        loud = tenkz_ctan.check_arxiv(tree, _loaded("tenkz.sty"))
    assert loud.failures, loud
    assert not loud.notes, loud.notes


def test_the_offline_check_reports_a_case_that_cannot_be_read() -> None:
    """The two findings that need no engine: a case source that has moved, and
    one that no longer spells the construct it was chosen for. Both are seeded
    here because a guard nobody has watched fail is not a guard."""

    engine = tenkz_ctan.shutil.which
    saved = tenkz_ctan.OFFLINE_CASES
    flat = next(case for case in saved if case.name == "flat")
    moved = tenkz_ctan.OfflineCase(
        flat.name, flat.picture_class, "tests/tenkz/rmp/gone.tex", False,
        flat.declares, flat.emits,
    )
    renamed = tenkz_ctan.OfflineCase(
        flat.name, flat.picture_class, flat.source, False,
        r"\begin{something-else}", flat.emits,
    )
    with tempfile.TemporaryDirectory() as directory:
        archive, _, _ = tenkz_ctan.build(Path(directory) / "out")
        try:
            tenkz_ctan.shutil.which = lambda _name: "/somewhere/xelatex"
            tenkz_ctan.OFFLINE_CASES = (moved,)
            gone = tenkz_ctan.check_offline(archive, required=True)
            tenkz_ctan.OFFLINE_CASES = (renamed,)
            drifted = tenkz_ctan.check_offline(archive, required=True)
        finally:
            tenkz_ctan.shutil.which = engine
            tenkz_ctan.OFFLINE_CASES = saved
    assert any("gone.tex is missing" in reason for reason in gone.failures), gone.failures
    assert any("no longer spells" in reason for reason in drifted.failures), drifted.failures


def test_the_offline_check_reports_an_archive_it_cannot_read() -> None:
    """Three shapes an archive can arrive in that are not an upload, each
    seeded and each required to be a report line rather than a traceback."""

    engine = tenkz_ctan.shutil.which
    with tempfile.TemporaryDirectory() as directory:
        room = Path(directory)
        (room / "torn.zip").write_bytes(b"not a zip file at all")
        real = ROOT / "docs/tenkz/ctan/MANIFEST.toml"
        with zipfile.ZipFile(room / "loose.zip", "w") as bundle:
            bundle.writestr("tenkz.sty", real.read_bytes())
        with zipfile.ZipFile(room / "nested.zip", "w") as bundle:
            bundle.writestr(f"{PACKAGE_DIR}/tenkz.sty", real.read_bytes())
            bundle.writestr(f"{PACKAGE_DIR}/runtime/", b"")
        with zipfile.ZipFile(room / "extra.zip", "w") as bundle:
            bundle.writestr(f"{PACKAGE_DIR}/tenkz.sty", real.read_bytes())
            bundle.writestr("READ-ME-FIRST.txt", b"a stray member\n")
        try:
            tenkz_ctan.shutil.which = lambda _name: "/somewhere/xelatex"
            reports = {
                name: tenkz_ctan.check_offline(room / f"{name}.zip", required=True)
                for name in ("torn", "loose", "nested", "extra")
            }
        finally:
            tenkz_ctan.shutil.which = engine
    assert any("does not open" in r for r in reports["torn"].failures), reports["torn"].failures
    assert any(
        "does not unpack into a single" in r for r in reports["loose"].failures
    ), reports["loose"].failures
    assert any(
        "is not a file" in r for r in reports["nested"].failures
    ), reports["nested"].failures
    assert any(
        "beside ['READ-ME-FIRST.txt']" in r for r in reports["extra"].failures
    ), reports["extra"].failures


def test_an_installer_that_fired_is_read_as_a_finding() -> None:
    """The shim half is pinned above. This is the reading that turns a shim
    that fired into a failed check, seeded by leaving the record a shim would
    have written."""

    engine = tenkz_ctan.shutil.which
    saved = tenkz_ctan.OFFLINE_CASES
    original = tenkz_ctan.write_shims

    def firing(shims: Path) -> None:
        original(shims)
        (shims.parent / "reached-for.txt").write_text("/shims/tlmgr\n", encoding="utf-8")

    with tempfile.TemporaryDirectory() as directory:
        archive, _, _ = tenkz_ctan.build(Path(directory) / "out")
        try:
            tenkz_ctan.shutil.which = lambda _name: "/somewhere/xelatex"
            tenkz_ctan.write_shims = firing
            # No case is compiled: the engine is a fiction here, and the
            # reading under test runs after the cases either way.
            tenkz_ctan.OFFLINE_CASES = ()
            report = tenkz_ctan.check_offline(archive, required=True)
        finally:
            tenkz_ctan.shutil.which = engine
            tenkz_ctan.write_shims = original
            tenkz_ctan.OFFLINE_CASES = saved
    assert any(
        "reached for an installer" in reason for reason in report.failures
    ), report.failures


def test_an_ownership_class_of_the_wrong_shape_is_named() -> None:
    """The two remaining shapes a classification can arrive in: a class nobody
    declared, and a class that is not a list of names."""

    closure = tenkz_ctan.Closure(libraries=["calc"], packages=["tikz"])
    invented = _ownership(["calc"], [], [])
    invented["runtime"]["requires"]["ownership"]["legacy"] = ["calc"]
    unknown = tenkz_ctan.check_dependencies(closure, invented)
    assert any("legacy" in reason for reason in unknown.failures), unknown.failures
    misshapen = _ownership(["calc"], [], [])
    misshapen["runtime"]["requires"]["ownership"]["placement"] = "calc"
    shape = tenkz_ctan.check_dependencies(closure, misshapen)
    assert any("not a list" in reason for reason in shape.failures), shape.failures


def test_check_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "check"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
