#!/usr/bin/env python3
"""The CTAN staging tree for tenkz, and the checks that keep it honest.

CTAN receives an archive, not a repository. This tool builds that archive
from the tree — the runtime files the entry point actually loads, plus the
reader-facing material an upload must carry — and then proves the properties
an upload is judged on, rather than asserting them.

What the tool refuses to guess:

  the runtime closure   The staged runtime is walked from
                        `tex/tenkz/tenkz.sty`, following `\\input` through the
                        stage modules and reading `\\RequirePackage` and
                        `\\usetikzlibrary` for what the archive does not carry.
                        A pinned copy in `docs/tenkz/ctan/MANIFEST.toml` fails
                        the check when the load graph moves, so a new stage
                        module cannot reach an upload unnoticed.

  the version           One declaration owns it, the `\\ProvidesPackage` line
                        of `tex/tenkz/tenkz.sty`. The archive name, the
                        README, and the citation records are checked against
                        that line; none of them may state a version of their
                        own. This tool never edits a version.

  the timestamps        Every staged file and every archive member is dated
                        from `SOURCE_DATE_EPOCH` when the environment sets it,
                        and otherwise from the package's own declared date, so
                        the archive is a function of the tree and of nothing
                        else. Determinism is checked by building twice, under
                        two file-creation masks and in two directories, and
                        comparing the bytes.

Commands:

  closure       print the runtime closure and what the archive expects to find
  stage         write the staging tree under --out (default build/ctan)
  archive       write the tree, the archive, and the archive's digest
  sync          report the version and date state of the release artifacts
  check         run every acceptance check and report one line each

`check` exits 1 on the first failing check's report, 0 when every check
passed or was skipped for a missing engine.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import zipfile
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from tenkzlib.texcase import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tex/tenkz"
ENTRY = SOURCE / "tenkz.sty"
MATERIAL = ROOT / "docs/tenkz/ctan"
MANIFEST = MATERIAL / "MANIFEST.toml"
DEFAULT_OUT = ROOT / "build/ctan"

PACKAGE = "tenkz"
DECLARATION = re.compile(r"^\\ProvidesPackage\{tenkz\}\[([^]]*)\]", re.MULTILINE)
PAYLOAD = re.compile(r"(?P<date>[0-9]{4})/([0-9]{2})/([0-9]{2}) v(?P<version>[0-9.]+) ")
INPUT_CALL = re.compile(r"\\input\{([^}]*)\}")
REQUIRE_CALL = re.compile(r"\\RequirePackage(?:\[[^]]*\])?\{([^}]*)\}")
LIBRARY_CALL = re.compile(r"\\usetikzlibrary\{([^}]*)\}", re.DOTALL)

# A name CTAN can carry through any file system and any unpacking tool: the
# invariant ASCII subset, no leading dot or dash, no space.
SAFE_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")

# What a LaTeX run leaves beside its sources. None of it belongs in an upload,
# and none of it belongs in the directory the upload is walked from either.
DEBRIS_SUFFIXES = frozenset(
    {
        ".aux", ".bbl", ".blg", ".fdb_latexmk", ".fls", ".glo", ".gz", ".idx",
        ".ilg", ".ind", ".log", ".nav", ".out", ".snm", ".tnlog", ".toc",
        ".vrb", ".xdv",
    }
)

# Midnight UTC on 1 January 1980, the earliest moment a zip entry can carry.
ZIP_EPOCH_FLOOR = 315532800

# The one licence marker every runtime file carries, and the sentence beside
# it. Both are checked; the identifier is what a machine reads.
LICENSE_MARKER = "% SPDX-License-Identifier: Apache-2.0"
LICENSE_SENTENCE = "% Copyright the TNLean project; see LICENSE for the full terms."

SMOKE_DOCUMENT = r"""\documentclass{article}
\usepackage{tenkz}
\begin{document}
\begin{tenkz}[cols=2]
  \tn[ports={180:virtual:$\alpha$, 90:physical:$i_1$}]{A} &
  \tn[ports={0:virtual:$\beta$, 90:physical:$i_2$}]{B}
\end{tenkz}
\end{document}
"""


# --------------------------------------------------------------------------
# The declared version, and the closure walked from the entry point
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Release:
    """The one version declaration, read from the one file that holds it."""

    version: str
    date: str

    @property
    def epoch(self) -> int:
        """Midnight UTC on the declared date, as the archive's one timestamp."""

        moment = datetime.strptime(self.date, "%Y-%m-%d").replace(tzinfo=timezone.utc)
        return int(moment.timestamp())

    @property
    def archive_stem(self) -> str:
        return f"{PACKAGE}-{self.version}"


def read_release(entry: Path = ENTRY) -> Release:
    declarations = DECLARATION.findall(entry.read_text(encoding="utf-8"))
    if len(declarations) != 1:
        raise SystemExit(
            f"{entry.name} must carry exactly one "
            f"\\ProvidesPackage{{tenkz}} line; found {len(declarations)}"
        )
    match = PAYLOAD.match(declarations[0])
    if match is None:
        raise SystemExit(
            f"{entry.name} declares {declarations[0]!r}, which is not "
            "spelled [YYYY/MM/DD vVERSION description]"
        )
    year, month, day = match.group(1), match.group(2), match.group(3)
    return Release(version=match["version"], date=f"{year}-{month}-{day}")


@dataclass
class Closure:
    """What the entry point loads, and what it expects the system to have."""

    files: list[str] = field(default_factory=list)
    packages: list[str] = field(default_factory=list)
    libraries: list[str] = field(default_factory=list)


def walk_closure(source: Path = SOURCE, entry: str = ENTRY.name) -> Closure:
    """Follow the load graph from the entry point, in load order.

    Comments are blanked before the graph is read, so a stage named only in
    prose — the load-order commentary in `tenkz.sty` names several — never
    enters the closure, and a stage commented out leaves it.
    """

    closure = Closure()
    packages: list[str] = []
    libraries: list[str] = []

    def visit(name: str) -> None:
        if name in closure.files:
            return
        path = source / name
        if not path.is_file():
            raise SystemExit(f"{entry} loads {name}, which is missing")
        closure.files.append(name)
        text = strip_comments(path.read_text(encoding="utf-8"))
        for group in REQUIRE_CALL.findall(text):
            packages.extend(part.strip() for part in group.split(",") if part.strip())
        for group in LIBRARY_CALL.findall(text):
            libraries.extend(part.strip() for part in group.split(",") if part.strip())
        for target in INPUT_CALL.findall(text):
            visit(target.strip())

    visit(entry)
    closure.packages = sorted(set(packages))
    closure.libraries = sorted(set(libraries))
    return closure


def read_manifest() -> dict:
    return tomllib.loads(MANIFEST.read_text(encoding="utf-8"))


# --------------------------------------------------------------------------
# Staging and the archive
# --------------------------------------------------------------------------


def staged_content(manifest: dict, closure: Closure) -> dict[str, Path]:
    """Every staged name, in the order the archive stores it, and its source.

    Runtime files keep their load order, the reader-facing material follows in
    the order the manifest declares. Archive member order is part of the
    bytes, so it comes from the tree rather than from a directory listing.
    """

    content: dict[str, Path] = {name: SOURCE / name for name in closure.files}
    for name, relative in manifest["material"].items():
        content[name] = ROOT / relative
    return content


def stage(destination: Path, epoch: int, content: dict[str, Path]) -> Path:
    """Write the staging tree, replacing whatever stood there before."""

    tree = destination / PACKAGE
    if destination.exists():
        shutil.rmtree(destination)
    tree.mkdir(parents=True)
    for name, source in content.items():
        target = tree / name
        target.write_bytes(source.read_bytes())
        target.chmod(0o644)
        os.utime(target, (epoch, epoch))
    tree.chmod(0o755)
    os.utime(tree, (epoch, epoch))
    return tree


def write_archive(destination: Path, release: Release, epoch: int,
                  content: dict[str, Path]) -> Path:
    """Write the upload archive, with every varying field fixed.

    Four fields of a zip entry are otherwise written from the machine that
    built it: the modification time, the permission bits, the creating system,
    and the member order. All four are set here.

    One field is not fixed by this file: the compressed bytes come from the
    compression library the builder links, at the level named here. Two builds
    of one tree in one environment agree, which is what the determinism check
    proves and what a recorded digest means; a digest carried across a
    compression-library change is not a claim this tool makes. The staged tree
    beside the archive has no such caveat, and the check compares it too.
    """

    archive = destination / f"{release.archive_stem}.zip"
    moment = datetime.fromtimestamp(epoch, tz=timezone.utc).timetuple()[:6]
    with zipfile.ZipFile(
        archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9
    ) as bundle:
        directory = zipfile.ZipInfo(f"{PACKAGE}/", date_time=moment)
        directory.create_system = 3
        directory.external_attr = (0o040755 << 16) | 0x10
        bundle.writestr(directory, b"")
        for name, source in content.items():
            entry = zipfile.ZipInfo(f"{PACKAGE}/{name}", date_time=moment)
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            bundle.writestr(entry, source.read_bytes())
    archive.chmod(0o644)
    os.utime(archive, (epoch, epoch))
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    receipt = destination / f"{release.archive_stem}.zip.sha256"
    receipt.write_text(f"{digest}  {archive.name}\n", encoding="utf-8")
    receipt.chmod(0o644)
    os.utime(receipt, (epoch, epoch))
    return archive


def build(destination: Path) -> tuple[Path, Release, str]:
    """Stage the tree and write the archive; answer the archive's digest."""

    release = read_release()
    epoch = chosen_epoch(release)
    closure = walk_closure()
    content = staged_content(read_manifest(), closure)
    stage(destination, epoch, content)
    archive = write_archive(destination, release, epoch, content)
    return archive, release, hashlib.sha256(archive.read_bytes()).hexdigest()


def chosen_epoch(release: Release) -> int:
    """`SOURCE_DATE_EPOCH` when the environment sets it, the package date else.

    A zip entry cannot carry a date before 1980, and `0` is a common value for
    the environment variable, so an earlier moment is raised to the format's
    floor rather than crashing the build. The staged tree is raised with it:
    one moment stamps both, or the tree and the archive would disagree.
    """

    value = os.environ.get("SOURCE_DATE_EPOCH")
    chosen = int(value) if value else release.epoch
    return max(chosen, ZIP_EPOCH_FLOOR)


# --------------------------------------------------------------------------
# The checks
# --------------------------------------------------------------------------


@dataclass
class Report:
    """One check's verdict, and every reason it holds or fails."""

    name: str
    failures: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    skipped: str = ""

    def require(self, condition: object, reason: str) -> None:
        if not condition:
            self.failures.append(reason)

    @property
    def status(self) -> str:
        if self.failures:
            return "FAIL"
        return "SKIP" if self.skipped else "ok"


def check_closure(closure: Closure, manifest: dict) -> Report:
    report = Report("closure")
    runtime = manifest["runtime"]
    report.require(
        closure.files == runtime["files"],
        f"the load graph walked from {ENTRY.name} is {closure.files}, and "
        f"{MANIFEST.relative_to(ROOT)} pins {runtime['files']}",
    )
    report.require(
        closure.packages == runtime["requires"]["packages"],
        f"loaded packages are {closure.packages}, pinned "
        f"{runtime['requires']['packages']}",
    )
    report.require(
        closure.libraries == runtime["requires"]["libraries"],
        f"loaded TikZ libraries are {closure.libraries}, pinned "
        f"{runtime['requires']['libraries']}",
    )
    report.notes.append(
        f"{len(closure.files)} runtime files; needs {', '.join(closure.packages)} "
        f"and {len(closure.libraries)} TikZ libraries"
    )
    return report


def check_source_tree(closure: Closure, manifest: dict, source: Path = SOURCE) -> Report:
    """Nothing in the source directory is unaccounted for, and none of it is debris."""

    report = Report("sources")
    excluded = set(manifest["source_tree"]["excluded"])
    for entry in sorted(source.iterdir()):
        if entry.name in excluded:
            continue
        report.require(
            entry.is_file(),
            f"{entry.name} is a directory that the upload neither carries nor excludes",
        )
        report.require(
            entry.suffix not in DEBRIS_SUFFIXES,
            f"{entry.name} is a compilation leftover in the source tree",
        )
        report.require(
            entry.name in closure.files,
            f"{entry.name} is not loaded by {ENTRY.name} and is not "
            f"excluded in {MANIFEST.relative_to(ROOT)}",
        )
    return report


def check_material(manifest: dict) -> Report:
    """The reader-facing material an upload must carry, and what it must say."""

    report = Report("material")
    for name, relative in manifest["material"].items():
        source = ROOT / relative
        report.require(source.is_file(), f"{relative} is declared and missing")
    readme = ROOT / manifest["material"]["README.md"]
    if not readme.is_file():
        return report
    text = readme.read_text(encoding="utf-8")
    for heading in ("## Requirements", "## Author and maintainer", "## License"):
        report.require(
            heading in text, f"the CTAN README carries no {heading[3:]!r} section"
        )
    report.require(
        "@" in text, "the CTAN README states no contact address"
    )
    return report


def check_encoding(content: dict[str, Path]) -> Report:
    """Every staged file decodes as UTF-8, and none carries a byte-order mark."""

    report = Report("encoding")
    for name, source in content.items():
        raw = source.read_bytes()
        report.require(
            not raw.startswith(b"\xef\xbb\xbf"),
            f"{name} begins with a byte-order mark",
        )
        try:
            raw.decode("utf-8")
        except UnicodeDecodeError as error:
            report.failures.append(f"{name} is not UTF-8: {error}")
    return report


def check_names(content: dict[str, Path]) -> Report:
    """Names an unpacking tool cannot misread, on any file system."""

    report = Report("names")
    seen: dict[str, str] = {}
    for name in content:
        report.require(
            SAFE_NAME.fullmatch(name) is not None,
            f"{name!r} is not spelled in the invariant ASCII subset",
        )
        collision = seen.get(name.lower())
        report.require(
            collision is None,
            f"{name!r} and {collision!r} differ only in case",
        )
        seen[name.lower()] = name
    return report


def check_permissions(tree: Path) -> Report:
    """One mode for files, one for directories, whatever the builder's mask."""

    report = Report("permissions")
    for path in [tree, *sorted(tree.rglob("*"))]:
        expected = 0o755 if path.is_dir() else 0o644
        mode = path.stat().st_mode & 0o777
        report.require(
            mode == expected,
            f"{path.name} is mode {mode:o}, and the upload normalizes to {expected:o}",
        )
    return report


def check_debris(tree: Path) -> Report:
    """The staged tree carries sources and reader-facing material, nothing else."""

    report = Report("debris")
    for path in sorted(tree.rglob("*")):
        if path.is_dir():
            continue
        report.require(
            path.suffix not in DEBRIS_SUFFIXES,
            f"{path.name} is a compilation leftover and would ship",
        )
    return report


def check_headers(closure: Closure, source: Path = SOURCE) -> Report:
    """Every runtime file names its licence where a reader of that file looks."""

    report = Report("headers")
    for name in closure.files:
        head = "\n".join((source / name).read_text(encoding="utf-8").splitlines()[:12])
        report.require(
            LICENSE_MARKER in head,
            f"{name} carries no licence identifier in its first twelve lines",
        )
        report.require(
            LICENSE_SENTENCE in head,
            f"{name} carries no copyright sentence in its first twelve lines",
        )
    return report


def _material_text(manifest: dict, name: str) -> str:
    """The staged material's text, or nothing when the file is absent.

    An absent file is the material check's finding to report. Reading it here
    would raise before any check printed its line, which turns a named missing
    file into a traceback.
    """

    path = ROOT / manifest["material"][name]
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def check_version(release: Release, manifest: dict) -> Report:
    """One declaration, and every other record checked against it."""

    report = Report("version")
    readme = _material_text(manifest, "README.md")
    stated = f"Version {release.version}, released {release.date}."
    report.require(
        stated in readme,
        f"the CTAN README must state {stated!r}, the version declared by "
        f"{ENTRY.relative_to(ROOT)}",
    )
    citation = _material_text(manifest, "CITATION.cff")
    report.require(
        f'version: "{release.version}"' in citation,
        f"the citation record must state version {release.version}",
    )
    report.require(
        f'date-released: "{release.date}"' in citation,
        f"the citation record must state date-released {release.date}",
    )
    bibliography = _material_text(manifest, "tenkz.bib")
    year, month, _ = release.date.split("-")
    report.require(
        f"version {release.version}" in bibliography,
        f"the BibTeX record must state version {release.version}",
    )
    report.require(
        re.search(rf"year\s*=\s*\{{{year}\}}", bibliography) is not None,
        f"the BibTeX record must state year {year}",
    )
    report.require(
        re.search(rf"month\s*=\s*\{{{int(month)}\}}", bibliography) is not None,
        f"the BibTeX record must state month {int(month)}",
    )
    report.notes.append(f"{release.archive_stem}.zip from v{release.version} of {release.date}")
    return report


def check_determinism(release: Release) -> Report:
    """Build twice and compare the bytes, under two masks and in two places."""

    report = Report("determinism")
    digests: list[str] = []
    listings: list[list[tuple[str, int, int]]] = []
    for label, mask in (("first", 0o022), ("second", 0o077)):
        previous = os.umask(mask)
        try:
            with tempfile.TemporaryDirectory(prefix=f"tenkz-ctan-{label}-") as directory:
                archive, _, digest = build(Path(directory) / "out")
                digests.append(digest)
                tree = archive.parent / PACKAGE
                listings.append(
                    sorted(
                        (
                            str(path.relative_to(tree)),
                            path.stat().st_mode & 0o777,
                            path.stat().st_mtime_ns,
                        )
                        for path in tree.rglob("*")
                    )
                )
        finally:
            os.umask(previous)
    report.require(
        digests[0] == digests[1],
        f"two builds of the same tree gave {digests[0]} and {digests[1]}",
    )
    report.require(
        listings[0] == listings[1],
        "two staged trees differ in name, mode, or modification time",
    )
    report.notes.append(f"{release.archive_stem}.zip is sha256 {digests[0]}")
    return report


def resolved_runtime_files(record: Path) -> list[str]:
    """The runtime files the engine actually opened, from its input record.

    The search path ends in an empty element, which is what restores the
    installation's own directories after the unpacked archive — an author who
    installs the package still needs `tikz`, `hobby`, and `spath3`. That same
    rule means a machine with an older tenkz installed could answer a file the
    archive forgot, and the run would pass while proving nothing. So the
    engine is asked to record every file it opened, and the record, not the
    exit status, says where the runtime came from.
    """

    opened: list[str] = []
    for line in record.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.startswith("INPUT "):
            continue
        path = line[len("INPUT "):].strip()
        if Path(path).name.startswith(PACKAGE):
            opened.append(path)
    return opened


def foreign_runtime_files(opened: list[str], room: Path, unpacked: Path) -> list[str]:
    """Those of the opened files that came from somewhere else.

    A record line may name a path relative to the directory the engine ran in,
    so the room is the base against which a name is resolved.
    """

    return [
        path for path in opened if not (room / path).resolve().is_relative_to(unpacked)
    ]


def check_smoke(archive: Path, required: bool) -> Report:
    """Unpack the archive alone and compile a document against it."""

    report = Report("clean-install")
    if shutil.which("xelatex") is None:
        if required:
            report.failures.append("xelatex is absent and the check was required")
        else:
            report.skipped = "xelatex is absent"
        return report
    with tempfile.TemporaryDirectory(prefix="tenkz-ctan-smoke-") as directory:
        room = Path(directory)
        with zipfile.ZipFile(archive) as bundle:
            bundle.extractall(room)
        unpacked = (room / PACKAGE).resolve()
        document = room / "smoke.tex"
        document.write_text(SMOKE_DOCUMENT, encoding="utf-8")
        environment = dict(os.environ)
        environment["TEXINPUTS"] = f"{unpacked}//:"
        environment["TEXMFOUTPUT"] = str(room)
        try:
            finished = subprocess.run(
                [
                    "xelatex",
                    "-interaction=nonstopmode",
                    "-halt-on-error",
                    "-recorder",
                    "smoke.tex",
                ],
                cwd=room,
                env=environment,
                capture_output=True,
                text=True,
                timeout=120,
            )
        except subprocess.TimeoutExpired:
            report.failures.append(
                "a document using only the unpacked archive did not finish "
                "compiling within 120 seconds"
            )
            return report
        if finished.returncode != 0:
            tail = "\n".join(
                (finished.stdout + finished.stderr).splitlines()[-25:]
            )
            report.failures.append(
                "a document using only the unpacked archive failed to compile, "
                f"exit {finished.returncode}:\n{tail}"
            )
            return report
        record = room / "smoke.fls"
        if not record.is_file():
            report.failures.append("the engine wrote no input record to read")
            return report
        opened = resolved_runtime_files(record)
        strangers = foreign_runtime_files(opened, room, unpacked)
        report.require(
            opened, "the run opened no tenkz file, so it proved nothing"
        )
        report.require(
            not strangers,
            "the run resolved runtime files outside the unpacked archive, so an "
            f"installed copy answered for it: {sorted(set(strangers))}",
        )
        if not report.failures:
            report.notes.append(
                f"a two-cell picture compiled from the unpacked archive, "
                f"reading {len(set(opened))} of its files and no other tenkz file"
            )
    return report


def release_sync(release: Release) -> list[tuple[str, str]]:
    """What each release artifact currently says about its version and date.

    The version freeze is a release decision, not this tool's: the rows are
    reported and never enforced here. `docs/tenkz/RELEASE-POLICY.md` §3 owns
    the agreement a tag requires.
    """

    manual = (ROOT / "docs/tenkz/manual2.tex").read_text(encoding="utf-8")
    changes = (ROOT / "docs/tenkz/CHANGES.md").read_text(encoding="utf-8")
    tnlog = (ROOT / "docs/tenkz/TNLOG.md").read_text(encoding="utf-8")
    dateline = re.search(r"The TNLean project \\quad---\\quad ([^\\]*)\\par", manual)
    event = re.search(r'^version = "([0-9.]+)"', tnlog, re.MULTILINE)
    return [
        ("tex/tenkz/tenkz.sty", f"v{release.version} of {release.date}"),
        ("docs/tenkz/manual2.tex", (dateline.group(1).strip() if dateline else "no date line")),
        ("docs/tenkz/CHANGES.md", changes.splitlines()[0].lstrip("# ").strip()),
        ("docs/tenkz/TNLOG.md", f"event format {event.group(1)}" if event else "no version"),
    ]


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------


def command_closure() -> int:
    closure = walk_closure()
    print(f"runtime closure of {ENTRY.relative_to(ROOT)}, in load order:")
    for name in closure.files:
        print(f"  {name}")
    print(f"loads: {', '.join(closure.packages)}")
    print(f"TikZ libraries: {', '.join(closure.libraries)}")
    return 0


def command_stage(out: Path) -> int:
    release = read_release()
    epoch = chosen_epoch(release)
    content = staged_content(read_manifest(), walk_closure())
    tree = stage(out, epoch, content)
    print(f"staged {len(content)} files under {tree}")
    return 0


def command_archive(out: Path) -> int:
    archive, release, digest = build(out)
    print(f"wrote {archive}")
    print(f"sha256 {digest}")
    print(f"version v{release.version} of {release.date}")
    return 0


def command_sync() -> int:
    for artifact, state in release_sync(read_release()):
        print(f"  {artifact:28s} {state}")
    return 0


def command_check(require_smoke: bool, keep: Path | None) -> int:
    release = read_release()
    manifest = read_manifest()
    closure = walk_closure()
    reports = [
        check_closure(closure, manifest),
        check_source_tree(closure, manifest),
        check_material(manifest),
        check_headers(closure),
        check_version(release, manifest),
    ]
    content = staged_content(manifest, closure)
    reports.append(check_encoding(content))
    reports.append(check_names(content))
    with tempfile.TemporaryDirectory(prefix="tenkz-ctan-check-") as directory:
        destination = keep if keep is not None else Path(directory) / "out"
        archive, _, digest = build(destination)
        reports.append(check_permissions(destination / PACKAGE))
        reports.append(check_debris(destination / PACKAGE))
        reports.append(check_determinism(release))
        reports.append(check_smoke(archive, require_smoke))
    for report in reports:
        print(f"  {report.status:4s} {report.name}")
        for note in report.notes:
            print(f"         {note}")
        if report.skipped:
            print(f"         skipped: {report.skipped}")
        for failure in report.failures:
            for line in failure.splitlines():
                print(f"         {line}")
    print("release artifacts, for the preparation change that synchronizes them:")
    for artifact, state in release_sync(release):
        print(f"  {artifact:28s} {state}")
    failed = [report.name for report in reports if report.failures]
    if failed:
        print(f"tenkz-ctan: FAIL: {', '.join(failed)}")
        return 1
    print(f"tenkz-ctan: PASS: {release.archive_stem}.zip is sha256 {digest}")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("closure", help="print the runtime closure")
    staging = commands.add_parser("stage", help="write the staging tree")
    staging.add_argument("--out", type=Path, default=DEFAULT_OUT)
    packing = commands.add_parser("archive", help="write the tree and the archive")
    packing.add_argument("--out", type=Path, default=DEFAULT_OUT)
    commands.add_parser("sync", help="report the release artifacts' version state")
    checking = commands.add_parser("check", help="run every acceptance check")
    checking.add_argument(
        "--require-smoke",
        action="store_true",
        help="fail rather than skip when no TeX engine is installed",
    )
    checking.add_argument(
        "--out",
        type=Path,
        default=None,
        help="keep the checked tree and archive here instead of discarding them",
    )
    arguments = parser.parse_args(argv)
    if arguments.command == "closure":
        return command_closure()
    if arguments.command == "stage":
        return command_stage(arguments.out)
    if arguments.command == "archive":
        return command_archive(arguments.out)
    if arguments.command == "sync":
        return command_sync()
    return command_check(arguments.require_smoke, arguments.out)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
