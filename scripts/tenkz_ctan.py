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
from datetime import date, datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from tenkzlib.texcase import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tex/tenkz"
ENTRY = SOURCE / "tenkz.sty"
MATERIAL = ROOT / "docs/tenkz/ctan"
# The pinned staging tree. An environment variable may name another one, so
# the contract tests can run the whole command against a manifest that is
# wrong on purpose without editing a tracked file to do it.
MANIFEST = Path(
    os.environ.get("TENKZ_CTAN_MANIFEST") or MATERIAL / "MANIFEST.toml"
)
MANIFEST_LABEL = (
    str(MANIFEST.relative_to(ROOT)) if MANIFEST.is_relative_to(ROOT) else str(MANIFEST)
)
DEFAULT_OUT = ROOT / "build/ctan"

PACKAGE = "tenkz"
MANIFEST_SCHEMA = 1
DECLARATION = re.compile(r"^\\ProvidesPackage\{tenkz\}\[([^]]*)\]", re.MULTILINE)
# The version spelling `RELEASE-POLICY.md` §3 fixes: major, minor, and an
# optional patch, each a nonempty run of digits, followed by a description.
# A typo such as `v1..0` is a malformed declaration, not a version this tool
# carries into an archive name. The pattern matches the whole payload, and
# spells it as `tests/tenkz/release-harness/tex_api_package_version.py` does,
# so the two gates cannot disagree about the same declaration.
PAYLOAD = re.compile(
    r"(?P<date>[0-9]{4})/([0-9]{2})/([0-9]{2}) "
    r"v(?P<version>[0-9]+\.[0-9]+(?:\.[0-9]+)?) \S.*",
    re.DOTALL,
)
# TeX allows space, and a comment-blanked newline, between a control word and
# its arguments, so the patterns allow it too: `\RequirePackage {tikz}` is a
# load, and a closure that missed it would let the manifest pin a dependency
# list the package does not have.
INPUT_CALL = re.compile(r"\\input\s*\{([^}]*)\}", re.DOTALL)
REQUIRE_CALL = re.compile(
    r"\\RequirePackage\s*(?:\[[^]]*\]\s*)?\{([^}]*)\}", re.DOTALL
)
LIBRARY_CALL = re.compile(r"\\usetikzlibrary\s*\{([^}]*)\}", re.DOTALL)

# A name CTAN can carry through any file system and any unpacking tool: the
# invariant ASCII subset, no leading dot or dash, no space.
SAFE_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")

# Names Windows reserves for devices, whatever suffix follows them, and which
# an unpacking tool there cannot write. A CTAN archive is unpacked on every
# platform TeX Live runs on.
RESERVED_NAMES = frozenset(
    {"CON", "PRN", "AUX", "NUL"}
    | {f"COM{digit}" for digit in range(1, 10)}
    | {f"LPT{digit}" for digit in range(1, 10)}
)

# What a LaTeX run leaves beside its sources. None of it belongs in an upload,
# and none of it belongs in the directory the upload is walked from either.
DEBRIS_SUFFIXES = frozenset(
    {
        ".aux", ".bbl", ".blg", ".fdb_latexmk", ".fls", ".glo", ".gz", ".idx",
        ".ilg", ".ind", ".log", ".nav", ".out", ".snm", ".tnlog", ".toc",
        ".vrb", ".xdv",
    }
)

# The window a zip entry's date field can express: from midnight UTC on 1
# January 1980 to the end of 2107. An earlier moment is raised to the floor,
# because `SOURCE_DATE_EPOCH=0` is a convention meaning "no meaningful date";
# a later one is refused, because a date past 2107 is a mistake and clamping
# it would silently mis-date the upload.
ZIP_EPOCH_FLOOR = 315532800
ZIP_EPOCH_CEILING = int(
    datetime(2107, 12, 31, 23, 59, 58, tzinfo=timezone.utc).timestamp()
)

# The staged names an upload carries whatever else the manifest declares. A
# manifest that dropped one of these would build an archive without a licence
# or without a change record, and every check below it would still pass.
REQUIRED_MATERIAL = ("README.md", "LICENSE", "CHANGES.md", "CITATION.cff", "tenkz.bib")

# Existence is not identity: a manifest can point a staged name at the wrong
# existing file, and an upload whose LICENSE is the change record is worse
# than one with no licence at all, because it looks answered.
#
# Two of the five are named elsewhere already — `DESIGN.md` calls
# `docs/tenkz/CHANGES.md` the release change record, and the licence is the
# repository's — so those are pinned to their source rather than sniffed. A
# phrase would not do for them: a change record has no durable sentence, and
# the licence's name appears in the README that sits beside it.
CANONICAL_MATERIAL = {
    "LICENSE": "LICENSE",
    "CHANGES.md": "docs/tenkz/CHANGES.md",
}

# The tables a staging manifest is made of, and the keys each one is read for.
# The checks below index them without asking, which is what a manifest that
# has passed `read_manifest` is for.
MANIFEST_TABLES = {
    "runtime": ("files", "requires"),
    "material": (),
    "source_tree": ("excluded",),
}

# The other three are recognized by a phrase each carries and the others do
# not.
MATERIAL_MARKS = {
    "README.md": "## Requirements",
    "CITATION.cff": "cff-version:",
    "tenkz.bib": "@manual{tenkz",
}

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
    try:
        text = entry.read_bytes().decode("utf-8")
    except FileNotFoundError:
        raise SystemExit(f"{entry.name} is missing; there is no package to stage") from None
    except UnicodeDecodeError as error:
        raise SystemExit(f"{entry.name} is not UTF-8 and cannot be read: {error}") from None
    declarations = DECLARATION.findall(text)
    if len(declarations) != 1:
        raise SystemExit(
            f"{entry.name} must carry exactly one "
            f"\\ProvidesPackage{{tenkz}} line; found {len(declarations)}"
        )
    match = PAYLOAD.fullmatch(declarations[0])
    if match is None:
        raise SystemExit(
            f"{entry.name} declares {declarations[0]!r}, which is not "
            "spelled [YYYY/MM/DD vVERSION description]"
        )
    year, month, day = match.group(1), match.group(2), match.group(3)
    try:
        date(int(year), int(month), int(day))
    except ValueError:
        raise SystemExit(
            f"{entry.name} declares {year}/{month}/{day}, which is not a "
            "calendar date"
        ) from None
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
        try:
            text = strip_comments(path.read_bytes().decode("utf-8"))
        except UnicodeDecodeError as error:
            raise SystemExit(f"{name} is not UTF-8 and cannot be read: {error}") from None
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
    """The pinned staging tree, or a message naming what is wrong with it."""

    try:
        manifest = tomllib.loads(MANIFEST.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise SystemExit(f"{MANIFEST_LABEL} is missing") from None
    except tomllib.TOMLDecodeError as error:
        raise SystemExit(f"{MANIFEST_LABEL} does not parse: {error}") from None
    # The schema and the package are read before anything else is trusted: a
    # later schema means this tool would be interpreting a manifest written
    # for a different one, and a different package means it is not this
    # package's manifest at all. Both fail closed.
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise SystemExit(
            f"{MANIFEST_LABEL} declares schema {manifest.get('schema')!r}; this "
            f"tool reads schema {MANIFEST_SCHEMA}"
        )
    if manifest.get("package") != PACKAGE:
        raise SystemExit(
            f"{MANIFEST_LABEL} declares package {manifest.get('package')!r}, "
            f"not {PACKAGE!r}"
        )
    # Every reader below indexes these tables directly, because a manifest
    # that has been read is a manifest that describes a staging tree. A file
    # missing one of them is not one, and it says so here rather than as a
    # key error from whichever check happened to reach it first.
    for table, keys in MANIFEST_TABLES.items():
        section = manifest.get(table)
        if not isinstance(section, dict):
            raise SystemExit(
                f"{MANIFEST_LABEL} declares no [{table}] table; a staging "
                "manifest names the runtime, the material, and what the "
                "source tree excludes"
            )
        for key in keys:
            if key not in section:
                raise SystemExit(
                    f"{MANIFEST_LABEL} declares [{table}] without {key!r}"
                )
    requires = manifest["runtime"]["requires"]
    if not isinstance(requires, dict) or not {"packages", "libraries"} <= set(requires):
        raise SystemExit(
            f"{MANIFEST_LABEL} declares [runtime.requires] without its "
            "packages and libraries"
        )
    return manifest


# --------------------------------------------------------------------------
# Staging and the archive
# --------------------------------------------------------------------------


def inside_repository(name: str, source: Path) -> Path:
    """The staged file's source, resolved, or a refusal to leave the tree.

    Every source is resolved, runtime files included: a runtime file may be a
    link, and a link out of the tree would put a machine's own files in an
    archive that claims to be a function of this repository.
    """

    resolved = source.resolve()
    if not resolved.is_relative_to(ROOT):
        raise SystemExit(
            f"{name} is staged from {resolved}, outside the repository; the "
            "archive is built from the tree and from nothing else"
        )
    return resolved


def staged_content(manifest: dict, closure: Closure) -> dict[str, Path]:
    """Every staged name, in the order the archive stores it, and its source.

    Runtime files keep their load order, the reader-facing material follows in
    the order the manifest declares. Archive member order is part of the
    bytes, so it comes from the tree rather than from a directory listing.

    Two manifest mistakes make this mapping unwritable: a material entry named
    after a runtime file, which would ship under a name the closure and header
    checks read from a different file, and a name outside the invariant subset,
    which would be joined to the staging directory and resolved. Both are
    findings of the `names` check, which the reporting command prints and
    `require_writable_names` turns into a refusal before any write.

    A source outside the repository is refused here and on both paths: it is
    not a mistake in what the archive would be called but in what it would
    contain, and resolving it is how it is found at all.
    """

    content: dict[str, Path] = {}
    for name in closure.files:
        content[name] = inside_repository(name, SOURCE / name)
    for name, relative in manifest["material"].items():
        content[name] = inside_repository(name, ROOT / relative)
    return content


def require_writable_names(manifest: dict, closure: Closure,
                           content: dict[str, Path]) -> None:
    """The name check, as a refusal rather than a report.

    The reporting command says what is wrong with a staged name and keeps
    going; a command that writes has nowhere to put a finding, so it stops on
    any of them. Both readings come from the same check, so they cannot drift
    apart.
    """

    findings = check_names(content, manifest, closure).failures
    if findings:
        raise SystemExit(
            f"{MANIFEST_LABEL} names a staged file that will not be "
            "written: " + "; ".join(findings)
        )


def require_sound_material(manifest: dict) -> None:
    """The material check, as a refusal rather than a report.

    The reporting command says what is wrong with the material and keeps
    going; a command that writes has nowhere to put a finding, so it stops on
    any of them — a missing entry, an absent file, a staged name pointing at
    the wrong one. Both readings come from the same check, so they cannot
    drift apart.
    """

    findings = check_material(manifest).failures
    if findings:
        raise SystemExit(
            f"{MANIFEST_LABEL} does not describe an upload: " + "; ".join(findings)
        )


def clear_destination(destination: Path, release: Release) -> None:
    """Empty the output directory of this tool's own artifacts, and nothing else.

    The output directory is an option, and an option that recursively deleted
    whatever it was pointed at would be a bad trade for the convenience of
    rebuilding in place. So the directory itself is never removed: the staged
    tree and the archives this tool writes are, and anything else standing
    there stops the run.

    Recognizing artifacts by name is not enough on its own. `tex/` holds a
    directory called `tenkz`, and it is the package's sources; a destination
    inside the repository is therefore confined to `build/`, which the
    repository ignores and which holds nothing else's work. Outside the
    repository any directory will do, as long as it holds only this tool's
    artifacts.
    """

    resolved = destination.resolve()
    if resolved == Path(resolved.root) or ROOT.is_relative_to(resolved):
        raise SystemExit(
            f"{resolved} contains the repository (or is the file-system root) "
            "and is not an output directory"
        )
    if resolved.is_relative_to(ROOT) and not resolved.is_relative_to(ROOT / "build"):
        raise SystemExit(
            f"{resolved} is inside the repository and outside build/; an output "
            "directory there would stand among tracked files"
        )
    if not resolved.exists():
        return
    if not resolved.is_dir():
        raise SystemExit(f"{resolved} is not a directory")
    # Exactly the three things this run would write, each in the shape it
    # would write them. A name that merely looks like one of them — a private
    # `tenkz-notes.zip`, or a plain file called `tenkz` — is somebody else's.
    expected = {
        PACKAGE: "directory",
        f"{release.archive_stem}.zip": "file",
        f"{release.archive_stem}.zip.sha256": "file",
    }
    ours = []
    for entry in sorted(resolved.iterdir()):
        shape = expected.get(entry.name)
        if shape is None or (shape == "directory") != entry.is_dir():
            raise SystemExit(
                f"{resolved} holds {entry.name}, which this run did not write; "
                f"it writes {sorted(expected)} and removes nothing else"
            )
        ours.append(entry)
    for entry in ours:
        shutil.rmtree(entry) if entry.is_dir() else entry.unlink()


def stage(
    destination: Path, release: Release, epoch: int, content: dict[str, Path]
) -> Path:
    """Write the staging tree, replacing this tool's earlier output."""

    tree = destination / PACKAGE
    clear_destination(destination, release)
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
    manifest = read_manifest()
    require_sound_material(manifest)
    content = staged_content(manifest, closure)
    require_writable_names(manifest, closure, content)
    stage(destination, release, epoch, content)
    archive = write_archive(destination, release, epoch, content)
    return archive, release, hashlib.sha256(archive.read_bytes()).hexdigest()


def even_second(epoch: int) -> int:
    """The moment a zip entry can actually store.

    A zip date field counts in two-second steps, so an odd second stamped on
    the staged tree would arrive in the archive as the second before it, and
    the tree and the archive would disagree about the one timestamp they are
    supposed to share.
    """

    return epoch - (epoch % 2)


def chosen_epoch(release: Release) -> int:
    """`SOURCE_DATE_EPOCH` when the environment sets it, the package date else.

    A zip entry cannot carry a date before 1980, and `0` is a common value for
    the environment variable, so an earlier moment is raised to the format's
    floor rather than crashing the build. The staged tree is raised with it:
    one moment stamps both, or the tree and the archive would disagree.
    """

    value = os.environ.get("SOURCE_DATE_EPOCH")
    if not value:
        return even_second(max(release.epoch, ZIP_EPOCH_FLOOR))
    try:
        chosen = int(value)
    except ValueError:
        raise SystemExit(
            f"SOURCE_DATE_EPOCH is {value!r}, which is not a number of seconds"
        ) from None
    if chosen > ZIP_EPOCH_CEILING:
        raise SystemExit(
            f"SOURCE_DATE_EPOCH is {chosen}, later than the last moment a zip "
            f"entry can carry ({ZIP_EPOCH_CEILING}, the end of 2107)"
        )
    return even_second(max(chosen, ZIP_EPOCH_FLOOR))


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
        f"{MANIFEST_LABEL} pins {runtime['files']}",
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
            f"excluded in {MANIFEST_LABEL}",
        )
    return report


def check_material(manifest: dict) -> Report:
    """The reader-facing material an upload must carry, and what it must say."""

    report = Report("material")
    declared = manifest["material"]
    for name in REQUIRED_MATERIAL:
        report.require(
            name in declared,
            f"{MANIFEST_LABEL} stages no {name}, which every upload "
            "must carry",
        )
    for name, relative in declared.items():
        source = ROOT / relative
        report.require(source.is_file(), f"{relative} is declared and missing")
    # What each required name must turn out to be. A manifest that points a
    # staged name at the wrong existing file — the change record staged as
    # LICENSE, say — passes every check that only asks whether a path exists.
    for name, canonical in CANONICAL_MATERIAL.items():
        report.require(
            declared.get(name, canonical) == canonical,
            f"{name} is staged from {declared.get(name)!r}; it is the "
            f"repository's {canonical}",
        )
    for name, mark in MATERIAL_MARKS.items():
        text = _material_text(manifest, name)
        if not text:
            continue
        report.require(
            mark in text,
            f"the file staged as {name} does not read as one: it does not "
            f"contain {mark!r}",
        )
    text = _material_text(manifest, "README.md")
    if not text:
        return report
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
        if not source.is_file():
            report.failures.append(f"{name} is declared and missing")
            continue
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


def check_names(content: dict[str, Path], manifest: dict | None = None,
                closure: Closure | None = None) -> Report:
    """Names an unpacking tool cannot misread, on any file system.

    Given the manifest and the closure, the check also answers whether the
    material stages a name the runtime already carries: the mapping itself
    cannot say so, because the second entry has taken the first one's place
    in it by the time anybody looks.
    """

    report = Report("names")
    if manifest is not None and closure is not None:
        collisions = sorted(set(manifest["material"]) & set(closure.files))
        report.require(
            not collisions,
            f"{MANIFEST_LABEL} stages material under the runtime "
            f"name(s) {collisions}; the archive would carry a file the closure "
            "and header checks never read",
        )
    seen: dict[str, str] = {}
    for name in content:
        report.require(
            SAFE_NAME.fullmatch(name) is not None,
            f"{name!r} is not spelled in the invariant ASCII subset",
        )
        report.require(
            not name.endswith("."),
            f"{name!r} ends in a dot, which Windows drops when it unpacks",
        )
        report.require(
            name.split(".")[0].upper() not in RESERVED_NAMES,
            f"{name!r} is a reserved device name on Windows, whatever its suffix",
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
    """The staged material's text, or nothing when it is absent or undeclared.

    An undeclared entry and an absent file are both the material check's
    findings to report. Indexing or reading here would raise before any check
    printed its line, which turns a named mistake into a traceback. Bytes are
    decoded permissively for the same reason: the encoding audit owns that
    verdict, and it prints one line rather than a stack.
    """

    relative = manifest["material"].get(name)
    if relative is None:
        return ""
    path = ROOT / relative
    return path.read_bytes().decode("utf-8", errors="replace") if path.is_file() else ""


def _live_bibtex(bibliography: str) -> str:
    """The entries of a BibTeX file, with its prose and its comments removed.

    Everything outside an entry is prose BibTeX never reads, and a `%` line is
    a comment by every convention this repository writes them under. Both can
    hold a version, a year, or a month, and neither states one: the record's
    own fields do, and they are what the version check reads.
    """

    uncommented = re.sub(r"(?m)^\s*%.*$", "", bibliography)
    return "\n".join(re.findall(r"@\w+\s*\{.*?\n\}", uncommented, re.DOTALL))


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
    # Anchored to the start of a line: a commented or nested occurrence of the
    # right string beside a stale live value would otherwise satisfy this. A
    # top-level field is stated once, so a second one — the stale line a
    # release edit left behind — is a finding and not a second chance.
    for field_name, value in (
        ("version", release.version),
        ("date-released", release.date),
    ):
        stated = re.findall(rf'^{field_name}: "([^"]*)"\s*$', citation, re.M)
        report.require(
            stated == [value],
            f"the citation record must state {field_name} {value} as its own "
            f"field, once; it states {stated}",
        )
    bibliography = _live_bibtex(_material_text(manifest, "tenkz.bib"))
    year, month, _ = release.date.split("-")
    # Read from the fields themselves, with the comments taken out first: a
    # BibTeX comment holding the right year beside a live field holding last
    # year's is a stale record, and it reads as one here.
    report.require(
        re.search(rf"note\s*=\s*\{{[^}}]*version\s+{re.escape(release.version)}",
                  bibliography) is not None,
        f"the BibTeX record must state version {release.version} in its note field",
    )
    report.require(
        re.search(rf"year\s*=\s*\{{\s*{year}\s*\}}", bibliography) is not None,
        f"the BibTeX record must state year {year}",
    )
    report.require(
        re.search(rf"month\s*=\s*\{{\s*{int(month)}\s*\}}", bibliography) is not None,
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

    def text(relative: str) -> str:
        # The report is the last thing the command prints, after the findings
        # it exists to report. A missing artifact must not replace them.
        path = ROOT / relative
        return path.read_text(encoding="utf-8", errors="replace") if path.is_file() else ""

    manual = text("docs/tenkz/manual2.tex")
    changes = text("docs/tenkz/CHANGES.md")
    tnlog = text("docs/tenkz/TNLOG.md")
    dateline = re.search(r"The TNLean project \\quad---\\quad ([^\\]*)\\par", manual)
    event = re.search(r'^version = "([0-9.]+)"', tnlog, re.MULTILINE)
    heading = changes.splitlines()[0].lstrip("# ").strip() if changes else "absent"
    return [
        ("tex/tenkz/tenkz.sty", f"v{release.version} of {release.date}"),
        ("docs/tenkz/manual2.tex", (dateline.group(1).strip() if dateline else "no date line")),
        ("docs/tenkz/CHANGES.md", heading),
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
    manifest = read_manifest()
    require_sound_material(manifest)
    closure = walk_closure()
    content = staged_content(manifest, closure)
    require_writable_names(manifest, closure, content)
    tree = stage(out, release, epoch, content)
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
    material = check_material(manifest)
    reports = [
        check_closure(closure, manifest),
        check_source_tree(closure, manifest),
        material,
        check_headers(closure),
        check_version(release, manifest),
    ]
    content = staged_content(manifest, closure)
    encoding = check_encoding(content)
    names = check_names(content, manifest, closure)
    reports.append(encoding)
    reports.append(names)
    # A build cannot run against material that is absent, undeclared, or
    # unreadable, or against a name it would refuse to write, and a traceback
    # would replace the report naming it. The checks that need a built tree
    # report themselves skipped instead; the finding is already a failure of
    # its own.
    blocked = material.failures + encoding.failures + names.failures
    digest = ""
    if blocked:
        for name in ("permissions", "debris", "determinism", "clean-install"):
            skipped = Report(name)
            skipped.skipped = f"the staged material is not complete ({len(blocked)} finding(s))"
            reports.append(skipped)
    else:
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
