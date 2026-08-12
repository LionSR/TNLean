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
  offline       compile the corpus cases against the archive, unpacked flat
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
# Every spelling of an input. The braced one is tried first, then Web2C's
# quoted form, which is how a name holding a space is written and which may
# follow the control word with no space at all, then the bare one, which reads
# to the next space as TeX does and stops at a brace, a comment, or a control
# sequence rather than guessing past one. Quotes are stripped from the name.
# A walk that read one spelling would let a stage module, or a package, reach
# an upload without reaching the pin.
INPUT_CALL = re.compile(
    r"\\input\s*\{\s*\"?([^}\"]*?)\"?\s*\}"
    r"|\\input\s*\"([^\"]+)\""
    r"|\\input\s+([^\s{}\\%\"]+)",
    re.DOTALL,
)
# Every spelling of a package load. A `.sty` writes `\RequirePackage`, but
# nothing stops a staged runtime file from writing `\usepackage` or
# `\RequirePackageWithOptions`, and they load the same package. A closure that
# read one spelling would let a load reach an upload without reaching the pin,
# and would report the retired front ends absent while one was being loaded.
REQUIRE_CALL = re.compile(
    r"\\(?:RequirePackageWithOptions|RequirePackage|usepackage)"
    r"\s*(?:\[[^]]*\]\s*)?\{([^}]*)\}",
    re.DOTALL,
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

# The ways a loaded TikZ library reaches the package, and the report that has
# to account for every one of them. `docs/tenkz/ctan/DEPENDENCIES.md` reads the
# same three words: a library the package's own placement and model code calls,
# a library only the ink it draws needs, and a library loaded with no consumer
# anywhere in the source. The third class is not a spare bin. It is the finding
# a rederivation exists to produce, and it is named so that a library entering
# or leaving it is a reviewed edit rather than a silence.
DEPENDENCY_CLASSES = ("placement", "ink", "unconsumed")

# Front ends the package once carried, and the load each of them brought with
# it. They are checked by absence: the closure walk blanks comments before it
# reads a load, so the sentence in `tenkz.sty` that says commutative diagrams
# belong to tikz-cd is prose and not a dependency, and a real load would be the
# only way any of these names could reach the closure.
RETIRED_DEPENDENCIES = ("tikz-cd", "tikzcd", "quantikz")

# A TikZ library vendored as a file goes by its conventional file name, and a
# stem alone would leave `tikzlibrarytikzcd.code` bearing no resemblance to the
# library it is. The suffixes are stripped in the order a name carries them,
# so `tenkz-core.code.tex` reduces to `tenkz-core` and not to `tenkz-core.code`.
TIKZ_LIBRARY_FILE = re.compile(r"^tikzlibrary(?P<library>.+)$")
LOAD_SUFFIXES = (".code.tex", ".tex", ".sty", ".def", ".cls", ".cfg")


def load_names(name: str) -> set[str]:
    """Every name one loaded file could be known by.

    A load may carry a directory, so the basename is what the suffix and the
    `tikzlibrary` prefix are stripped from; the name as written stays in the
    set as well, since that is what a manifest would pin.
    """

    bare = Path(name).name
    for suffix in LOAD_SUFFIXES:
        if bare.endswith(suffix):
            bare = bare[: -len(suffix)]
            break
    names = {name, Path(name).name, bare}
    library = TIKZ_LIBRARY_FILE.match(bare)
    if library is not None:
        names.add(library["library"])
    return names

# What arXiv will not do for a source submission, expressed as the file kinds
# whose presence would mean it has to. A `.dtx` or `.ins` pair is the usual
# LaTeX-package shape and needs a docstrip run before the runtime exists; a
# `.fmt` or a `.mf` needs the format or the font built. tenkz stages its
# runtime as the files the engine reads, so none of these may be staged. The
# comparison lowers the suffix first: a file system that preserves case will
# hand back `tenkz.INS`, and docstrip does not care which way it was typed.
REGENERATED_SUFFIXES = frozenset({".dtx", ".ins", ".fmt", ".mf", ".drv"})

# The primitives a submission may not need, because arXiv compiles without
# `\write18`. tenkz writes its event stream to a file stream it allocates, and
# calls nothing that reaches a shell; the check is what keeps that true.
#
# The gate fails closed, because TeX's integer scanner accepts more spellings
# of 18 than a pattern can enumerate: space, leading zeros, a run of signs, `"`
# for hexadecimal and `'` for octal, a backtick character constant, `\numexpr`,
# a register. So a `\write` is read three ways and refused if it is none of
# them: a constant, evaluated in the base its prefix names and compared with
# 18; a stream the same file allocated with `\newwrite` or `\iow_new:N`, which
# is a file stream by construction and by intent, unless the same file also
# redefines the name; or anything else, which cannot be shown not to be 18 and
# is a finding on that ground alone.
#
# The boundary after `write` excludes `@` and, for a file under
# `\ExplSyntaxOn`, `_` and `:`, because those are letters there: `\write@event`
# and `\write:nn` are control words of their own, and reading them as the
# primitive would refuse a release over a name.
#
# What the reading is for is a mistake in a staged source, not a source
# written to hide a shell call from it. A primitive assembled at run time
# cannot be read from the text at all, so the one spelling that is still
# recognizable is matched and the rest is out of scope, stated here rather
# than implied by silence.
WRITE_CALL = re.compile(
    r"(?:\\write|\\csname\s*write\s*\\endcsname)"
    r"(?![A-Za-z@_:])(?P<signs>[\s+-]*)"
    r"(?:\"(?P<hex>[0-9A-Fa-f]+)|'(?P<oct>[0-7]+)|(?P<dec>[0-9]+)"
    r"|(?P<name>\\[A-Za-z@_:]+))?"
)
ALLOCATED_STREAM = re.compile(r"\\(?:newwrite|iow_new:N)\s*(\\[A-Za-z@_:]+)")
# A control sequence the same file also redefines is no longer the stream it
# was allocated as: `\newwrite\out \def\out{18} \write\out{...}` reaches the
# shell through a name the allocation vouched for. Reading order is beyond a
# text scan, so an allocated name that is redefined anywhere in the file loses
# the allocation ground and is refused with every other unreadable stream.
REDEFINED_NAME = re.compile(
    r"\\(?:def|edef|gdef|xdef|let|cs_set[a-z_]*:Npn|cs_new[a-z_]*:Npn)"
    r"\s*(\\[A-Za-z@_:]+)"
)
# Web2C reads a file name whose first character is a bar as a command to run,
# so `\openin\stream="|uname -a"` reaches a shell without naming a stream or an
# interface. The bar is only a command in a file name, so the reading is
# scoped to one: a bare `"|` in a macro body or in typeset documentation is
# two characters, and refusing it would refuse a source that executes nothing.
PIPE_FILENAME = re.compile(
    r"\\(?:openin|openout|input|include|read|write)\s*"
    r"(?:\\[A-Za-z@_:]+\s*)?"
    r"(?:=\s*)?"
    r"(?:\{\s*)?"
    r"\"?\s*\|"
)
# The named ways to reach a shell that are not a write at all: the TeX
# primitive's LaTeX name, and expl3's own shell interface, which a file under
# `\ExplSyntaxOn` would use in preference to either. The expl3 names are the
# ones its source defines, `\sys_shell_now:n`, `\sys_shell_shipout:n`,
# `\sys_get_shell:nnN`, `\ior_shell_open:Nn`, and `\iow_shell_open:Nn`, with
# shellesc's `\DelayedShellEscape` beside its `\ShellEscape`, read
# from `l3kernel` rather than recalled, because a name invented here would be a
# gate that looks closed. Only executors are named: `\tex_shellescape:D` and
# `\sys_if_shell:TF` report whether the engine has a shell and run nothing, so
# reading them as calls would refuse a file for asking a question.
# The boundary after the name is the one `WRITE_CALL` uses, for the same
# reason: `@` is a
# letter in a package and `_` and `:` are letters under `\ExplSyntaxOn`, so
# `\ShellEscape@status` and `\sys_shell_now:n_aux` are control words of their
# own and refusing them would block a shell-free release over a name.
SHELL_ESCAPE_NAME = re.compile(
    r"(?:\\(?:Delayed)?ShellEscape"
    r"|\\sys_(?:shell_(?:now|shipout)|get_shell):[a-zA-Z]*"
    r"|\\(?:ior|iow)_shell_open:[a-zA-Z]*)"
    r"(?![A-Za-z@_:])"
)
SHELL_ESCAPE_STREAM = 18


def uncontrolled(text: str) -> str:
    r"""`text` with every `\\` control symbol blanked out.

    A backslash preceded by an odd number of backslashes starts a control
    sequence and one preceded by an even number does not, so the pairs are
    removed before anything is read: `\\write18` is the control symbol and then
    ordinary characters, while `\\\write18` is that symbol and then the
    primitive. Blanking keeps the length, so a match's span still indexes the
    text it came from.
    """

    return text.replace("\\\\", "\x00\x00")


def shell_escape_call(text: str) -> str:
    r"""What in `text` could reach a shell, named, or nothing.

    A `\write` to a constant stream is read in the base its prefix names, so
    the verdict does not depend on how the number was written, and only 18 is
    a finding. A `\write` to a stream the same file allocated is a file stream.
    A `\write` to anything else is a finding, because it cannot be shown not to
    be 18.
    """

    scanned = uncontrolled(text)
    named = SHELL_ESCAPE_NAME.search(scanned)
    if named is not None:
        return f"{text[named.start():named.end()]}, which reaches a shell"
    piped = PIPE_FILENAME.search(scanned)
    if piped is not None:
        return (
            f'{text[piped.start():piped.end()]}, a file name opening a pipe, '
            "which the engine runs as a command"
        )
    allocated = set(ALLOCATED_STREAM.findall(scanned)) - set(
        REDEFINED_NAME.findall(scanned)
    )
    for found in WRITE_CALL.finditer(scanned):
        call = text[found.start():found.end()]
        if found["name"] is not None:
            if found["name"] in allocated:
                continue
            return f"{call.strip()}, a stream this file does not allocate"
        digits, base = (
            (found["hex"], 16) if found["hex"]
            else (found["oct"], 8) if found["oct"]
            else (found["dec"], 10) if found["dec"]
            else (None, 10)
        )
        if digits is None:
            return (
                f"{call.strip()}, whose stream is not a constant this reading "
                "can evaluate"
            )
        sign = -1 if found["signs"].count("-") % 2 else 1
        if sign * int(digits, base) == SHELL_ESCAPE_STREAM:
            return f"{call}, the shell-escape stream"
    return ""


# An absolute path in a staged source names the machine that wrote it. The
# pattern catches the spellings a TeX file can carry: a Unix path or a Windows
# drive letter opening a braced load argument, with the star a starred form
# such as `\includegraphics*` puts before its arguments and the space LaTeX's
# star test skips before it, and the same two opening `\input` unbraced, which
# is plain TeX's own syntax and reads to the next space. Either spelling may
# open with a quote, which is how a path holding a space is written. The
# loader list is
# every one the LaTeX kernel defines that takes a file name, conditional ones
# included: a runtime whose behaviour depends on a machine-local file is not
# submittable even when the file's absence is handled.
ABSOLUTE_PATH_HEAD = r"(?:/|[A-Za-z]:[\\/])"
ABSOLUTE_LOAD = re.compile(
    r"\\(?:input|include|usepackage|RequirePackageWithOptions|RequirePackage"
    r"|InputIfFileExists|IfFileExists|includegraphics|file_input:n"
    r"|file_if_exist:nTF)(?:\s*\*)?"
    rf"\s*(?:\[[^]]*\]\s*)?\{{\s*\"?{ABSOLUTE_PATH_HEAD}"
    rf"|\\input\s*\"?{ABSOLUTE_PATH_HEAD}"
    rf"|\\open(?:in|out)\s*(?:\\[A-Za-z@_:]+)?\s*=\s*\"?{ABSOLUTE_PATH_HEAD}"
)


@dataclass(frozen=True)
class OfflineCase:
    """One picture class, the corpus case that draws it, and its evidence.

    `declares` is read from the case source and `emits` from the event stream
    the compiled run wrote, so a case swapped for one of another class fails
    on both sides rather than passing as "a picture compiled". `absent` is the
    negative half of the same reading: a flat placement is recognized by the
    frame record it does not write.
    """

    name: str
    picture_class: str
    source: str
    document: bool
    declares: str
    emits: str
    absent: str = ""


# The six picture classes an upload is judged on, each drawn by a case the
# corpus already owns and audits: the review benchmark for the classes it
# covers, and the kernel probes for the self-contained document form, whose
# preamble is the one an author writes rather than one this tool supplies.
OFFLINE_CASES = (
    OfflineCase(
        "flat", "flat",
        "tests/tenkz/rmp/section-ii/cases/rmp-ii-mps-marginal.tex",
        False, r"\begin{tenkz}", r"atom\|", absent=r"(?m)^frame\|",
    ),
    OfflineCase(
        "plane", "plane",
        "tests/tenkz/rmp/section-ii/cases/rmp-ii-peps-marginal.tex",
        False, "frame=plane", r"(?m)^frame\|.*map=plane",
    ),
    OfflineCase(
        "circle", "circle",
        "tests/tenkz/rmp/section-ii/cases/rmp-ii-triangle-network.tex",
        # A circle frame transports each port along its station's outward
        # radius, so the boundary signature carries a numeric compass face. A
        # flat or plane placement writes a named one, so the digit is the
        # reading that tells the two apart.
        False, "frame=circle", r"kernel-boundary\|signature=phys:[0-9]",
    ),
    OfflineCase(
        "crossing", "string/crossing",
        "tests/tenkz/rmp/section-iii-b/cases/rmp-iii-b-braid-two.tex",
        # `\tnwire` alone would not tell this case from the flat one, which
        # draws wires too. A string-kind wire is what a crossing is made of.
        False, "kind=string", r"(?m)^stringcross\|",
    ),
    OfflineCase(
        "enclosure", "enclosure",
        "tests/tenkz/rmp/section-ii/cases/rmp-ii-peps-projection.tex",
        False, "form=enclosure", r"(?m)^mark\|.*form=enclosure",
    ),
    OfflineCase(
        "equation", "equation",
        "tests/tenkz/rmp/section-ii/cases/rmp-ii-mpu-brickwork.tex",
        False, r"\begin{tenkzeq}", r"(?m)^check\|.*result=equal",
    ),
    OfflineCase(
        "probe-plane", "plane",
        "tests/tenkz/kernel/k_plane.tex",
        True, "frame=plane", r"(?m)^frame\|.*map=plane",
    ),
    OfflineCase(
        "probe-crossing", "string/crossing",
        "tests/tenkz/kernel/k_braid.tex",
        True, "cross=", r"(?m)^stringcross\|",
    ),
)

# The document an author writes around a preamble-free case. It names the case
# by its flat basename, which is what the submission would look like. The
# preamble asks the environment for nothing beyond what the README declares an
# installation must have. It is `article` rather than the corpus driver's
# `standalone`, and it drops `mathtools`, which none of the cases below calls:
# a gate that failed on a minimal installation would be reporting on the
# installation rather than on the archive.
OFFLINE_WRAPPER = r"""\documentclass{article}
\usepackage{amsmath,amssymb}
\usepackage{tenkz}
\begin{document}
\input{%s}
\end{document}
"""

# The tools a run must not reach for. Each is shadowed by a script that records
# its own call and fails, so "no installation and no fetch happened" is read
# from whether any of them ran rather than assumed from a run that passed.
# `tlmgr` would install a missing package; the `mktex` family would build a
# font or a format on the fly, which is the other way a run can quietly repair
# an incomplete environment.
INTERPOSED_TOOLS = (
    "tlmgr", "curl", "wget", "git", "ftp", "scp", "ssh", "rsync",
    "mktextfm", "mktexpk", "mktexmf", "mktexlsr", "updmap", "fmtutil",
)
TRIPWIRE = "#!/bin/sh\nprintf '%s\\n' \"$0\" >> \"$TENKZ_OFFLINE_TRIPWIRE\"\nexit 127\n"


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
            # Comments are blanked, and so are the `\\` control symbols: a
            # load spelled inside a macro body as text is not a load, and
            # recording one would refuse a release over a definition.
            text = uncontrolled(strip_comments(path.read_bytes().decode("utf-8")))
        except UnicodeDecodeError as error:
            raise SystemExit(f"{name} is not UTF-8 and cannot be read: {error}") from None
        for group in REQUIRE_CALL.findall(text):
            packages.extend(part.strip() for part in group.split(",") if part.strip())
        for group in LIBRARY_CALL.findall(text):
            libraries.extend(part.strip() for part in group.split(",") if part.strip())
        for braced, quoted, bare in INPUT_CALL.findall(text):
            visit((braced or quoted or bare).strip())

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


def check_dependencies(closure: Closure, manifest: dict) -> Report:
    """Every loaded library is accounted for by one consumer class, and the
    retired front ends' loads are gone.

    The closure says what is loaded. It cannot say why, and a list of ten
    library names is not a dependency report: an author reading it cannot tell
    which of them the package needs to place a tensor and which of them only
    the ink it draws needs. The manifest's classification says which, and this
    check is what stops the two from drifting: a library that enters or leaves
    the load list without a class, that is filed under two, or that is named
    twice inside one, fails here, and so does a manifest that leaves a class
    out rather than declaring it empty.

    What this cannot read is whether a class is the *right* one, and the
    `unconsumed` class is where that matters: nothing here can tell a library
    nothing reads from one whose consumer the reader did not find. Searching
    for the library's name does not settle it either, because a library is
    reached through the names it defines rather than through its own. The class
    is established by removing the load and compiling, and
    `docs/tenkz/ctan/DEPENDENCIES.md` records that reading.

    Absence is checked the same way. The retired front ends each brought a load
    with them, and the walk that reads loads has already blanked the comments,
    so a name from that list reaching the closure would mean a real load
    survived the removal rather than a sentence about one.
    """

    report = Report("dependencies")
    ownership = manifest["runtime"]["requires"].get("ownership")
    if not isinstance(ownership, dict):
        report.failures.append(
            f"{MANIFEST_LABEL} declares no [runtime.requires.ownership]; the "
            "loaded libraries are then a list nobody has traced to a consumer"
        )
        return report
    unknown = sorted(set(ownership) - set(DEPENDENCY_CLASSES))
    report.require(
        not unknown,
        f"{MANIFEST_LABEL} files libraries under {unknown}, and a library "
        f"reaches the package one of {list(DEPENDENCY_CLASSES)} ways",
    )
    classified: dict[str, list[str]] = {}
    for name in DEPENDENCY_CLASSES:
        if name not in ownership:
            report.failures.append(
                f"{MANIFEST_LABEL} declares no {name!r} class; a class with no "
                "members is written as an empty list, because leaving it out "
                "reads as a class nobody considered"
            )
            return report
        members = ownership[name]
        if not isinstance(members, list) or any(
            not isinstance(member, str) for member in members
        ):
            report.failures.append(f"[runtime.requires.ownership] {name} is not a list of names")
            return report
        repeated = sorted({member for member in members if members.count(member) > 1})
        report.require(
            not repeated,
            f"{repeated} are named more than once under {name!r}, which reads "
            "as more consumers than the report traced",
        )
        classified[name] = members
    twice = sorted(
        library
        for library in closure.libraries
        if sum(library in members for members in classified.values()) > 1
    )
    report.require(
        not twice,
        f"{twice} are filed under more than one consumer class; a library is "
        "read for one reason or the report does not say what that reason is",
    )
    filed = sorted({library for members in classified.values() for library in members})
    report.require(
        filed == closure.libraries,
        f"the classification covers {filed}, and {ENTRY.name} loads "
        f"{closure.libraries}",
    )
    # A retired front end can arrive as a package load, a library load, or a
    # file the entry point inputs, and a vendored `tikz-cd.sty` or
    # `tikzlibrarytikzcd.code.tex` reaches the closure only in the third way.
    # Each file is compared under every name it could be known by, since a load
    # carries a suffix and a conventional library file carries a prefix too.
    loaded = set(closure.packages) | set(closure.libraries)
    for name in closure.files:
        loaded |= load_names(name)
    survivors = sorted(name for name in RETIRED_DEPENDENCIES if name in loaded)
    report.require(
        not survivors,
        f"{ENTRY.name} still loads {survivors}, which the retired front ends "
        "brought and their removal was supposed to take with them",
    )
    # The note states what the check found, so it is written only when the
    # check held: a line claiming no retired load, printed above the line
    # reporting one, is worse than no line at all.
    if not report.failures:
        report.notes.append(
            "; ".join(
                f"{name}: {len(classified[name])}" for name in DEPENDENCY_CLASSES
            )
            + f"; no load of {', '.join(RETIRED_DEPENDENCIES)}"
        )
    if not report.failures and classified["unconsumed"]:
        report.notes.append(
            "loaded and unread, by the ablation recorded in DEPENDENCIES.md: "
            + ", ".join(classified["unconsumed"])
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


def recorded_inputs(record: Path) -> list[str]:
    """Every file the engine opened, from its input record."""

    return [
        line[len("INPUT "):].strip()
        for line in record.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.startswith("INPUT ")
    ]


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

    return [
        path
        for path in recorded_inputs(record)
        if Path(path).name.startswith(PACKAGE)
    ]


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


def check_arxiv(tree: Path, closure: Closure) -> Report:
    """The staged tree read as an arXiv source submission.

    An upload to CTAN and a source submission to arXiv are the same files under
    two sets of rules, and the second set is the stricter one: arXiv unpacks a
    submission beside the manuscript rather than installing it, runs no
    docstrip and no font builder, and compiles without shell escape. So the
    tree has to be flat, has to be the runtime itself rather than the sources a
    runtime is generated from, has to name no path on the machine that wrote
    it, and has to call no primitive that would need a shell.

    The last two are read from the closure rather than from a list of suffixes.
    Every file the engine opens is on the load graph, whatever it is called, so
    a runtime file added later as a class, a definition file, or a
    configuration is scanned because it is loaded and not because somebody
    remembered to add its suffix here. The reader-facing material is not
    scanned: arXiv never compiles a change record, and a change record that
    mentioned a primitive in prose would be a finding about nothing.
    """

    report = Report("arxiv")
    loaded = set(closure.files)
    for path in sorted(tree.rglob("*")):
        report.require(
            not path.is_dir(),
            f"{path.name} is a directory, and a submission unpacks beside a "
            "manuscript rather than into a tree of its own",
        )
        if path.is_dir():
            continue
        report.require(
            path.suffix.lower() not in REGENERATED_SUFFIXES,
            f"{path.name} would have to be run before the runtime exists, and "
            "a submission is compiled rather than built",
        )
        if path.name not in loaded:
            continue
        text = strip_comments(path.read_bytes().decode("utf-8", errors="replace"))
        report.require(
            ABSOLUTE_LOAD.search(uncontrolled(text)) is None,
            f"{path.name} loads a file by absolute path, which names the "
            "machine it was written on",
        )
        called = shell_escape_call(text)
        report.require(
            not called,
            f"{path.name} calls {called}, and a submission compiles with no shell",
        )
    if not report.failures:
        report.notes.append(
            f"{len(list(tree.iterdir()))} files, one directory deep; "
            f"{len(loaded)} loaded sources read, no generated source and no shell call"
        )
    return report


def offline_room(archive: Path, room: Path) -> list[str]:
    """Unpack the archive flat into one directory, as a submission unpacks.

    CTAN receives a `tenkz/` directory and an installation puts it on the
    search path. A submission has no search path to put it on: the files sit
    beside the manuscript, so this is where the archive is flattened and where
    a runtime file that only resolves through a directory would fail.

    An archive that does not open, or that does not hold the one directory the
    upload is judged on, is answered with a message rather than a traceback:
    this tool's contract is that every finding is a printed line of the report,
    and a caller that raised here would break it.
    """

    with tempfile.TemporaryDirectory(prefix="tenkz-offline-unpack-") as unpacking:
        try:
            with zipfile.ZipFile(archive) as bundle:
                bundle.extractall(unpacking)
        except (zipfile.BadZipFile, OSError) as error:
            raise SystemExit(f"{archive.name} does not open as an archive: {error}") from None
        unpacked = Path(unpacking) / PACKAGE
        if not unpacked.is_dir():
            raise SystemExit(
                f"{archive.name} does not unpack into a single {PACKAGE}/ directory"
            )
        siblings = sorted(
            path.name for path in Path(unpacking).iterdir() if path.name != PACKAGE
        )
        if siblings:
            raise SystemExit(
                f"{archive.name} unpacks {PACKAGE}/ beside {siblings}; an upload "
                "unpacks into one directory and nothing else"
            )
        staged = sorted(path.name for path in unpacked.iterdir())
        for path in sorted(unpacked.iterdir()):
            if not path.is_file():
                raise SystemExit(
                    f"{archive.name} holds {PACKAGE}/{path.name}, which is not a "
                    "file; an upload unpacks one directory deep"
                )
            shutil.copy2(path, room / path.name)
    return staged


def offline_environment(room: Path, shims: Path, tripwire: Path, home: Path) -> dict[str, str]:
    """The environment a run gets, built rather than inherited.

    Nothing of the caller's environment reaches the engine except the search
    path it needs to find its own binaries, and the shim directory comes first
    on it, so an installer or a fetcher the run reached for would be recorded
    instead of run. `TEXINPUTS` is the current directory and then the
    installation: the empty last element is what leaves `tikz`, `hobby`, and
    `spath3` findable, and it is also why the input record, not the exit
    status, decides where the runtime came from.
    """

    return {
        "PATH": os.pathsep.join([str(shims), "/usr/bin", "/bin", os.environ.get("PATH", "")]),
        "HOME": str(home),
        "TEXMFHOME": str(home / "texmf"),
        "TEXMFVAR": str(home / "texmf-var"),
        "TEXMFCONFIG": str(home / "texmf-config"),
        "TEXINPUTS": ".:",
        "TEXMFOUTPUT": str(room),
        "TENKZ_OFFLINE_TRIPWIRE": str(tripwire),
        # kpathsea reads these before it runs a generator, so a missing font or
        # format is a failed run rather than a build nobody asked for.
        "MKTEXTFM": "0",
        "MKTEXPK": "0",
        "MKTEXMF": "0",
        "MKTEXFMT": "0",
        # The discard port, for any client that honours a proxy variable: a
        # fetch that got past the shims still has nowhere to go.
        "http_proxy": "http://127.0.0.1:9",
        "https_proxy": "http://127.0.0.1:9",
        "ftp_proxy": "http://127.0.0.1:9",
        "all_proxy": "http://127.0.0.1:9",
    }


def write_shims(shims: Path) -> None:
    """Shadow every tool a run could install or fetch with, and record calls."""

    shims.mkdir(parents=True, exist_ok=True)
    for tool in INTERPOSED_TOOLS:
        shim = shims / tool
        shim.write_text(TRIPWIRE, encoding="utf-8")
        shim.chmod(0o755)


def carried_runtime() -> set[str]:
    """The runtime file names a record line is read against.

    It comes from the load graph rather than from a `tenkz` prefix, because the
    documents the offline check writes are named from the package too and a
    prefix match would count one of them as proof that the package answered.

    It is deliberately not narrowed to what the archive staged. A runtime file
    the archive forgot has to stay in the reading: an installed copy answering
    for it resolves outside the room, and dropping the name is what would hide
    that. The archive's own completeness is the closure check's question, and
    it is asked there.
    """

    return set(walk_closure().files)


def repository_inputs(opened: list[str], room: Path, flat: Path) -> list[str]:
    """Those of the opened files that came from the repository, not the flat.

    The room is the base a relative record line resolves against, and it is
    also the one directory a file may legitimately come from besides the
    installation. It is subtracted before the repository is read, because a
    temporary directory is placed wherever `TMPDIR` says, and a runner that
    put it inside the workspace would otherwise make every file the archive
    itself answered look like one the repository did.
    """

    return [
        path
        for path in opened
        if not (room / path).resolve().is_relative_to(flat)
        and (room / path).resolve().is_relative_to(ROOT)
    ]


def check_offline(archive: Path, required: bool) -> Report:
    """Compile one case of every picture class against the unpacked flat.

    The clean-install check proves the archive carries a runtime. This one
    proves the runtime draws: a case of each class the release is judged on is
    compiled beside the flattened archive, with no network reachable and no
    installer on the path, and each result is read as the corpus reads it --
    the event stream through the audit, and the class's own record through the
    evidence the case declares. A run that produced a PDF and no tensor network
    fails here, and so does one whose picture is of another class than the one
    it was chosen for.
    """

    report = Report("offline")
    engine = shutil.which("xelatex")
    if engine is None:
        if required:
            report.failures.append("xelatex is absent and the check was required")
        else:
            report.skipped = "xelatex is absent"
        return report
    audit = ROOT / "scripts/tenkz_audit.py"
    if not audit.is_file():
        report.failures.append(f"{audit.relative_to(ROOT)} is missing; nothing would read the runs")
        return report
    with tempfile.TemporaryDirectory(prefix="tenkz-offline-") as directory:
        base = Path(directory)
        room = base / "submission"
        room.mkdir()
        home = base / "home"
        (home / "texmf").mkdir(parents=True)
        tripwire = base / "reached-for.txt"
        shims = base / "shims"
        write_shims(shims)
        try:
            staged = offline_room(archive, room)
        except SystemExit as refusal:
            report.failures.append(str(refusal))
            return report
        environment = offline_environment(room, shims, tripwire, home)
        carried = carried_runtime()
        for case in OFFLINE_CASES:
            _offline_case(case, room, engine, environment, audit, carried, report)
        if tripwire.exists():
            report.failures.append(
                "the runs reached for an installer or a fetcher: "
                + tripwire.read_text(encoding="utf-8", errors="replace").replace("\n", " ")
            )
    if not report.failures:
        report.notes.append(
            f"{len(OFFLINE_CASES)} cases over "
            f"{len({case.picture_class for case in OFFLINE_CASES})} picture classes, "
            f"compiled and audited against {len(staged)} flat files, with "
            f"{len(INTERPOSED_TOOLS)} installers and fetchers shadowed and uncalled"
        )
    return report


def _offline_case(case: OfflineCase, room: Path, engine: str,
                  environment: dict[str, str], audit: Path, carried: set[str],
                  report: Report) -> None:
    """Compile one case in the flat room and read what it wrote.

    `carried` is the runtime the archive holds, by name, and it is what a
    record line is read against.
    """

    source = ROOT / case.source
    if not source.is_file():
        report.failures.append(f"{case.source} is missing; the {case.picture_class} case has moved")
        return
    text = source.read_text(encoding="utf-8")
    if case.declares not in text:
        report.failures.append(
            f"{case.name}: {case.source} no longer spells {case.declares!r}, so it "
            f"is not the {case.picture_class} case this check reads"
        )
        return
    job = f"tenkz-offline-{case.name}"
    if case.document:
        read = f"{job}.tex"
        (room / read).write_text(text, encoding="utf-8")
    else:
        read = f"{job}-case.tex"
        (room / read).write_text(text, encoding="utf-8")
        (room / f"{job}.tex").write_text(OFFLINE_WRAPPER % read, encoding="utf-8")
    try:
        finished = subprocess.run(
            [engine, "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", "-recorder", f"{job}.tex"],
            cwd=room, env=environment, capture_output=True, text=True, timeout=300,
        )
    except subprocess.TimeoutExpired:
        report.failures.append(f"{case.name} did not finish compiling within 300 seconds")
        return
    if finished.returncode != 0:
        tail = "\n".join((finished.stdout + finished.stderr).splitlines()[-20:])
        report.failures.append(
            f"{case.name} ({case.picture_class}) failed to compile from the flat "
            f"archive, exit {finished.returncode}:\n{tail}"
        )
        return
    pdf, stream, record = (room / f"{job}.pdf", room / f"{job}.tnlog", room / f"{job}.fls")
    if not pdf.is_file() or pdf.stat().st_size == 0:
        report.failures.append(f"{case.name} produced no PDF")
        return
    if not stream.is_file() or not stream.read_text(encoding="utf-8").strip():
        report.failures.append(f"{case.name} produced no event stream, so it drew nothing to read")
        return
    if not record.is_file():
        report.failures.append(f"{case.name} wrote no input record to read")
        return
    opened = recorded_inputs(record)
    flat = room.resolve()
    strangers = repository_inputs(opened, room, flat)
    report.require(
        not strangers,
        f"{case.name} read {sorted(set(strangers))} from the repository, so the "
        "flat archive did not answer for the run",
    )
    # That the package answered at all is already established above: the event
    # stream is written by tenkz and by nothing else, so a run that reached
    # this line loaded it. What is left to read is where it was loaded from.
    # There is deliberately no assertion that the list is non-empty; it could
    # not fail, and an assertion that cannot fail reads as coverage.
    answered = [path for path in opened if Path(path).name in carried]
    report.require(
        not foreign_runtime_files(answered, room, flat),
        f"{case.name} resolved a runtime file outside the flat archive, so an "
        "installed copy answered for it",
    )
    events = stream.read_text(encoding="utf-8")
    report.require(
        re.search(case.emits, events) is not None,
        f"{case.name} compiled but its stream records no {case.picture_class} "
        f"picture: nothing matches {case.emits!r}",
    )
    if case.absent:
        report.require(
            re.search(case.absent, events) is None,
            f"{case.name} records {case.absent!r}, which a {case.picture_class} "
            "picture does not write",
        )
    try:
        read_back = subprocess.run(
            [sys.executable, str(audit), str(stream), str(room / read)],
            cwd=room, capture_output=True, text=True, timeout=300,
        )
    except subprocess.TimeoutExpired:
        report.failures.append(
            f"{case.name}: the event audit did not finish within 300 seconds"
        )
        return
    if read_back.returncode != 0:
        tail = "\n".join((read_back.stdout + read_back.stderr).splitlines()[-15:])
        report.failures.append(f"{case.name} failed the event audit:\n{tail}")


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


def command_offline(require_engine: bool) -> int:
    """Build the archive and compile the picture classes against its flat."""

    with tempfile.TemporaryDirectory(prefix="tenkz-ctan-offline-") as directory:
        archive, _, _ = build(Path(directory) / "out")
        report = check_offline(archive, require_engine)
    print(f"  {report.status:4s} {report.name}")
    for note in report.notes:
        print(f"         {note}")
    if report.skipped:
        print(f"         skipped: {report.skipped}")
    for failure in report.failures:
        for line in failure.splitlines():
            print(f"         {line}")
    return 1 if report.failures else 0


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
        check_dependencies(closure, manifest),
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
        for name in ("permissions", "debris", "arxiv", "determinism", "clean-install", "offline"):
            skipped = Report(name)
            skipped.skipped = f"the staged material is not complete ({len(blocked)} finding(s))"
            reports.append(skipped)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz-ctan-check-") as directory:
            destination = keep if keep is not None else Path(directory) / "out"
            archive, _, digest = build(destination)
            reports.append(check_permissions(destination / PACKAGE))
            reports.append(check_debris(destination / PACKAGE))
            reports.append(check_arxiv(destination / PACKAGE, closure))
            reports.append(check_determinism(release))
            reports.append(check_smoke(archive, require_smoke))
            reports.append(check_offline(archive, require_smoke))
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
    offline = commands.add_parser(
        "offline", help="compile the picture classes against the unpacked flat"
    )
    offline.add_argument(
        "--require-engine",
        action="store_true",
        help="fail rather than skip when no TeX engine is installed",
    )
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
    if arguments.command == "offline":
        return command_offline(arguments.require_engine)
    if arguments.command == "sync":
        return command_sync()
    return command_check(arguments.require_smoke, arguments.out)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
