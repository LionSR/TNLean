#!/usr/bin/env python3
"""Audit the event stream of every tenkz picture in the blueprint.

The web build compiles a picture standalone and caches it by a content hash
of its own source plus the library's (`blueprint/src/Packages/tenkz_pic.py`),
leaving one `.tnlog` beside the SVG.  This sweep walks the blueprint sources,
asks that pipeline for each unit's stream, and runs `tenkz_audit.py` over all
of them, so a hard finding names the chapter file and line it came from
rather than a hash.

**The unit is the display, not the panel.**  A picture standing alone is its
own unit; a picture inside a displayed row (`tenkzequation`) is compiled with
the whole row, so one stream holds every panel of that display and the
equation checks have something to compare.  Compiling the panels apart would
leave every display's boundary unchecked, which is coverage this check would
be claiming and not performing.

How far the equation checks reach depends on what the display declares.  A
display written as `tenkzeq` stamps its scope into every panel record and the
hard group rules apply.  A display written with the blueprint's presentational
row states its relation only as typeset mathematics, so the panels are read
through the source `=` and a mismatch is advisory (`DESIGN.md`, "Equation
grouping").  The closing line states both counts: a run whose displays are all
presentational has performed no hard group check, and says so.

A unit whose stream is absent is compiled here; after `leanblueprint web`
every panel-sized stream is cached, and the display-sized ones are compiled
by this sweep.

Usage: tenkz_blueprint_sweep.py [--src blueprint/src] [--quiet]
Exit status: 1 iff some unit's stream has a hard finding.
"""

from __future__ import annotations

import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO / "blueprint/src/Packages"))

from tenkz_audit import Audit  # noqa: E402
from tenkzlib.texcase import (  # noqa: E402
    scan_picture_event_constructs,
    strip_comments,
)

# The rows that hold several panels around the mathematics between them.
# `tenkzeq` is the language's own equation scope; `tenkzequation` is the
# blueprint's presentational row, whose migration is #5693.
# TeX reads the space after a control word as part of it, so `\begin {tenkzeq}`
# opens the same environment; the shared construct scanner allows it and so
# must this, or a spaced wrapper would leave its panels ungrouped.
DISPLAYS = re.compile(
    r"\\begin\s*\{(tenkzeq|tenkzequation)\}(.*?)\\end\s*\{\1\}", re.S
)


@dataclass(frozen=True)
class Unit:
    """One audited compile: where the source states it, and what it states."""

    path: Path
    line: int
    source: str
    display: bool  # a whole row of panels rather than a lone picture


def scan_units(src_dir: Path) -> list[Unit]:
    """Every audit unit in the blueprint sources, in file order.

    A display holding at least one picture is one unit carrying all its
    panels; every picture outside every display is a unit of its own.  A
    `tenkzeq` display keeps its own environment, since the scope is what the
    hard checks read; a presentational row contributes its body, because the
    row is layout the audit has no use for and its macro is not available to
    a standalone compile.
    """
    units: list[Unit] = []
    for path in sorted(src_dir.rglob("*.tex")):
        if any(part.startswith(".") for part in path.relative_to(src_dir).parts):
            continue  # the render cache holds generated copies, not sources
        # A commented-out picture is not drawn, so it owns no stream; the
        # offsets of the surviving ones must still name their real lines.
        live = strip_comments(path.read_text(encoding="utf-8"))
        # The shared scanner owns picture syntax and matches begin against end
        # by nesting, so an outer picture keeps the inner one it contains.
        constructs = scan_picture_event_constructs(live)
        pictures = [
            construct for construct in constructs
            if not any(
                other.start < construct.start and construct.end <= other.end
                for other in constructs
            )
        ]
        found: list[Unit] = []
        covered: list[tuple[int, int]] = []
        for match in DISPLAYS.finditer(live):
            if not any(
                match.start() <= picture.start and picture.end <= match.end()
                for picture in pictures
            ):
                continue  # a row of prose or of tikz-cd: no stream to audit
            source = (
                match.group(0) if match.group(1) == "tenkzeq" else match.group(2)
            )
            found.append(
                Unit(path, live.count("\n", 0, match.start()) + 1, source, True)
            )
            covered.append((match.start(), match.end()))
        for picture in pictures:
            if any(start <= picture.start < end for start, end in covered):
                continue  # audited as a panel of its display
            found.append(
                Unit(
                    path,
                    live.count("\n", 0, picture.start) + 1,
                    live[picture.start:picture.end],
                    False,
                )
            )
        units.extend(sorted(found, key=lambda unit: unit.line))
    return units


def _relative(path: Path) -> Path:
    """The repository-relative name when there is one, else the path itself."""
    try:
        return path.relative_to(REPO)
    except ValueError:
        return path


def main(argv: list[str]) -> int:
    if "-h" in argv or "--help" in argv:
        print(__doc__.strip().splitlines()[0])
        print("usage: tenkz_blueprint_sweep.py [--src DIR] [--quiet]")
        return 0
    quiet = "--quiet" in argv
    src_dir = REPO / "blueprint/src"
    if "--src" in argv:
        src_dir = Path(argv[argv.index("--src") + 1]).resolve()

    import tenkz_pic

    svg_dir = src_dir / ".tenkz_svg_cache" / "sweep_svg"
    units = scan_units(src_dir)
    if not units:
        print(f"tenkz-blueprint-sweep: no pictures under {src_dir}")
        return 1
    failed: list[str] = []
    advisories = 0
    pictures = 0
    displays = 0
    scoped = 0
    with tempfile.TemporaryDirectory(prefix="tenkz_blueprint_sweep_") as tmp:
        for unit in units:
            where = f"{_relative(unit.path)}:{unit.line}"
            # Name the linked copy after the source it came from, so a
            # source-linked finding's bracket reads as the chapter it is about.
            source_path = Path(tmp) / f"{unit.path.stem}-{unit.line}.tex"
            # One figure that will not compile or convert must not take the
            # sweep down with it: the rest of the volume still has an answer.
            try:
                log_path = tenkz_pic.unit_event_log(unit.source, svg_dir)
            except (RuntimeError, OSError) as failure:
                print(f"  HARD [unit-compile] {where}: {failure}")
                failed.append(where)
                continue
            if log_path is None:
                print(f"  MISSING {where}: no event stream and no SVG toolchain")
                failed.append(where)
                continue
            # The unit's own source is what the log came from, so the
            # source-linked half of the audit reads exactly this display.
            source_path.write_text(unit.source, encoding="utf-8")
            audit = Audit(log_path, source_path)
            audit.parse_log()
            audit.link_tex()
            audit.check_empty_pictures()
            audit.check_dialects()
            audit.check_kernel_crossings()
            audit.check_kernel_checks()
            audit.check_bbox_coverage()
            audit.check_label_overlaps()
            audit.check_equation_groups()
            audit.check_equation_boundaries()
            audit.check_repeated_topology()
            pictures += len(audit.pictures)
            displays += 1 if unit.display else 0
            if unit.display and any(
                event.kind == "picture" and "scope" in event.attrs
                for event in audit.log_events
            ):
                scoped += 1
            hard = [f for f in audit.findings if f.severity == "HARD"]
            advisories += sum(1 for f in audit.findings if f.severity == "ADV")
            if hard:
                failed.append(where)
            for finding in audit.findings:
                if finding.severity == "HARD" or not quiet:
                    print(f"  {finding.severity:<4} [{finding.rule}] {where}: "
                          f"{finding.msg}")
    print(f"tenkz-blueprint-sweep: {pictures} picture(s) in {len(units)} unit(s), "
          f"{len(failed)} with hard findings, {advisories} advisory(ies)")
    print(f"  equation displays: {displays}; carrying a tenkzeq scope "
          f"(hard group checks): {scoped}; read through the source `=` "
          f"(advisory only): {displays - scoped}")
    if displays and not scoped:
        print("  NOTE: no blueprint display declares an equation scope, so no "
              "hard group check ran over the volume; the migration is #5693.")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
