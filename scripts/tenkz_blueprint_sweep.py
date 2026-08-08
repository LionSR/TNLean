#!/usr/bin/env python3
"""Audit the event stream of every tenkz picture in the blueprint.

The web build compiles each picture standalone and caches it by a content
hash of its own source plus the library's (`blueprint/src/Packages/
tenkz_pic.py`), leaving one `.tnlog` per picture beside the SVG.  This sweep
walks the blueprint sources, asks that pipeline for each picture's stream,
and runs `tenkz_audit.py` over all of them, so a hard finding names the
chapter file and line it came from rather than a hash.

A picture whose stream is absent is compiled here; after `leanblueprint web`
every stream is already cached and the sweep is a read.

Usage: tenkz_blueprint_sweep.py [--src blueprint/src] [--quiet]
Exit status: 1 iff some picture's stream has a hard finding.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO / "blueprint/src/Packages"))

from tenkz_audit import Audit  # noqa: E402
from tenkzlib.texcase import strip_comments  # noqa: E402

# The environments plasTeX captures verbatim and renders as one unit.  Only
# the tenkz surface writes an event stream; `tikzcd` is drawn by tikz-cd.
UNIT_ENVIRONMENTS = ("tenkz",)


@dataclass(frozen=True)
class Unit:
    """One picture: where the source states it, and what it states."""

    path: Path
    line: int
    source: str


def scan_units(src_dir: Path) -> list[Unit]:
    """Every picture unit in the blueprint sources, in file order."""
    pattern = re.compile(
        r"\\begin\{(" + "|".join(UNIT_ENVIRONMENTS) + r")\}(.*?)\\end\{\1\}",
        re.S,
    )
    units: list[Unit] = []
    for path in sorted(src_dir.rglob("*.tex")):
        if any(part.startswith(".") for part in path.relative_to(src_dir).parts):
            continue  # the render cache holds generated copies, not sources
        text = path.read_text(encoding="utf-8")
        # A commented-out picture is not drawn, so it owns no stream; the
        # offsets of the surviving ones must still name their real lines.
        live = strip_comments(text)
        for match in pattern.finditer(live):
            name = match.group(1)
            unit = f"\\begin{{{name}}}{match.group(2)}\\end{{{name}}}"
            units.append(
                Unit(path, live.count("\n", 0, match.start()) + 1, unit)
            )
    return units


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
    for unit in units:
        where = f"{unit.path.relative_to(REPO)}:{unit.line}"
        log_path = tenkz_pic.unit_event_log(unit.source, svg_dir)
        if log_path is None:
            print(f"  MISSING {where}: no event stream and no SVG toolchain")
            failed.append(where)
            continue
        audit = Audit(log_path, None)
        audit.parse_log()
        audit.link_tex()
        audit.check_empty_pictures()
        audit.check_dialects()
        audit.check_kernel_crossings()
        audit.check_kernel_checks()
        audit.check_bbox_coverage()
        audit.check_label_overlaps()
        audit.check_equation_groups()
        audit.check_repeated_topology()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        advisories += sum(1 for f in audit.findings if f.severity == "ADV")
        if hard:
            failed.append(where)
        for finding in audit.findings:
            if finding.severity == "HARD" or not quiet:
                print(f"  {finding.severity:<4} [{finding.rule}] {where}: "
                      f"{finding.msg}")
    print(f"tenkz-blueprint-sweep: {len(units)} picture(s), "
          f"{len(failed)} with hard findings, {advisories} advisory(ies)")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
