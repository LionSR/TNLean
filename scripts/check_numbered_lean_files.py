#!/usr/bin/env python3
"""Reject new numbered-sequel names among tracked production Lean modules.

The debt allowlist is a ratchet: existing numbered sequel files may remain, but
new entries fail, and removed or concept-renamed files must be removed from the
allowlist in the same change.  Genuine mathematical/source numbers belong in
``SEMANTIC_EXCEPTIONS`` with a path-specific explanation.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

NUMBERED_STEM = re.compile(r"\d+[A-Za-z]?$")
PRODUCTION_ROOT = "TNLean/"
ARCHIVE_ROOT = "TNLean/Archive/"

# Existing structural debt only.  Never add a new path: split into modules named
# for their mathematical responsibility, then use a concept-named aggregator.
NUMBERED_DEBT_ALLOWLIST: frozenset[str] = frozenset(
    {
        "TNLean/MPS/Periodic/Overlap/Case1.lean",
        "TNLean/MPS/Periodic/Overlap/Case2.lean",
        "TNLean/MPS/Periodic/Overlap/Case3.lean",
        "TNLean/PEPS/CoherentFrameInstance2.lean",
        "TNLean/PEPS/NormalSquareFundamentalTheorem2.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite10.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite11.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite2.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite3.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite4.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite5.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite6.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite7.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite8.lean",
        "TNLean/PEPS/RegionBlock/CoarseThreeSite9.lean",
        "TNLean/PEPS/RegionBlock/GaugeInjectivity2.lean",
        "TNLean/PEPS/RegionBlock/Recovery10.lean",
        "TNLean/PEPS/RegionBlock/Recovery11.lean",
        "TNLean/PEPS/RegionBlock/Recovery2.lean",
        "TNLean/PEPS/RegionBlock/Recovery3.lean",
        "TNLean/PEPS/RegionBlock/Recovery4.lean",
        "TNLean/PEPS/RegionBlock/Recovery5.lean",
        "TNLean/PEPS/RegionBlock/Recovery6.lean",
        "TNLean/PEPS/RegionBlock/Recovery7.lean",
        "TNLean/PEPS/RegionBlock/Recovery8.lean",
        "TNLean/PEPS/RegionBlock/Recovery9.lean",
        "TNLean/PEPS/RegionBlock/ThreeBlockResonate2.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityGeneral2.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap2.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3b.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap4.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap5.lean",
        "TNLean/PEPS/RegionBlock/UnionInjectivityOverlap6.lean",
        "TNLean/PEPS/TorusFundamentalTheorem2.lean",
        "TNLean/PEPS/TorusWindowChain2.lean",
        "TNLean/PEPS/TorusWindowChain3.lean",
        "TNLean/PEPS/TorusWindowChain4.lean",
        "TNLean/PEPS/TorusWindowChain5.lean",
        "TNLean/PEPS/TorusWindowChain6.lean",
        "TNLean/PEPS/TorusWindowPeel2.lean",
        "TNLean/PEPS/TorusWindowPeel3.lean",
        "TNLean/PEPS/TorusWindowPeel4.lean",
    }
)

# These suffixes identify mathematical objects or source labels, not the order
# in which a proof was split.  Each exception is exact and reviewable.
SEMANTIC_EXCEPTIONS: dict[str, str] = {
    "TNLean/Channel/FixedPoint/WolfTheorem614.lean":
        "Wolf's theorem 6.14 is the source result formalized by this module.",
    "TNLean/MPS/Examples/ZMod2.lean":
        "ZMod 2 is the mathematical coefficient group used by the example.",
    "TNLean/MPS/MPDO/GroupedFigure8.lean":
        "Figure 8 is the source-paper figure whose grouped construction is formalized.",
    "TNLean/MPS/Periodic/Symmetry/Corollary41.lean":
        "Corollary 4.1 is the source result formalized by this module.",
}

SPLIT_GUIDANCE = (
    "Choose names for mathematical responsibilities (for example, "
    "BoundaryRecovery.lean), move shared definitions into a family Basic.lean "
    "module, and use a concept-named import aggregator. Do not continue a proof "
    "as Foo2.lean/Foo3.lean."
)


def _tracked_production_lean_files(root: Path) -> set[str]:
    """Return Git-tracked, non-archive Lean files below ``TNLean/``."""
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", "TNLean"],
        check=True,
        stdout=subprocess.PIPE,
    )
    paths = result.stdout.decode("utf-8").split("\0")
    return {
        path
        for path in paths
        if path.startswith(PRODUCTION_ROOT)
        and not path.startswith(ARCHIVE_ROOT)
        and path.endswith(".lean")
    }


def _has_numbered_suffix(path: str) -> bool:
    return NUMBERED_STEM.search(Path(path).stem) is not None


def check_numbered_files(
    root: Path,
    debt_allowlist: frozenset[str] = NUMBERED_DEBT_ALLOWLIST,
    semantic_exceptions: dict[str, str] = SEMANTIC_EXCEPTIONS,
) -> int:
    """Check the numbered-name ratchet and return a process exit status."""
    try:
        tracked = _tracked_production_lean_files(root)
    except (subprocess.CalledProcessError, UnicodeDecodeError) as error:
        print(f"::error title=Numbered Lean file check failed::git ls-files failed: {error}")
        return 1

    errors: list[str] = []
    overlap = debt_allowlist & semantic_exceptions.keys()
    for path in sorted(overlap):
        errors.append(f"{path}: listed as both structural debt and a semantic exception")

    for path in sorted(debt_allowlist):
        if path not in tracked:
            errors.append(
                f"{path}: stale debt allowlist entry; remove it now that the tracked "
                "production file is gone"
            )
        elif not _has_numbered_suffix(path):
            errors.append(f"{path}: no longer has a numbered suffix; remove its debt entry")

    for path, reason in sorted(semantic_exceptions.items()):
        if not reason.strip():
            errors.append(f"{path}: semantic exception has no explanation")
        if path not in tracked:
            errors.append(f"{path}: stale semantic exception; remove or update it")
        elif not _has_numbered_suffix(path):
            errors.append(f"{path}: semantic exception is unnecessary; remove it")

    numbered = {path for path in tracked if _has_numbered_suffix(path)}
    unexplained = numbered - debt_allowlist - semantic_exceptions.keys()
    for path in sorted(unexplained):
        errors.append(
            f"{path}: new numbered-sequel filename; name the module for what it proves"
        )

    for message in errors:
        path = message.split(":", 1)[0]
        print(f"::error file={path},title=Numbered Lean module policy::{message}")

    debt_present = len(numbered & debt_allowlist)
    semantic_present = len(numbered & semantic_exceptions.keys())
    print(
        f"Checked {len(tracked)} tracked production Lean files: "
        f"{debt_present} numbered debt, {semantic_present} semantic exceptions, "
        f"{len(unexplained)} new violations."
    )
    if errors:
        print(f"Split guidance: {SPLIT_GUIDANCE}")
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject new numbered-sequel names in tracked production Lean modules."
    )
    parser.add_argument("--root", type=Path, default=Path("."), help="Repository root")
    args = parser.parse_args()
    return check_numbered_files(args.root.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
