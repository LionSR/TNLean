#!/usr/bin/env python3
"""Update the reviewed exact-site inventory for RMP case dimensions."""

from __future__ import annotations

import argparse
import difflib
import sys
from pathlib import Path
from typing import Callable, Iterable

from tenkz_rmp import DEFAULT_MANIFEST, RMPError, load_manifest
from tenkzlib.dimension_inventory import (
    DEFAULT_DIMENSION_INVENTORY,
    DimensionInventoryError,
    collect_dimension_inventory,
    format_dimension_inventory,
    format_dimension_inventory_counts,
    load_dimension_inventory,
)
from tenkzlib.dimensions import (
    DimensionOwnershipError,
    collect_dimension_report,
    validate_dimension_report,
)


REPO = Path(__file__).resolve().parent.parent


def update_dimension_inventory(
    repo: Path,
    case_paths: Iterable[Path],
    destination: Path,
    *,
    check: bool = False,
    emit: Callable[[str], None] = print,
) -> bool:
    """Validate ceilings, show the exact diff, and optionally write it."""
    paths = tuple(case_paths)
    # The updater must never bless a regression merely by recording it.  Run
    # every aggregate ceiling, comment, and benchmark-book check before even
    # considering a replacement inventory.
    validate_dimension_report(collect_dimension_report(repo, paths))
    inventory = collect_dimension_inventory(repo, paths)
    rendered = format_dimension_inventory(inventory)

    if destination.exists():
        # Refuse to paper over malformed or duplicate committed rows.
        load_dimension_inventory(destination)
        previous = destination.read_text(encoding="utf-8")
    else:
        previous = ""
    changed = previous != rendered
    if changed:
        diff = "\n".join(
            difflib.unified_diff(
                previous.splitlines(),
                rendered.splitlines(),
                fromfile=destination.as_posix(),
                tofile=destination.as_posix(),
                lineterm="",
            )
        )
        emit(diff)
    emit("RMP dimension inventory: " + format_dimension_inventory_counts(inventory))
    if not changed:
        emit("RMP dimension inventory is unchanged")
        return False
    if check:
        raise DimensionInventoryError(
            "RMP dimension inventory is stale; run "
            "python3 scripts/update_tenkz_dimension_inventory.py"
        )
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(rendered, encoding="utf-8")
    emit(f"updated {destination}")
    return True


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Review and update exact active RMP dimension owner sites."
    )
    result.add_argument(
        "--check", action="store_true", help="report drift without writing"
    )
    result.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    result.add_argument(
        "--output", type=Path, default=REPO / DEFAULT_DIMENSION_INVENTORY
    )
    return result


def main() -> int:
    args = parser().parse_args()
    manifest = args.manifest
    if not manifest.is_absolute():
        manifest = REPO / manifest
    destination = args.output
    if not destination.is_absolute():
        destination = REPO / destination
    try:
        targets = load_manifest(manifest)
        update_dimension_inventory(
            REPO,
            (target.case for target in targets),
            destination,
            check=args.check,
        )
    except (
        DimensionInventoryError,
        DimensionOwnershipError,
        OSError,
        RMPError,
        UnicodeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
