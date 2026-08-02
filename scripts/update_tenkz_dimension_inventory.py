#!/usr/bin/env python3
"""Rewrite the reviewed RMP physical-dimension inventory."""

from pathlib import Path

from tenkz_rmp import DEFAULT_MANIFEST, load_manifest
from tenkzlib.dimensions import (
    CASE_DIMENSION_INVENTORY,
    case_dimension_inventory,
    scan_case_dimensions,
    write_dimension_inventory,
)


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    occurrences = []
    for target in load_manifest(DEFAULT_MANIFEST):
        occurrences.extend(
            scan_case_dimensions(
                target.case,
                (ROOT / target.case).read_text(encoding="utf-8"),
            )
        )
    inventory = case_dimension_inventory(occurrences)
    destination = ROOT / CASE_DIMENSION_INVENTORY
    write_dimension_inventory(destination, inventory)
    print(
        f"Updated {destination.relative_to(ROOT)} with "
        f"{sum(inventory.values())} dimensions in {len(inventory)} rows"
    )


if __name__ == "__main__":
    main()
