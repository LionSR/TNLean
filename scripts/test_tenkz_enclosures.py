#!/usr/bin/env python3
"""Grid enclosure test — retired with the grid subdivision machinery.

The grid frontend was deleted in the tenkz surface swap (9d0dd18);
kernel-region outline events are covered by the kernel-knot probes.
This stub exists because the CI workflow (pr-ci.yml) still references
the script and the bot token cannot edit workflow files.
"""

import sys


def main() -> int:
    print("test_tenkz_enclosures: skipped (grid surface retired)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
