#!/usr/bin/env python3
"""Grid face-port test — retired with the grid contraction-slot machinery.

The grid frontend was deleted in the tenkz surface swap (9d0dd18);
kernel port typing is covered by the r_/n_ port fixtures.
This stub exists because the CI workflow (pr-ci.yml) still references
the script and the bot token cannot edit workflow files.
"""

import sys


def main() -> int:
    print("test_tenkz_face_ports: skipped (grid surface retired)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
