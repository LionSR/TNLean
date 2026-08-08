#!/usr/bin/env python3
"""The package declares exactly one well-formed version.

`RELEASE-POLICY.md` §3: the version string lives in one place, the
`\\ProvidesPackage` line of `tex/tenkz/tenkz.sty`, and the manual, change
record, event-format declaration, and release manifest are all checked against
it. A second declaration, a missing date, or a version the manifest grammar
cannot read makes every one of those checks meaningless, so this is the
assertion they all rest on.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, read  # noqa: E402


TEST_ID = "tex-api-package-version-declared"
FINGERPRINT = "aa16d2f161b986789b582d211b59344b66171a386e3fcfcc259aafb2ba48e1d8"
SUBJECT = "tex/tenkz/tenkz.sty"
DECLARATION = re.compile(r"^\\ProvidesPackage\{tenkz\}\[([^]]*)\]", re.MULTILINE)
PAYLOAD = re.compile(r"[0-9]{4}/[0-9]{2}/[0-9]{2} v[0-9]+\.[0-9]+(?:\.[0-9]+)? \S.*")


def main() -> int:
    declarations = DECLARATION.findall(read(SUBJECT))
    assert_that(
        len(declarations) == 1 and PAYLOAD.fullmatch(declarations[0]) is not None,
        test_id=TEST_ID,
        failure_fingerprint=FINGERPRINT,
        reason=(
            f"{SUBJECT} must carry exactly one \\ProvidesPackage line spelled "
            f"[YYYY/MM/DD vMAJOR.MINOR[.PATCH] description]; found {declarations!r}"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
