#!/usr/bin/env python3
"""The package's version declaration, as two independent assertions.

`RELEASE-POLICY.md` §3: the version string lives in one place, the
`\\ProvidesPackage` line of `tex/tenkz/tenkz.sty`, and the manual, change
record, event-format declaration, and release manifest are all checked against
it.

Two things can be wrong with that line and they need separate fingerprints,
because a friction record names the fingerprint and one that stood for both
could not tell a reader whether to fix a duplicated declaration or a malformed
version:

    cardinality   the file carries exactly one declaration
    syntax        every declaration it carries parses as date-and-version

The two are independent. A file with two well-formed declarations fails the
first and passes the second; a file with one malformed declaration does the
reverse.
"""

from __future__ import annotations

import re
import sys
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, read  # noqa: E402


SUBJECT = "tex/tenkz/tenkz.sty"
DECLARATION = re.compile(r"^\\ProvidesPackage\{tenkz\}\[([^]]*)\]", re.MULTILINE)
PAYLOAD = re.compile(
    r"(?P<y>[0-9]{4})/(?P<m>[0-9]{2})/(?P<d>[0-9]{2}) v[0-9]+\.[0-9]+(?:\.[0-9]+)? \S.*"
)


def well_formed(payload: str) -> bool:
    """The payload parses, and its date is a real calendar date.

    Counting digits is not enough: `2026/99/99` has the right shape and cannot
    be the ISO calendar date the release manifest declares against.
    """

    match = PAYLOAD.fullmatch(payload)
    if match is None:
        return False
    try:
        date(int(match["y"]), int(match["m"]), int(match["d"]))
    except ValueError:
        return False
    return True

ASSERTIONS = {
    "cardinality": (
        "tex-api-package-version-declared-once",
        "6975c749deed3d812904570c3ea9fc4d14fe2f002c5ecff56b66e7aaba8e6e21",
    ),
    "syntax": (
        "tex-api-package-version-well-formed",
        "4c75affd12f21b0ee2e262ccce6495382baed3cf11e1d9ac96c5bed05d8a3d36",
    ),
}


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ASSERTIONS:
        print(f"unknown assertion {mode!r}", file=sys.stderr)
        return 2
    test_id, fingerprint = ASSERTIONS[mode]
    declarations = DECLARATION.findall(read(SUBJECT))

    if mode == "cardinality":
        assert_that(
            len(declarations) == 1,
            test_id=test_id,
            failure_fingerprint=fingerprint,
            reason=(
                f"{SUBJECT} must carry exactly one \\ProvidesPackage{{tenkz}} line; "
                f"found {len(declarations)}"
            ),
        )
        return 0

    malformed = [payload for payload in declarations if not well_formed(payload)]
    assert_that(
        not malformed,
        test_id=test_id,
        failure_fingerprint=fingerprint,
        reason=(
            f"{SUBJECT} declares {malformed!r}, which is not spelled "
            f"[YYYY/MM/DD vMAJOR.MINOR[.PATCH] description] with a real date"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
