#!/usr/bin/env python3
"""Every command the registry declares reaches the generated language reference.

`RELEASE-POLICY.md` §1 freezes the registry as the machine inventory of the TeX
surface and requires `chapters2/generated-language-reference.tex` to agree with
the manual. A command that lives in the registry but never reaches the
reference is a documented spelling the reader cannot find, which is the one
failure the manual-is-the-contract rule of #4163 exists to prevent.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, read  # noqa: E402


TEST_ID = "tex-api-registry-commands-reach-the-reference"
FINGERPRINT = "6b10bdfa0d4079c322990a4e9916416013a4c8a6f8ba47aa69d6905cd50d10b0"
REGISTRY = "tex/tenkz/tenkz-language-registry.tex"
REFERENCE = "docs/tenkz/chapters2/generated-language-reference.tex"
COMMAND_ROW = re.compile(r"\\__tenkz_language_registry_command:nnnnn\s*\{([^}]+)\}")


def main() -> int:
    declared = sorted(set(COMMAND_ROW.findall(read(REGISTRY))))
    reference = read(REFERENCE)
    missing = [
        name
        for name in declared
        if f"\\texttt{{\\textbackslash {name}}}" not in reference
    ]
    assert_that(
        declared and not missing,
        test_id=TEST_ID,
        failure_fingerprint=FINGERPRINT,
        reason=(
            f"{REFERENCE} omits registry command(s) {missing!r}"
            if declared
            else f"{REGISTRY} declares no command rows"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
