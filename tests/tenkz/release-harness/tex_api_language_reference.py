#!/usr/bin/env python3
"""The registry's command rows, as two independent assertions.

`RELEASE-POLICY.md` §1 freezes the registry as the machine inventory of the TeX
surface and requires `chapters2/generated-language-reference.tex` to agree with
the manual. A command that lives in the registry but never reaches the
reference is a documented spelling the reader cannot find, which is the one
failure the manual-is-the-contract rule of #4163 exists to prevent.

Two things can be wrong and they need separate fingerprints:

    extraction  the registry yields command rows at all
    coverage    every row it yields reaches the generated reference

An empty result would otherwise satisfy a coverage check vacuously, so a
friction record could not tell a reader whether the registry parser broke or
the reference fell behind.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, read, selected_assertion  # noqa: E402


SUBJECTS = {
    "extraction": (
        "tex-api-registry-declares-commands",
        "9848e1f6bf653612c61c5287b7e7ebb165a39224623b66b8ee8f4ddd26aee26b",
    ),
    "coverage": (
        "tex-api-registry-commands-reach-the-reference",
        "6b10bdfa0d4079c322990a4e9916416013a4c8a6f8ba47aa69d6905cd50d10b0",
    ),
}
REGISTRY = "tex/tenkz/tenkz-language-registry.tex"
REFERENCE = "docs/tenkz/chapters2/generated-language-reference.tex"
COMMAND_ROW = re.compile(r"\\__tenkz_language_registry_command:nnnnn\s*\{([^}]+)\}")
TEX_COMMENT = re.compile(r"(?<!\\)%.*")


def registry_rows() -> list[str]:
    """The command names the registry actually declares.

    Comments are stripped first. A row commented out with `%` is not in the
    executable registry, so counting it would let this assertion report that a
    removed public command is still declared — the precise failure the
    manual-is-the-contract rule exists to catch.
    """

    source = TEX_COMMENT.sub("", read(REGISTRY))
    return sorted(set(COMMAND_ROW.findall(source)))


def main() -> int:
    mode = sys.argv[1]
    test_id, fingerprint = selected_assertion(SUBJECTS)
    declared = registry_rows()

    if mode == "extraction":
        assert_that(
            bool(declared),
            test_id=test_id,
            failure_fingerprint=fingerprint,
            reason=(
                f"{REGISTRY} yielded no command rows; either the registry lost "
                f"its command declarations or their spelling changed"
            ),
        )
        return 0

    reference = read(REFERENCE)
    missing = [
        name
        for name in declared
        if f"\\texttt{{\\textbackslash {name}}}" not in reference
    ]
    assert_that(
        not missing,
        test_id=test_id,
        failure_fingerprint=fingerprint,
        reason=f"{REFERENCE} omits registry command(s) {missing!r}",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
