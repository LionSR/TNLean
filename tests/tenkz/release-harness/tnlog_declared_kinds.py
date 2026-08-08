#!/usr/bin/env python3
"""The event-kind declaration, as two independent assertions.

`TNLOG.md` is the event-format declaration named by `DESIGN.md`'s
`release_event_format`, and a declaration that has drifted from the reader is
worse than none: it tells a consumer that a kind is part of the surface when
the canonical reader has no schema for it, or hides a kind the reader knows.
The declaration's `tenkz-event-kinds-v1` block carries the set; this assertion
holds it equal to `FIELD_VALIDATORS`.
"""

from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, load_module, read  # noqa: E402


ASSERTIONS = {
    "declaration": (
        "tnlog-declaration-block-parses",
        "db1f1014a9d1791c035590e01900c4ed4a1780de55ebc893ac69a748904dcf64",
    ),
    "kinds": (
        "tnlog-declared-kinds-match-the-reader",
        "bae39735591cfdbdf20376e84041aec4d57f7c5b004e5addce6f5a3fa24e5cf3",
    ),
}
SUBJECT = "scripts/tenkzlib/tnlog.py"
DECLARATION = "docs/tenkz/TNLOG.md"
BLOCK = re.compile(
    r"^```toml[ \t]+tenkz-event-kinds-v1[ \t]*\n(.*?)^```[ \t]*$",
    re.MULTILINE | re.DOTALL,
)


def parsed_block() -> tuple[dict | None, str]:
    """The declaration's kind block, or None with the reason it did not parse."""

    blocks = BLOCK.findall(read(DECLARATION))
    if len(blocks) != 1:
        return None, f"{DECLARATION} carries {len(blocks)} kind blocks, not exactly one"
    try:
        table = tomllib.loads(blocks[0])
    except tomllib.TOMLDecodeError as error:
        return None, f"{DECLARATION} kind block is not valid TOML: {error}"
    schema = table.get("schema")
    if not isinstance(schema, int) or isinstance(schema, bool) or schema != 1:
        return None, f"{DECLARATION} kind block declares schema {schema!r}, not the integer 1"
    if not isinstance(table.get("reader_table"), list):
        return None, f"{DECLARATION} kind block has no reader_table list"
    return table, ""


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode not in ASSERTIONS:
        print(f"unknown assertion {mode!r}", file=sys.stderr)
        return 2
    test_id, fingerprint = ASSERTIONS[mode]
    table, reason = parsed_block()

    if mode == "declaration":
        assert_that(
            table is not None,
            test_id=test_id,
            failure_fingerprint=fingerprint,
            reason=reason,
        )
        return 0

    # The declaration assertion owns the parse; this one owns the kind set. A
    # block that does not parse cannot be compared, and saying so is not the
    # same failure as a set that genuinely differs.
    if table is None:
        print(f"skipping: {reason}", file=sys.stderr)
        return 2
    declared = sorted(table["reader_table"])
    tabled = sorted(load_module(SUBJECT).FIELD_VALIDATORS)
    assert_that(
        declared == tabled,
        test_id=test_id,
        failure_fingerprint=fingerprint,
        reason=(
            f"{DECLARATION} declares reader kinds {declared!r} while {SUBJECT} "
            f"tables {tabled!r}"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
