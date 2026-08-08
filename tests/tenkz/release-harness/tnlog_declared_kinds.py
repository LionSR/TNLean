#!/usr/bin/env python3
"""The declared reader table and the reader's own table are the same set.

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


TEST_ID = "tnlog-declared-kinds-match-the-reader"
FINGERPRINT = "bae39735591cfdbdf20376e84041aec4d57f7c5b004e5addce6f5a3fa24e5cf3"
SUBJECT = "scripts/tenkzlib/tnlog.py"
DECLARATION = "docs/tenkz/TNLOG.md"
BLOCK = re.compile(
    r"^```toml[ \t]+tenkz-event-kinds-v1[ \t]*\n(.*?)^```[ \t]*$",
    re.MULTILINE | re.DOTALL,
)




def declared_kinds() -> list[str] | None:
    blocks = BLOCK.findall(read(DECLARATION))
    if len(blocks) != 1:
        return None
    table = tomllib.loads(blocks[0])
    if table.get("schema") != 1:
        return None
    return sorted(table.get("reader_table", []))


def main() -> int:
    declared = declared_kinds()
    tabled = sorted(load_module(SUBJECT).FIELD_VALIDATORS)
    assert_that(
        declared == tabled,
        test_id=TEST_ID,
        failure_fingerprint=FINGERPRINT,
        reason=(
            f"{DECLARATION} declares reader kinds {declared!r} while {SUBJECT} "
            f"tables {tabled!r}"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
