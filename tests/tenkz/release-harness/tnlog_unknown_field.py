#!/usr/bin/env python3
"""The reader ignores an unknown optional field.

`DESIGN.md` `[event_format]`: `unknown_optional_fields = "ignore"`. This is the
rule that lets a minor release add a field to an existing event kind without
breaking a reader built against the previous minor. `TNLOG.md` §6 records that
the reader implements it by permissiveness rather than by a declared
optional-field set; either way, a reader that started rejecting an untabled
field would turn every such addition into a breaking change.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, load_module  # noqa: E402


TEST_ID = "tnlog-reader-ignores-unknown-fields"
FINGERPRINT = "4312555019ae1123120a0e29328272a20f876568c2f6d12a470cf3e5aea6648f"
SUBJECT = "scripts/tenkzlib/tnlog.py"
STREAM = [
    "picture|id=k1|lang=kernel|later-minor-field=value",
    "atom|id=atom-1|addr=(1,1)|kind=tn|another-later-field=value",
    "kernel-boundary|signature=open:w",
]




def main() -> int:
    reader = load_module(SUBJECT)
    findings: list[str] = []
    parsed = reader.parse_log(
        "\n".join(STREAM) + "\n",
        hard=lambda rule, where, message: findings.append(f"{rule}: {message}"),
    )
    invalid = [event.kind for event in parsed.events if not event.valid]
    assert_that(
        not findings and not invalid and len(parsed.valid_events) == len(STREAM),
        test_id=TEST_ID,
        failure_fingerprint=FINGERPRINT,
        reason=(
            f"{SUBJECT} rejected a stream carrying only untabled extra fields: "
            f"findings={findings!r}, invalid kinds={invalid!r}"
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
