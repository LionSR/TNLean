#!/usr/bin/env python3
"""The assertion protocol every atomic release test uses.

A release test states one compatibility assertion about one public surface and
reports one of two outcomes.  It exits zero when the assertion holds.  When the
assertion fails it writes the closed receipt at `$TENKZ_TEST_OUTPUT` and exits
exactly ten; `docs/tenkz/SOAK-1.0.md` §Release payload evidence fixes both the
receipt shape and the exit code, and the supervisor rejects any other pairing.

A test that wants to report two failure causes is two tests.  The fingerprint
in `tests/tenkz/release-tests.toml` names the one cause, so a second cause
reaching the same fingerprint would make the friction record unreadable.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path


RECEIPT_NAME = "assertion-failure-v1.json"
ASSERTION_EXIT = 10


def output_directory() -> Path:
    """The writable mount the supervisor provides, and the only writable path."""

    value = os.environ.get("TENKZ_TEST_OUTPUT")
    if not value:
        print("TENKZ_TEST_OUTPUT is unset; run through the supervisor", file=sys.stderr)
        raise SystemExit(2)
    return Path(value)


def fail(test_id: str, failure_fingerprint: str, reason: str) -> None:
    """Record the sole assertion failure and leave with the pinned exit code."""

    receipt = {
        "schema": 1,
        "test_id": test_id,
        "failure_fingerprint": failure_fingerprint,
        "completed": True,
    }
    destination = output_directory() / RECEIPT_NAME
    temporary = destination.with_suffix(".partial")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    temporary.replace(destination)
    print(reason, file=sys.stderr)
    raise SystemExit(ASSERTION_EXIT)


def assert_that(
    condition: object,
    *,
    test_id: str,
    failure_fingerprint: str,
    reason: str,
) -> None:
    """Hold the assertion, or record its one failure."""

    if not condition:
        fail(test_id, failure_fingerprint, reason)


def read(relative: str) -> str:
    """Read one declared subject from the view, by its repository-relative path."""

    return Path(relative).read_text(encoding="utf-8")
