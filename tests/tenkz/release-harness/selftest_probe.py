#!/usr/bin/env python3
"""The one synthetic program the supervisor self-test drives.

Each mode exercises one property of the hermetic view or one branch of the
supervisor's outcome classification. The probe is never in the release-test
inventory; `selftest.py` builds synthetic inventory entries for it and checks
the outcome against the pinned expectations in the support tree.

Modes that assert something about the view report through the same protocol as
a real release test, so a broken view is reported as an assertion failure with
the synthetic fingerprint rather than as a crash.
"""

from __future__ import annotations

import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, output_directory  # noqa: E402


FINGERPRINT = "5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e"


def test_id() -> str:
    """The synthetic entry id `selftest.py` gave this run, derived from the mode."""

    return f"supervisor-selftest-{sys.argv[1] if len(sys.argv) > 1 else 'unknown'}"

# Exposed to every command: the pinned trees, the inventory, and the four
# canonical artifacts.  Nothing else in the repository may be reachable.
DECLARED = (
    "tests/tenkz/release-harness/harnesslib.py",
    "tests/tenkz/release-support/tool-profile.toml",
    "tests/tenkz/release-tests.toml",
    "tex/tenkz/tenkz.sty",
    "docs/tenkz/TNLOG.md",
)
UNDECLARED = (
    "scripts/check_tenkz_policy.py",
    "docs/tenkz/SOAK-1.0.md",
    "tests/tenkz/census-baseline.json",
    "lakefile.toml",
    "TNLean.lean",
)


def check(condition: object, reason: str) -> None:
    assert_that(
        condition,
        test_id=test_id(),
        failure_fingerprint=FINGERPRINT,
        reason=reason,
    )


def mode_isolation() -> None:
    absent = [path for path in DECLARED if not Path(path).exists()]
    check(not absent, f"the view is missing declared entries {absent!r}")
    present = [path for path in UNDECLARED if Path(path).exists()]
    check(not present, f"the view exposes undeclared entries {present!r}")


def mode_environment() -> None:
    # The supervisor sets exactly these. An operating system may inject others
    # into any child — macOS adds `__CF_USER_TEXT_ENCODING` — so the assertion
    # is that nothing beyond the declared set carries a path. That is the rule
    # the ledger states: no inherited repository-path variables.
    declared = {
        "PATH",
        "LC_ALL",
        "LANG",
        "TZ",
        "HOME",
        "TENKZ_TEST_OUTPUT",
        "PYTHONDONTWRITEBYTECODE",
    }
    missing = sorted(declared - set(os.environ))
    check(not missing, f"the environment is missing {missing!r}")
    leaked = sorted(
        name
        for name, value in os.environ.items()
        if name not in declared and "/" in value
    )
    check(not leaked, f"the environment carries inherited path variables {leaked!r}")
    check(os.environ.get("LC_ALL") == "C", "LC_ALL is not the fixed locale")
    check(os.environ.get("TZ") == "UTC", "TZ is not the fixed timezone")
    repository_directories = [
        entry
        for entry in os.environ["PATH"].split(os.pathsep)
        if "release-harness" in entry or "release-support" in entry
    ]
    check(
        not repository_directories,
        f"PATH reaches into the pinned trees at {repository_directories!r}",
    )


def mode_readonly() -> None:
    subject = Path("tex/tenkz/tenkz.sty")
    try:
        with subject.open("a", encoding="utf-8"):
            writable = True
    except OSError:
        writable = False
    check(not writable, "a declared subject is writable inside the view")
    probe = output_directory() / "writable-probe"
    probe.write_text("ok\n", encoding="utf-8")
    check(probe.read_text(encoding="utf-8") == "ok\n", "the output mount is not writable")
    probe.unlink()


def main() -> int:
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode == "pass":
        return 0
    if mode == "assertion":
        check(False, "the probe reports its one synthetic assertion failure")
    if mode == "unrelated-exit":
        return 3
    if mode == "exit-without-receipt":
        return 10
    if mode == "isolation":
        mode_isolation()
        return 0
    if mode == "environment":
        mode_environment()
        return 0
    if mode == "readonly":
        mode_readonly()
        return 0
    if mode == "timeout":
        time.sleep(30)
        return 0
    print(f"unknown probe mode {mode!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
