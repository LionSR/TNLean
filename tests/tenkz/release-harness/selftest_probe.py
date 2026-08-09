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

import json
import os
import subprocess
import sys
import time
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from harnesslib import assert_that, output_directory  # noqa: E402


FINGERPRINT = "5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e"


def test_id() -> str:
    """The synthetic entry id `selftest.py` gave this run, derived from the mode."""

    return f"supervisor-selftest-{sys.argv[1] if len(sys.argv) > 1 else 'unknown'}"

# The pinned manifest of everything this run may see, read from the support
# tree, which is itself exposed.  The probe compares it with the *complete*
# view rather than sampling a handful of paths: sampling passes whenever a
# regression exposes something the sample forgot to name, and this probe is the
# activation evidence that the access denials hold.
MANIFEST = "tests/tenkz/release-support/selftest-expectations.toml"
TOOL_PROFILE = "tests/tenkz/release-support/tool-profile.toml"


def check(condition: object, reason: str) -> None:
    assert_that(
        condition,
        test_id=test_id(),
        failure_fingerprint=FINGERPRINT,
        reason=reason,
    )


def allowed_view() -> tuple[tuple[str, ...], tuple[str, ...]]:
    document = tomllib.loads(Path(MANIFEST).read_text(encoding="utf-8"))
    view = document["view"]
    return tuple(view["roots"]), tuple(view["files"])


def mode_isolation() -> None:
    roots, files = allowed_view()

    absent = [path for path in files if not Path(path).exists()]
    check(not absent, f"the view is missing declared entries {absent!r}")
    missing_roots = [root for root in roots if not Path(root).is_dir()]
    check(not missing_roots, f"the view is missing pinned trees {missing_roots!r}")

    # Every regular file anywhere in the view must be inside a pinned tree or
    # be one of the named blobs. Anything else entered the view undeclared.
    unexpected = sorted(
        str(path)
        for path in Path(".").rglob("*")
        if path.is_file()
        and str(path) not in files
        and not any(str(path).startswith(f"{root}/") for root in roots)
    )
    check(
        not unexpected,
        f"the view exposes {len(unexpected)} undeclared entr(ies): {unexpected[:10]!r}",
    )


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

    # PATH must name the allowlist, not a directory that happens to contain
    # it. A CPython install ships `pip`, `pydoc`, and versioned interpreters
    # beside `python3`, so putting the interpreter's parent on PATH would hand
    # the command every one of them un-fingerprinted.
    allowed = set(tomllib.loads(Path(TOOL_PROFILE).read_text(encoding="utf-8"))["tool"])
    reachable: set[str] = set()
    for entry in os.environ["PATH"].split(os.pathsep):
        directory = Path(entry)
        if directory.is_dir():
            reachable.update(item.name for item in directory.iterdir())
    check(
        reachable == allowed,
        f"PATH reaches {sorted(reachable - allowed)!r} beyond the tool allowlist "
        f"{sorted(allowed)!r}",
    )


def refused(action) -> bool:
    """Run one mutation and report whether the view refused it."""

    try:
        action()
    except OSError:
        return True
    return False


def mode_readonly() -> None:
    # Appending to a declared subject is the shallow half of the guarantee.
    subject = Path("tex/tenkz/tenkz.sty")
    check(
        refused(lambda: subject.open("a", encoding="utf-8").close()),
        "a declared subject is writable inside the view",
    )

    # The deep half: a writable directory permits create, rename, and unlink,
    # so a command could delete a declared subject and put its own bytes at the
    # same path while every file in the view still reads mode 444. Each probe
    # below mutates a *directory*, not a file, and each must be refused.
    directory = Path("tex/tenkz")
    intruder = directory / "intruder.sty"
    check(
        refused(lambda: intruder.write_text("x\n", encoding="utf-8")),
        f"a new file can be created under the read-only subject tree {directory}",
    )
    check(
        refused(lambda: (directory / "intruder-dir").mkdir()),
        f"a new directory can be created under {directory}",
    )
    check(
        refused(lambda: subject.rename(directory / "renamed.sty")),
        f"a declared subject can be renamed inside {directory}",
    )
    check(
        refused(subject.unlink),
        f"a declared subject can be deleted from {directory}",
    )
    check(
        subject.exists() and not intruder.exists(),
        f"{directory} was mutated despite refusing every recorded attempt",
    )

    # The output mount is the one writable path.
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
    if mode == "bool-schema":
        # A receipt whose `schema` is JSON `true` must not be read as version 1
        # merely because Python considers `True == 1`.
        receipt = output_directory() / "assertion-failure-v1.json"
        receipt.write_text(
            json.dumps(
                {
                    "schema": True,
                    "test_id": test_id(),
                    "failure_fingerprint": FINGERPRINT,
                    "completed": True,
                }
            )
            + "\n",
            encoding="utf-8",
        )
        return 10
    if mode == "orphan-timeout":
        # Leave a descendant running and then hang. The supervisor must bound
        # the whole process group, not just this process.
        subprocess.Popen([sys.executable, "-c", "import time; time.sleep(300)"])
        time.sleep(30)
        return 0
    print(f"unknown probe mode {mode!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
