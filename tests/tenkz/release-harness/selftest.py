#!/usr/bin/env python3
"""The supervisor self-test.

`docs/tenkz/SOAK-1.0.md` §Release payload evidence requires a closed self-test
suite from the pinned support tree, run against pinned synthetic fixtures,
before the campaign may be armed. Its receipt binds the code and support trees,
the output mount, the environment, the access denials, the tool fingerprints,
and the completion of every isolation probe.

The suite drives `selftest_probe.py` through the real supervisor and compares
each outcome with `tests/tenkz/release-support/selftest-expectations.toml`. It
touches neither the release-test inventory nor any release tag, so it runs on
every pull request rather than only at activation, and a change that quietly
weakened the view would be caught by the isolation probe on that run.
"""

from __future__ import annotations

import json
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from supervisor import (  # noqa: E402
    ROOT,
    SupervisorError,
    Test,
    computed_pins,
    observe,
    read_policy,
    resolve_tool,
    tool_profile,
)


EXPECTATIONS = "tests/tenkz/release-support/selftest-expectations.toml"
PROBE = "tests/tenkz/release-harness/selftest_probe.py"
PROBE_SUBJECT = "tex/tenkz/tenkz.sty"
PROBE_FIXTURE = "docs/tenkz/TNLOG.md"


def synthetic(probe: dict, fingerprint: str) -> Test:
    """One synthetic inventory entry, built here rather than read from the pins."""

    return Test(
        id=f"supervisor-selftest-{probe['id']}",
        surface="tex-api",
        failure_fingerprint=fingerprint,
        runner="python3",
        path=PROBE,
        args=(probe["id"],),
        program_paths=(PROBE_SUBJECT,),
        fixture_paths=(PROBE_FIXTURE,),
        timeout_seconds=probe["timeout_seconds"],
    )


def run(root: Path = ROOT) -> int:
    policy = read_policy(root)
    document = tomllib.loads((root / EXPECTATIONS).read_text(encoding="utf-8"))
    if document.get("schema") != 1:
        print("FAIL: self-test expectations have an unknown schema", file=sys.stderr)
        return 1
    fingerprint = document["synthetic_fingerprint"]

    completed: list[str] = []
    failures: list[str] = []
    for probe in document["probe"]:
        test = synthetic(probe, fingerprint)
        expected = probe["outcome"]
        try:
            receipt = observe(test, policy, root)
            observed = receipt["assertion_result"]
        except SupervisorError as error:
            observed = "fails-closed"
            message = probe.get("message", "")
            if message and message not in str(error):
                failures.append(
                    f"{probe['id']}: failed closed with {str(error)!r}, which does "
                    f"not carry the expected {message!r}"
                )
                continue
        if observed != expected:
            failures.append(f"{probe['id']}: expected {expected}, observed {observed}")
            continue
        completed.append(probe["id"])

    pins = computed_pins(policy, root)
    receipt = {
        "schema": 1,
        "code_tree": pins["release_test_code_tree"],
        "support_tree": pins["release_test_support_tree"],
        "output_mount": "/tenkz-output",
        "tool_fingerprints": {
            name: resolve_tool(name, pattern, root)[1]
            for name, pattern in sorted(tool_profile(root).items())
        },
        "probes_completed": completed,
    }
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        return 1
    print(json.dumps(receipt, indent=2, sort_keys=True))
    print(f"PASS: {len(completed)} supervisor isolation probe(s) completed")
    return 0


def main() -> int:
    try:
        return run()
    except (SupervisorError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
