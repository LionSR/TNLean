#!/usr/bin/env python3
"""The supervisor self-test.

`docs/tenkz/SOAK-1.0.md` §Release payload evidence requires a closed self-test
suite from the pinned support tree, run against pinned synthetic fixtures,
before the campaign may be armed. Its receipt binds the code and support trees,
the output mount, the environment, the access denials, the tool fingerprints,
and the completion of every isolation probe.

The suite has two halves. The *probes* drive `selftest_probe.py` through the
real supervisor and check what a command sees from inside the view. The
*guards* call the supervisor's own entry points against synthetic filesystem
fixtures the suite builds and destroys, because the escapes they cover —
symlinks, special file modes, an incomplete receipt — cannot be staged from
inside a view that is supposed to reject them. Both halves compare against
`tests/tenkz/release-support/selftest-expectations.toml`.

Neither half touches the release-test inventory's pins or any release tag, so
the suite runs on every pull request rather than only at activation, and a
change that quietly weakened the view is caught on that run.
"""

from __future__ import annotations

import json
import os
import shutil
import sys
import tempfile
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from supervisor import (  # noqa: E402
    ROOT,
    SupervisorError,
    Test,
    computed_pins,
    expose,
    observe,
    read_policy,
    require_regular_file,
    require_tree_is_clean,
    resolve_tool,
    tool_profile,
)


EXPECTATIONS = "tests/tenkz/release-support/selftest-expectations.toml"
PROBE = "tests/tenkz/release-harness/selftest_probe.py"
PROBE_SUBJECT = "tex/tenkz/tenkz.sty"
PROBE_FIXTURE = "docs/tenkz/TNLOG.md"
ESCAPE_MARKER = "content-from-outside-the-repository\n"


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


# --------------------------------------------------------------------------
# Guards
# --------------------------------------------------------------------------
#
# Each guard stages one escape in a throwaway directory and requires the
# supervisor to refuse it. A guard whose staged escape the supervisor accepts
# is reported as `accepted`, which is always a self-test failure: these are the
# refusals the hermetic view is built out of, and a view that accepts them
# produces evidence a release would trust.


def outside_file(workspace: Path) -> Path:
    """One file outside the synthetic repository, standing in for /etc/hosts."""

    target = workspace / "outside" / "secret.txt"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(ESCAPE_MARKER, encoding="utf-8")
    return target


def guard_nested_symlink(workspace: Path) -> None:
    """A symlink one level down inside an exposed tree must not be followed.

    `shutil.copytree(symlinks=False)` dereferences such a link and writes its
    target's bytes into the view, so this guard fails against any harness that
    copies an exposed tree with `copytree`.
    """

    fake_root = workspace / "repository"
    tree = fake_root / "tex" / "tenkz" / "nested"
    tree.mkdir(parents=True)
    (fake_root / "tex" / "tenkz" / "plain.sty").write_text("ok\n", encoding="utf-8")
    os.symlink(outside_file(workspace), tree / "escape.sty")
    view = workspace / "view"
    view.mkdir()
    expose(fake_root, view, "tex/tenkz")


def guard_symlinked_program_path(workspace: Path) -> None:
    """A declared subject that is itself a symlink must be rejected."""

    fake_root = workspace / "repository"
    (fake_root / "tex" / "tenkz").mkdir(parents=True)
    os.symlink(outside_file(workspace), fake_root / "tex" / "tenkz" / "tenkz.sty")
    require_regular_file(fake_root, "tex/tenkz/tenkz.sty", "guard program path")


def guard_symlinked_parent(workspace: Path) -> None:
    """A declared subject reached through a symlinked directory must be rejected.

    The leaf is an ordinary regular file, so any check that looks only at the
    leaf accepts it. The escape is the parent.
    """

    fake_root = workspace / "repository"
    (fake_root / "tex").mkdir(parents=True)
    real = workspace / "elsewhere" / "tenkz"
    real.mkdir(parents=True)
    (real / "tenkz.sty").write_text(ESCAPE_MARKER, encoding="utf-8")
    os.symlink(real, fake_root / "tex" / "tenkz")
    require_regular_file(fake_root, "tex/tenkz/tenkz.sty", "guard program path")


def guard_special_entry(workspace: Path) -> None:
    """A named pipe inside an exposed tree must be rejected, not copied."""

    fake_root = workspace / "repository"
    tree = fake_root / "docs" / "tenkz"
    tree.mkdir(parents=True)
    os.mkfifo(tree / "pipe")
    require_tree_is_clean(fake_root, "docs/tenkz", "guard fixture path")


GUARDS = {
    "nested-symlink": guard_nested_symlink,
    "symlinked-program-path": guard_symlinked_program_path,
    "symlinked-parent": guard_symlinked_parent,
    "special-entry": guard_special_entry,
}


def run_guards(document: dict, failures: list[str]) -> list[str]:
    completed: list[str] = []
    for guard in document["guard"]:
        name = guard["id"]
        if name not in GUARDS:
            failures.append(f"{name}: the expectations name an unknown guard")
            continue
        workspace = Path(tempfile.mkdtemp(prefix="tenkz-guard-"))
        try:
            GUARDS[name](workspace)
        except SupervisorError as error:
            if guard["message"] not in str(error):
                failures.append(
                    f"{name}: refused with {str(error)!r}, which does not carry "
                    f"the expected {guard['message']!r}"
                )
                continue
            completed.append(name)
            continue
        except OSError as error:
            failures.append(f"{name}: could not be staged: {error}")
            continue
        finally:
            shutil.rmtree(workspace, ignore_errors=True)
        failures.append(f"{name}: the supervisor accepted a staged escape")
    return completed


def receipt_schema(root: Path) -> dict:
    """The `supervisorReceipt` shape from the pinned replay schema."""

    schema = json.loads(
        (root / "tests/tenkz/release-support/reset-replay-v1.schema.json").read_text(
            encoding="utf-8"
        )
    )
    return schema["$defs"]["supervisorReceipt"]


def run(root: Path = ROOT) -> int:
    policy = read_policy(root)
    document = tomllib.loads((root / EXPECTATIONS).read_text(encoding="utf-8"))
    if document.get("schema") != 1:
        print("FAIL: self-test expectations have an unknown schema", file=sys.stderr)
        return 1
    fingerprint = document["synthetic_fingerprint"]
    pins = computed_pins(policy, root)

    completed: list[str] = []
    failures: list[str] = []
    observed_receipts: list[dict] = []
    for probe in document["probe"]:
        test = synthetic(probe, fingerprint)
        expected = probe["outcome"]
        try:
            payload = observe(test, policy, root, pins)
            observed = payload["assertion_result"]
            observed_receipts.append(payload)
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

    guards_completed = run_guards(document, failures)

    # A replay receipt embeds these verbatim under a shape that is closed in
    # both directions, so the check runs in both directions. Missing a required
    # field and carrying one the schema does not declare are equally fatal, and
    # the second is the one that bit: `tag` was added to every receipt without
    # being added to the schema, and a required-fields-only check saw nothing.
    shape = receipt_schema(root)
    required = sorted(shape["required"])
    declared = set(shape["properties"])
    for payload in observed_receipts:
        missing = [field for field in required if field not in payload]
        forbidden = sorted(set(payload) - declared)
        if missing or forbidden:
            failures.append(
                f"{payload['test_id']}: payload receipt omits {missing!r} and "
                f"carries undeclared field(s) {forbidden!r}, which "
                f"additionalProperties:false rejects"
            )
            break

    receipt = {
        "schema": 1,
        "code_tree": pins["release_test_code_tree"],
        "support_tree": pins["release_test_support_tree"],
        "inventory_sha256": pins["release_test_inventory_sha256"],
        "output_mount": sorted({r["output_mount"] for r in observed_receipts}),
        "tool_fingerprints": {
            name: resolve_tool(name, pattern, root)[1]
            for name, pattern in sorted(tool_profile(root).items())
        },
        "probes_completed": completed,
        "guards_completed": guards_completed,
        "receipt_fields_required": required,
    }
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        return 1
    print(json.dumps(receipt, indent=2, sort_keys=True))
    print(
        f"PASS: {len(completed)} isolation probe(s) and {len(guards_completed)} "
        f"escape guard(s) completed"
    )
    return 0


def main() -> int:
    try:
        return run()
    except (SupervisorError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
