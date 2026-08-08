#!/usr/bin/env python3
"""Evidence supervisor for the tenkz release-test inventory.

`docs/tenkz/SOAK-1.0.md` §Release payload evidence is the authority for
everything here.  The supervisor reads the pinned policy block out of
`docs/tenkz/DESIGN.md`, checks the closed inventory against it, builds one
repository-shaped view per command, runs the command in that view, and emits a
payload receipt.  It is release-test code, so it imports nothing from
`scripts/` and nothing outside this tree.

Subcommands:

    check-inventory   grammar, path roles, and policy agreement, no execution
    run --test ID     observe-release-test: build the view and run one test
    run-all           every inventory test in inventory order
    pins              the three activation pins as the current tree computes them
    check-readiness   what the enforcement state permits at this tree

Two parts of the ledger's protocol are not simulated here and belong to the
enforcement workflow: the mount namespace that hides the real checkout, and the
denial of network access before repository code runs.  The view below exposes
exactly the declared entries and nothing else, and every path a command reads
outside it is a defect the receipt cannot hide, but a determined command could
still read an absolute path.  `RELEASE-POLICY.md` §2 records this as the
boundary between the harness and the job that runs it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path


HARNESS_ROOT = Path(__file__).resolve().parent
ROOT = HARNESS_ROOT.parents[2]
DESIGN_PATH = "docs/tenkz/DESIGN.md"
POLICY_BLOCK = re.compile(
    r"^```toml[ \t]+tenkz-policy-v1[ \t]*\n(.*?)^```[ \t]*$",
    re.MULTILINE | re.DOTALL,
)
TEST_ID_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
SHA256_RE = re.compile(r"[0-9a-f]{64}")
GIT_OID_RE = re.compile(r"[0-9a-f]{40}")
RUNNER_SUFFIX = {"python3": ".py", "bash": ".sh"}
SURFACES = ("tex-api", "tnlog")
TEST_FIELDS = {
    "id",
    "surface",
    "failure_fingerprint",
    "runner",
    "path",
    "args",
    "program_paths",
    "fixture_paths",
    "timeout_seconds",
}
FAILURE_RECEIPT = "assertion-failure-v1.json"
ASSERTION_EXIT = 10
TOOL_PROFILE = "tests/tenkz/release-support/tool-profile.toml"


class SupervisorError(Exception):
    """The inventory, the policy, or a command run is invalid."""


def require(condition: object, message: str) -> None:
    if not condition:
        raise SupervisorError(message)


# --------------------------------------------------------------------------
# Pinned policy
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Policy:
    """The release-payload values the supervisor reads from the pinned block."""

    enforcement: str
    inventory: str
    inventory_sha256: str
    code_root: str
    code_tree: str
    support_root: str
    support_tree: str
    subject_roots: tuple[str, ...]
    fix_paths: dict[str, tuple[str, ...]]
    package_metadata: str
    manual: str
    change_record: str
    event_format: str
    tag_public_key: str


def read_policy(root: Path = ROOT) -> Policy:
    text = (root / DESIGN_PATH).read_text(encoding="utf-8")
    blocks = POLICY_BLOCK.findall(text)
    require(len(blocks) == 1, f"expected one policy block in {DESIGN_PATH}")
    table = tomllib.loads(blocks[0])["policy"]
    return Policy(
        enforcement=table["enforcement"],
        inventory=table["release_test_inventory"],
        inventory_sha256=table["release_test_inventory_sha256"],
        code_root=table["release_test_code_root"],
        code_tree=table["release_test_code_tree"],
        support_root=table["release_test_support_root"],
        support_tree=table["release_test_support_tree"],
        subject_roots=tuple(table["release_test_subject_roots"]),
        fix_paths={
            "tex-api": tuple(table["tex_api_fix_paths"]),
            "tnlog": tuple(table["tnlog_fix_paths"]),
        },
        package_metadata=table["release_package_metadata"],
        manual=table["release_manual"],
        change_record=table["release_change_record"],
        event_format=table["release_event_format"],
        tag_public_key=table["release_tag_public_key"],
    )


# --------------------------------------------------------------------------
# Path grammar
# --------------------------------------------------------------------------


def normalized(value: object) -> str | None:
    """Return the repository-relative path, or None when the spelling is illegal."""

    if not isinstance(value, str) or not value or value.startswith("/") or "\\" in value:
        return None
    parts = value.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        return None
    return value


def glob_matches(path: str, pattern: str) -> bool:
    """Match the policy's `*`/`**` repository-path grammar, not the shell's."""

    expression = re.escape(pattern)
    expression = expression.replace(r"\*\*/", r"(?:[^/]+/)*")
    expression = expression.replace(r"\*", r"[^/]*")
    return re.fullmatch(expression, path) is not None


def within_roots(path: str, roots: tuple[str, ...]) -> bool:
    return any(path == root or path.startswith(f"{root}/") for root in roots)


# --------------------------------------------------------------------------
# Inventory
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Test:
    """One atomic compatibility assertion and everything it may read."""

    id: str
    surface: str
    failure_fingerprint: str
    runner: str
    path: str
    args: tuple[str, ...]
    program_paths: tuple[str, ...]
    fixture_paths: tuple[str, ...]
    timeout_seconds: int


def load_inventory(policy: Policy, root: Path = ROOT) -> tuple[Test, ...]:
    """Parse and fully validate the closed inventory against the pinned policy."""

    blob = root / policy.inventory
    require(blob.is_file(), f"{policy.inventory} is absent")
    document = tomllib.loads(blob.read_text(encoding="utf-8"))
    require(set(document) == {"schema", "test"}, "inventory has fields outside its schema")
    require(document["schema"] == 1, "inventory schema must be 1")
    raw = document["test"]
    require(isinstance(raw, list) and raw, "inventory needs one or more [[test]] tables")

    tests: list[Test] = []
    seen_ids: set[str] = set()
    seen_fingerprints: set[str] = set()
    for index, entry in enumerate(raw, start=1):
        require(set(entry) == TEST_FIELDS, f"test {index} fields differ from the schema")
        test_id = entry["id"]
        require(
            isinstance(test_id, str) and TEST_ID_RE.fullmatch(test_id) is not None,
            f"test {index} has an invalid id",
        )
        require(test_id not in seen_ids, f"duplicate test id {test_id}")
        seen_ids.add(test_id)

        surface = entry["surface"]
        require(surface in SURFACES, f"{test_id} has an unknown surface")

        fingerprint = entry["failure_fingerprint"]
        require(
            isinstance(fingerprint, str) and SHA256_RE.fullmatch(fingerprint) is not None,
            f"{test_id} has an invalid failure fingerprint",
        )
        require(
            fingerprint not in seen_fingerprints,
            f"{test_id} reuses another test's failure fingerprint",
        )
        seen_fingerprints.add(fingerprint)

        runner = entry["runner"]
        require(runner in RUNNER_SUFFIX, f"{test_id} has an unknown runner")

        path = normalized(entry["path"])
        require(path is not None, f"{test_id} has an illegal path spelling")
        require(
            path.startswith(f"{policy.code_root}/"),
            f"{test_id} path is outside the pinned test-code root",
        )
        require(
            path.endswith(RUNNER_SUFFIX[runner]),
            f"{test_id} path suffix does not match its runner",
        )
        require((root / path).is_file(), f"{test_id} path is not a regular file")

        args = entry["args"]
        require(
            isinstance(args, list)
            and all(isinstance(item, str) and item for item in args),
            f"{test_id} args must be nonempty strings",
        )

        programs = subject_paths(root, policy, test_id, entry["program_paths"], "program")
        require(programs, f"{test_id} declares no program path")
        for program in programs:
            require(
                (root / program).is_file(),
                f"{test_id} program path {program} is not a regular file",
            )
            require(
                any(glob_matches(program, p) for p in policy.fix_paths[surface]),
                f"{test_id} program path {program} is outside its surface's fix paths",
            )

        fixtures = subject_paths(root, policy, test_id, entry["fixture_paths"], "fixture")
        for fixture in fixtures:
            require(
                (root / fixture).exists(),
                f"{test_id} fixture path {fixture} is absent",
            )

        overlap = set(programs) & set(fixtures)
        require(not overlap, f"{test_id} declares {sorted(overlap)} in both roles")
        for fixture in fixtures:
            require(
                not any(program.startswith(f"{fixture}/") for program in programs),
                f"{test_id} fixture tree {fixture} contains a program path",
            )

        timeout = entry["timeout_seconds"]
        require(
            isinstance(timeout, int) and not isinstance(timeout, bool) and timeout > 0,
            f"{test_id} timeout must be a positive integer",
        )

        tests.append(
            Test(
                id=test_id,
                surface=surface,
                failure_fingerprint=fingerprint,
                runner=runner,
                path=path,
                args=tuple(args),
                program_paths=programs,
                fixture_paths=fixtures,
                timeout_seconds=timeout,
            )
        )
    return tuple(tests)


def subject_paths(
    root: Path,
    policy: Policy,
    test_id: str,
    value: object,
    role: str,
) -> tuple[str, ...]:
    require(isinstance(value, list), f"{test_id} {role}_paths must be a list")
    resolved: list[str] = []
    for item in value:
        path = normalized(item)
        require(path is not None, f"{test_id} has an illegal {role} path spelling")
        require(
            within_roots(path, policy.subject_roots),
            f"{test_id} {role} path {path} is outside the declared subject roots",
        )
        resolved.append(path)
    require(len(resolved) == len(set(resolved)), f"{test_id} {role}_paths repeat a path")
    return tuple(resolved)


# --------------------------------------------------------------------------
# Pins
# --------------------------------------------------------------------------


def git_tree_oid(root: Path, path: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"HEAD:{path}"],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    require(result.returncode == 0, f"could not read the Git tree OID of {path}")
    oid = result.stdout.strip()
    require(GIT_OID_RE.fullmatch(oid) is not None, f"{path} did not resolve to a tree OID")
    return oid


def blob_sha256(root: Path, path: str) -> str:
    return hashlib.sha256((root / path).read_bytes()).hexdigest()


def computed_pins(policy: Policy, root: Path = ROOT) -> dict[str, str]:
    """The three values the activation change copies into the pinned policy."""

    return {
        "release_test_inventory_sha256": blob_sha256(root, policy.inventory),
        "release_test_code_tree": git_tree_oid(root, policy.code_root),
        "release_test_support_tree": git_tree_oid(root, policy.support_root),
    }


# --------------------------------------------------------------------------
# Hermetic view and command execution
# --------------------------------------------------------------------------


def tool_profile(root: Path) -> dict[str, str]:
    document = tomllib.loads((root / TOOL_PROFILE).read_text(encoding="utf-8"))
    require(set(document) == {"tool"}, "tool profile has fields outside its schema")
    return {name: table["version_pattern"] for name, table in document["tool"].items()}


def resolve_tool(name: str, pattern: str, root: Path) -> tuple[str, str]:
    """Resolve one allowlisted child tool and validate its configured fingerprint.

    Resolution reads the caller's path once.  What the command then sees is the
    sanitized path built from the resolved tools alone, so an inventory command
    can reach the allowlisted tools and nothing else.  A tool that resolves
    inside the repository is rejected: the pinned trees supply assertions, not
    interpreters.
    """

    executable = shutil.which(name)
    require(executable is not None, f"child tool {name} is not on the caller's path")
    resolved = Path(executable).resolve()
    require(
        not resolved.is_relative_to(root),
        f"child tool {name} resolves inside the repository at {resolved}",
    )
    result = subprocess.run(
        [executable, "--version"],
        text=True,
        capture_output=True,
        check=False,
        timeout=30,
    )
    fingerprint = (result.stdout + result.stderr).strip().splitlines()[0]
    require(
        re.fullmatch(pattern, fingerprint) is not None,
        f"child tool {name} reports {fingerprint!r}, which the tool profile rejects",
    )
    return executable, fingerprint


def expose(root: Path, view: Path, relative: str) -> None:
    """Copy one repository entry into the view at its own relative path."""

    source = root / relative
    require(not source.is_symlink(), f"{relative} is a symlink")
    destination = view / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if source.is_dir():
        if destination.exists():
            return
        shutil.copytree(
            source,
            destination,
            symlinks=False,
            ignore=shutil.ignore_patterns("__pycache__"),
        )
    else:
        shutil.copy2(source, destination)


def make_read_only(view: Path) -> None:
    for path in sorted(view.rglob("*"), reverse=True):
        if path.is_file():
            path.chmod(stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)


def make_writable(view: Path) -> None:
    for path in view.rglob("*"):
        if path.is_file():
            path.chmod(stat.S_IRUSR | stat.S_IWUSR)


def canonical_artifacts(policy: Policy) -> tuple[str, ...]:
    return (
        policy.package_metadata,
        policy.manual,
        policy.change_record,
        policy.event_format,
    )


def observe(test: Test, policy: Policy, root: Path = ROOT) -> dict:
    """Run one inventory test in its own view and return its payload receipt."""

    profile = tool_profile(root)
    require(
        test.runner in profile,
        f"{test.id} runner {test.runner} is not in the pinned tool profile",
    )
    tools = {
        name: resolve_tool(name, pattern, root) for name, pattern in profile.items()
    }
    sanitized_path = os.pathsep.join(
        dict.fromkeys(str(Path(executable).parent) for executable, _ in tools.values())
    )

    workspace = Path(tempfile.mkdtemp(prefix="tenkz-release-"))
    view = workspace / "view"
    output = workspace / "output"
    view.mkdir()
    output.mkdir()
    try:
        for relative in (
            policy.code_root,
            policy.support_root,
            policy.inventory,
            *canonical_artifacts(policy),
            *test.program_paths,
            *test.fixture_paths,
        ):
            expose(root, view, relative)
        make_read_only(view)

        environment = {
            "PATH": sanitized_path,
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "HOME": str(workspace / "home"),
            "TENKZ_TEST_OUTPUT": str(output),
            "PYTHONDONTWRITEBYTECODE": "1",
        }
        (workspace / "home").mkdir()

        timed_out = False
        try:
            completed = subprocess.run(
                [tools[test.runner][0], test.path, *test.args],
                cwd=view,
                env=environment,
                text=True,
                capture_output=True,
                timeout=test.timeout_seconds,
                check=False,
            )
            exit_status = completed.returncode
            stderr = completed.stderr
        except subprocess.TimeoutExpired:
            timed_out = True
            exit_status = -1
            stderr = ""

        require(not timed_out, f"{test.id} exceeded its {test.timeout_seconds}s timeout")
        result = classify(test, exit_status, output, stderr)
        return {
            "test_id": test.id,
            "surface": test.surface,
            "command": [test.runner, test.path, *test.args],
            "program_paths": list(test.program_paths),
            "fixture_paths": list(test.fixture_paths),
            "exit_status": exit_status,
            "assertion_result": result,
            "timed_out": timed_out,
            "output_mount": "/tenkz-output",
            "tool_fingerprints": {name: value[1] for name, value in tools.items()},
        }
    finally:
        make_writable(view)
        shutil.rmtree(workspace, ignore_errors=True)


def classify(test: Test, exit_status: int, output: Path, stderr: str) -> str:
    """Accept exit zero, or exit ten with the exact receipt.  Nothing else."""

    receipt_path = output / FAILURE_RECEIPT
    if exit_status == 0:
        require(
            not receipt_path.exists(),
            f"{test.id} passed but wrote an assertion-failure receipt",
        )
        return "passed"
    require(
        exit_status == ASSERTION_EXIT,
        f"{test.id} exited {exit_status}, which is neither a pass nor an assertion "
        f"failure: {stderr.strip()[:400]}",
    )
    require(receipt_path.is_file(), f"{test.id} exited 10 without its receipt")
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    require(
        set(receipt) == {"schema", "test_id", "failure_fingerprint", "completed"},
        f"{test.id} wrote a receipt outside the closed shape",
    )
    require(receipt["schema"] == 1, f"{test.id} receipt schema must be 1")
    require(receipt["test_id"] == test.id, f"{test.id} receipt names another test")
    require(
        receipt["failure_fingerprint"] == test.failure_fingerprint,
        f"{test.id} receipt carries another test's fingerprint",
    )
    require(receipt["completed"] is True, f"{test.id} receipt is incomplete")
    return "assertion-failed"


# --------------------------------------------------------------------------
# Subcommands
# --------------------------------------------------------------------------


def command_check_inventory(policy: Policy, root: Path) -> int:
    tests = load_inventory(policy, root)
    surfaces = sorted({test.surface for test in tests})
    print(
        f"PASS: {len(tests)} atomic release assertion(s) over "
        f"{', '.join(surfaces)}; inventory agrees with the pinned policy"
    )
    return 0


def command_run(policy: Policy, root: Path, selected: str | None) -> int:
    tests = load_inventory(policy, root)
    if selected is not None:
        tests = tuple(test for test in tests if test.id == selected)
        require(tests, f"no inventory test has id {selected}")
    failures = []
    for test in tests:
        receipt = observe(test, policy, root)
        print(f"{receipt['assertion_result']:>16}  {test.id}")
        if receipt["assertion_result"] != "passed":
            failures.append((test, receipt))
    if failures:
        for test, receipt in failures:
            print(
                f"FAIL: {test.id} reported {receipt['assertion_result']} with "
                f"fingerprint {test.failure_fingerprint}",
                file=sys.stderr,
            )
        return 1
    print(f"PASS: {len(tests)} release assertion(s) hold at this tree")
    return 0


def command_pins(policy: Policy, root: Path) -> int:
    for name, value in computed_pins(policy, root).items():
        print(f'{name} = "{value}"')
    return 0


def command_check_readiness(policy: Policy, root: Path) -> int:
    load_inventory(policy, root)
    pending = {
        "release_test_inventory_sha256": policy.inventory_sha256,
        "release_test_code_tree": policy.code_tree,
        "release_test_support_tree": policy.support_tree,
    }
    if policy.enforcement == "pending":
        for name, value in pending.items():
            require(
                value == "pending",
                f"policy enforcement is pending but {name} is already pinned",
            )
        key = root / policy.tag_public_key
        state = "present" if key.is_file() else "absent"
        print(
            "PASS: enforcement pending; the harness, support tree, and inventory "
            f"exist and the final-tag public key is {state}. No release command "
            "is available."
        )
        return 0
    computed = computed_pins(policy, root)
    for name, value in pending.items():
        require(
            value == computed[name],
            f"armed policy {name} does not equal this tree's value",
        )
    require(
        (root / policy.tag_public_key).is_file(),
        "armed policy names a final-tag public key that is absent",
    )
    print("PASS: enforcement armed; every activation pin matches this tree")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check-inventory")
    run = subparsers.add_parser("run")
    run.add_argument("--test", help="run only the inventory test with this id")
    subparsers.add_parser("run-all")
    subparsers.add_parser("pins")
    subparsers.add_parser("check-readiness")
    args = parser.parse_args(argv)

    root = args.root.resolve()
    try:
        policy = read_policy(root)
        if args.command == "check-inventory":
            return command_check_inventory(policy, root)
        if args.command == "run":
            return command_run(policy, root, args.test)
        if args.command == "run-all":
            return command_run(policy, root, None)
        if args.command == "pins":
            return command_pins(policy, root)
        return command_check_readiness(policy, root)
    except (SupervisorError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
