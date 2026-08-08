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

What the view is, and what it is not.  It is *declarative* isolation: it
contains exactly the pinned trees, the inventory, the command's declared
subjects, and — with a tag — the tag-derived manifest, so a command that reads
only what it declared cannot see anything else, and a receipt names everything
it could have seen.  It is not a sandbox.  Three limits follow and none is
closed by anything this file can do:

  * the command runs as the user that built the view and owns every path in
    it, so it can `chmod` a sealed file or directory back and then modify it;
  * nothing stops it reading an absolute path outside the view;
  * nothing stops it opening a socket.

The mode bits below therefore stop an accident, not an adversary.  Closing all
three needs a mount namespace and an identity that does not own the view, which
the ledger assigns to the enforcement workflow and not to the supervisor;
`RELEASE-POLICY.md` §2 records the boundary.  Read a payload receipt as
evidence about a cooperating command, which is what a release test is.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
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
DRAIN_SECONDS = 15
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
    manifest_pattern: str


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
        manifest_pattern=table["release_manifest_pattern"],
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
# Symlink and file-mode rejection
# --------------------------------------------------------------------------
#
# `docs/tenkz/SOAK-1.0.md` §Release payload evidence: every exposed repository
# entry is recursively a regular blob or tree, and symlinks, submodules,
# special entries, and any other in-repository dependency are rejected
# *without following them*.  Every check below therefore reads `os.lstat` and
# never `Path.exists`, `Path.is_file`, or any other call that resolves a link.
# A path is checked one component at a time, because a symlinked parent
# directory escapes the repository just as effectively as a symlinked leaf.


def lstat_mode(root: Path, relative: str) -> int:
    """Return the unresolved mode of one repository path, or 0 when absent."""

    try:
        return os.lstat(root / relative).st_mode
    except OSError:
        return 0


def resolve_without_following(root: Path, relative: str, subject: str) -> int:
    """Walk a repository path component by component, refusing every symlink.

    Returns the leaf's unresolved mode.  A missing component, a symlink at any
    depth, or an entry that is neither a regular file nor a directory fails
    closed, so no caller can reach outside the repository through a link and no
    caller learns anything about the link's target.
    """

    parts = relative.split("/")
    for depth in range(1, len(parts) + 1):
        prefix = "/".join(parts[:depth])
        mode = lstat_mode(root, prefix)
        require(mode != 0, f"{subject} is absent at {prefix}")
        require(
            not stat.S_ISLNK(mode),
            f"{subject} passes through the symlink {prefix}, which is rejected "
            f"without following it",
        )
        if depth < len(parts):
            require(
                stat.S_ISDIR(mode),
                f"{subject} treats the non-directory {prefix} as a directory",
            )
    require(
        stat.S_ISREG(mode) or stat.S_ISDIR(mode),
        f"{subject} at {relative} is neither a regular file nor a directory",
    )
    return mode


def require_regular_file(root: Path, relative: str, subject: str) -> None:
    mode = resolve_without_following(root, relative, subject)
    require(stat.S_ISREG(mode), f"{subject} at {relative} is not a regular file")


def gitlink_paths(root: Path) -> frozenset[str]:
    """Every submodule path Git records, by mode 160000 in the index.

    A checked-out submodule is an ordinary directory to `lstat`, and an
    uninitialized one is an empty directory, so neither filesystem mode nor
    emptiness distinguishes it from a tree the view may copy. The Git index is
    the only place the distinction is recorded.
    """

    result = subprocess.run(
        ["git", "ls-files", "--stage", "-z"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return frozenset()
    paths = set()
    for record in result.stdout.decode("utf-8", errors="replace").split("\0"):
        if record.startswith("160000 "):
            paths.add(record.split("\t", 1)[-1])
    return frozenset(paths)


def require_tree_is_clean(root: Path, relative: str, subject: str) -> None:
    """Reject a symlink or special entry anywhere beneath one exposed tree."""

    mode = resolve_without_following(root, relative, subject)
    submodules = gitlink_paths(root)
    # The index records only the submodule's own path, so a declared file
    # *inside* one looks like an ordinary file. Every ancestor is checked.
    parts = relative.split("/")
    for depth in range(1, len(parts) + 1):
        prefix = "/".join(parts[:depth])
        require(
            prefix not in submodules,
            f"{subject} at {relative} descends through the submodule {prefix}, "
            f"which the release contract rejects",
        )
    if not stat.S_ISDIR(mode):
        return
    pending = [relative]
    while pending:
        current = pending.pop()
        for entry in sorted(os.listdir(root / current)):
            child = f"{current}/{entry}"
            require(
                child not in submodules,
                f"{subject} contains the submodule {child}, which the release "
                f"contract rejects",
            )
            child_mode = lstat_mode(root, child)
            require(
                not stat.S_ISLNK(child_mode),
                f"{subject} contains the symlink {child}, which is rejected "
                f"without following it",
            )
            require(
                stat.S_ISREG(child_mode) or stat.S_ISDIR(child_mode),
                f"{subject} contains {child}, which is neither a regular file "
                f"nor a directory",
            )
            if stat.S_ISDIR(child_mode):
                pending.append(child)


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
    schema = document["schema"]
    require(
        isinstance(schema, int) and not isinstance(schema, bool) and schema == 1,
        "inventory schema must be the integer 1",
    )
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
        require_regular_file(root, path, f"{test_id} runner path")

        args = entry["args"]
        require(
            isinstance(args, list)
            and all(isinstance(item, str) and item for item in args),
            f"{test_id} args must be nonempty strings",
        )

        programs = subject_paths(root, policy, test_id, entry["program_paths"], "program")
        require(programs, f"{test_id} declares no program path")
        for program in programs:
            require_regular_file(root, program, f"{test_id} program path")
            require(
                any(glob_matches(program, p) for p in policy.fix_paths[surface]),
                f"{test_id} program path {program} is outside its surface's fix paths",
            )

        fixtures = subject_paths(root, policy, test_id, entry["fixture_paths"], "fixture")
        for fixture in fixtures:
            require_tree_is_clean(root, fixture, f"{test_id} fixture path")

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


def require_clean_worktree(
    policy: Policy,
    root: Path = ROOT,
    extra: tuple[str, ...] = (),
) -> None:
    """Refuse to run when the exposed trees differ from the recorded OIDs.

    The pins come from `HEAD` while `expose` copies bytes from the working
    tree. If the two disagree — a dirty checkout, or an earlier workflow step
    that rewrote the harness — the command would execute code the receipt does
    not name, which is the one thing a payload receipt exists to prevent.
    """

    roots = [policy.code_root, policy.support_root, policy.inventory, *extra]
    result = subprocess.run(
        ["git", "status", "--porcelain", "-z", "--", *roots],
        cwd=root,
        capture_output=True,
        check=False,
    )
    require(result.returncode == 0, "could not read worktree status for the pinned trees")
    dirty = sorted(
        record[3:]
        for record in result.stdout.decode("utf-8", errors="replace").split("\0")
        if record.strip()
    )
    require(
        not dirty,
        f"the pinned trees differ from HEAD at {dirty}; the receipt would name "
        f"OIDs the command did not execute",
    )


def head_commit(root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    require(result.returncode == 0, "could not resolve the observed commit")
    oid = result.stdout.strip()
    require(GIT_OID_RE.fullmatch(oid) is not None, "HEAD did not resolve to a commit OID")
    return oid


def object_ids(root: Path, paths: tuple[str, ...]) -> dict[str, str]:
    """The Git object ID of each exposed path at `HEAD`.

    A receipt naming only the harness pins and its subjects' *paths* cannot be
    told apart from a receipt produced at another commit where the same paths
    hold different bytes. The blob and tree identities are what bind a receipt
    to what it actually read.
    """

    identities = {}
    for path in paths:
        result = subprocess.run(
            ["git", "rev-parse", f"HEAD:{path}"],
            cwd=root,
            text=True,
            capture_output=True,
            check=False,
        )
        require(result.returncode == 0, f"could not read the object ID of {path}")
        oid = result.stdout.strip()
        require(GIT_OID_RE.fullmatch(oid) is not None, f"{path} has no object ID")
        identities[path] = oid
    return identities


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


IGNORED_ENTRIES = frozenset({"__pycache__"})
READ_ONLY_FILE = stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH
READ_ONLY_DIRECTORY = (
    stat.S_IRUSR | stat.S_IXUSR | stat.S_IRGRP | stat.S_IXGRP | stat.S_IROTH | stat.S_IXOTH
)


def expose(root: Path, view: Path, relative: str) -> None:
    """Copy one repository entry into the view at its own relative path.

    The copy never follows a link.  `shutil.copytree` is not used: with
    `symlinks=False` it dereferences a nested symlink and pulls its target into
    the view, which is exactly the escape the ledger forbids, and with
    `symlinks=True` it reproduces the link so the command dereferences it
    instead.  Every entry is checked with `os.lstat` and copied only when it is
    a regular file or a directory.
    """

    require_tree_is_clean(root, relative, f"exposed entry {relative}")
    destination = view / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if stat.S_ISDIR(lstat_mode(root, relative)):
        copy_tree_without_links(root / relative, destination)
    else:
        shutil.copyfile(root / relative, destination, follow_symlinks=False)


def copy_tree_without_links(source: Path, destination: Path) -> None:
    """Copy one directory, refusing any entry that is not a file or directory.

    The copy merges rather than replacing, because exposed entries overlap: a
    declared fixture tree may be an ancestor of a canonical artifact already
    written, and `docs/tenkz` is exactly that case. Returning early when the
    destination existed would have handed the command a directory containing
    only the artifacts, so a tree-shaped assertion would have inspected partial
    coverage and failed for the wrong reason. Merging keeps the union, and a
    file already present is identical because both copies came from one tree.
    """

    destination.mkdir(parents=True, exist_ok=True)
    for name in sorted(os.listdir(source)):
        if name in IGNORED_ENTRIES:
            continue
        child = source / name
        mode = os.lstat(child).st_mode
        require(
            not stat.S_ISLNK(mode),
            f"{child} is a symlink and cannot enter the view",
        )
        require(
            stat.S_ISREG(mode) or stat.S_ISDIR(mode),
            f"{child} is neither a regular file nor a directory",
        )
        if stat.S_ISDIR(mode):
            copy_tree_without_links(child, destination / name)
        elif not (destination / name).exists():
            shutil.copyfile(child, destination / name, follow_symlinks=False)


def tool_directory(workspace: Path, tools: dict[str, tuple[str, str]]) -> Path:
    """Build the one directory the sanitized `PATH` names.

    Putting each resolved interpreter's *parent* on `PATH` would have handed
    the command every sibling executable in that directory — a CPython install
    ships `pip`, `pydoc`, and versioned interpreters beside `python3` — so the
    allowlist would have named the tools while the path exposed the image. The
    directory below contains exactly one entry per allowlisted tool, each a
    link to the executable whose fingerprint was validated.
    """

    directory = workspace / "tools"
    directory.mkdir()
    for name, (executable, _) in tools.items():
        os.symlink(executable, directory / name)
    directory.chmod(READ_ONLY_DIRECTORY)
    return directory


def make_read_only(view: Path) -> None:
    """Clear write access on files *and* directories under the view.

    A read-only file inside a writable directory is not read-only in any sense
    a release cares about: on Unix the directory's write bit governs create,
    unlink, and rename, so a command could delete a declared subject and put
    its own bytes at the same path. Directories are walked deepest first so a
    parent is sealed only after its children.
    """

    for path in sorted(view.rglob("*"), reverse=True):
        mode = os.lstat(path).st_mode
        if stat.S_ISDIR(mode):
            path.chmod(READ_ONLY_DIRECTORY)
        elif stat.S_ISREG(mode):
            path.chmod(READ_ONLY_FILE)
    view.chmod(READ_ONLY_DIRECTORY)


def make_writable(view: Path) -> None:
    """Restore write access so the workspace can be removed.

    Directories are reopened shallowest first: a sealed directory permits
    reading and traversal, so the walk itself succeeds either way, but a child
    cannot be unlinked until its parent is writable again.
    """

    view.chmod(stat.S_IRWXU)
    for path in sorted(view.rglob("*")):
        mode = os.lstat(path).st_mode
        if stat.S_ISDIR(mode):
            path.chmod(stat.S_IRWXU)
        elif stat.S_ISREG(mode):
            path.chmod(stat.S_IRUSR | stat.S_IWUSR)


def run_command(
    argv: list[str],
    *,
    cwd: Path,
    environment: dict[str, str],
    timeout: int,
) -> tuple[int, str, bool]:
    """Run one command in its own process group and bound its whole descendancy.

    `subprocess.run(timeout=...)` kills only the process it started, so a
    command that spawned a child tool could leave descendants running past the
    declared timeout and on into the workspace teardown. The declared timeout
    has to be an execution boundary for the command and everything it starts,
    so the runner gets a new session and the timeout kills the group.
    """

    process = subprocess.Popen(
        argv,
        cwd=cwd,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        _, stderr = process.communicate(timeout=timeout)
        # Success is an execution boundary too. A command that left a
        # background child running would otherwise keep running through
        # classification and workspace teardown, racing the removal of the
        # very files the receipt describes.
        terminate_group(process)
        return process.returncode, stderr, False
    except subprocess.TimeoutExpired:
        terminate_group(process)
        try:
            # Descendants inherit the pipes, so an unbounded drain here would
            # block forever exactly when the group kill failed — turning a
            # fail-closed timeout into a hung run.
            process.communicate(timeout=DRAIN_SECONDS)
        except subprocess.TimeoutExpired:
            process.kill()
            require(
                False,
                "the command's descendants outlived their process group and kept "
                "its output pipes open",
            )
        return -1, "", True


def terminate_group(process: subprocess.Popen) -> None:
    """Signal the command's whole process group, then its leader as a fallback."""

    try:
        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
    except (OSError, ProcessLookupError):
        process.kill()


def canonical_artifacts(policy: Policy) -> tuple[str, ...]:
    return (
        policy.package_metadata,
        policy.manual,
        policy.change_record,
        policy.event_format,
    )


CAMPAIGN_TAG = re.compile(r"tenkz-v(?:0\.9\.(?:0|[1-9][0-9]*)|1\.0\.0)")


def manifest_path(policy: Policy, tag: str) -> str:
    """The manifest path for one campaign tag, after checking the tag itself.

    The tag is interpolated into a repository path, so an unchecked value
    containing `..` would walk out of both the repository and the view. Only
    the two shapes this campaign validates are accepted: a `tenkz-v0.9.PATCH`
    freeze tag or `tenkz-v1.0.0`.
    """

    require(
        CAMPAIGN_TAG.fullmatch(tag) is not None,
        f"{tag!r} is not a campaign tag; expected tenkz-v0.9.PATCH or tenkz-v1.0.0",
    )
    path = normalized(policy.manifest_pattern.replace("TAG", tag))
    require(path is not None, f"the {tag} manifest path is not a repository path")
    return path


def observe(
    test: Test,
    policy: Policy,
    root: Path = ROOT,
    pins: dict[str, str] | None = None,
    tag: str | None = None,
) -> dict:
    """Run one inventory test in its own view and return its payload receipt.

    The receipt carries every field the `supervisorReceipt` shape in
    `tests/tenkz/release-support/reset-replay-v1.schema.json` marks required,
    because a replay receipt embeds these receipts verbatim and a later payload
    validation rejects an incomplete one. `pins` is accepted so a caller
    running the whole inventory reads the three Git pins once.

    `output_mount` records the path the command actually received, not the
    ledger's `/tenkz-output` spelling. Until the enforcement workflow supplies
    a mount namespace, the two differ, and a receipt that named the intended
    path while the command saw another would be false evidence about the run
    that produced it.

    `tag` selects the release the observation is bound to. With a tag this is
    `observe-release-test(K, Q, R)`: the tag-derived manifest joins the view
    and its absence fails closed. Without one — the only shape available while
    no `tenkz-v*` tag exists — the run is a standing check of the assertions at
    this tree and the receipt records `tag = null`, so it can never be read as
    evidence for a release it never saw.
    """

    pins = pins if pins is not None else computed_pins(policy, root)
    profile = tool_profile(root)
    require(
        test.runner in profile,
        f"{test.id} runner {test.runner} is not in the pinned tool profile",
    )
    tools = {
        name: resolve_tool(name, pattern, root) for name, pattern in profile.items()
    }
    workspace = Path(tempfile.mkdtemp(prefix="tenkz-release-"))
    view = workspace / "view"
    output = workspace / "output"
    view.mkdir()
    output.mkdir()
    try:
        sanitized_path = str(tool_directory(workspace, tools))
        # A canonical artifact reaches a command only through one of its two
        # declared roles. Exposing all four to every command would let an
        # assertion read `CHANGES.md` or `TNLOG.md` while its receipt declared
        # neither, so the receipt would not describe what the assertion
        # depended on.
        # An artifact is declared when a declared path *is* it or contains it:
        # a fixture tree such as `docs/tenkz` carries three of the four
        # canonical documents, and reporting those as withheld while the
        # command could read them would make the receipt false.
        declared = (*test.program_paths, *test.fixture_paths)
        undeclared = sorted(
            artifact
            for artifact in canonical_artifacts(policy)
            if not any(
                artifact == path or artifact.startswith(f"{path}/") for path in declared
            )
        )
        exposed = [
            policy.code_root,
            policy.support_root,
            policy.inventory,
            *test.program_paths,
            *test.fixture_paths,
        ]
        if tag is not None:
            manifest = manifest_path(policy, tag)
            require_regular_file(root, manifest, f"the {tag} release manifest")
            exposed.append(manifest)
        for relative in exposed:
            expose(root, view, relative)
        subject_objects = object_ids(root, tuple(exposed))
        home = workspace / "home"
        home.mkdir()
        home.chmod(READ_ONLY_DIRECTORY)
        make_read_only(view)

        environment = {
            "PATH": sanitized_path,
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "HOME": str(home),
            "TENKZ_TEST_OUTPUT": str(output),
            "PYTHONDONTWRITEBYTECODE": "1",
        }

        exit_status, stderr, timed_out = run_command(
            [tools[test.runner][0], test.path, *test.args],
            cwd=view,
            environment=environment,
            timeout=test.timeout_seconds,
        )

        require(not timed_out, f"{test.id} exceeded its {test.timeout_seconds}s timeout")
        result = classify(test, exit_status, output, stderr)
        return {
            "test_id": test.id,
            "surface": test.surface,
            "tag": tag,
            "observed_commit": head_commit(root),
            "exposed_objects": subject_objects,
            "code_tree": pins["release_test_code_tree"],
            "support_tree": pins["release_test_support_tree"],
            "inventory_sha256": pins["release_test_inventory_sha256"],
            "command": [test.runner, test.path, *test.args],
            "program_paths": list(test.program_paths),
            "fixture_paths": list(test.fixture_paths),
            "undeclared_artifacts_withheld": undeclared,
            "exit_status": exit_status,
            "assertion_result": result,
            "timed_out": timed_out,
            "output_mount": str(output),
            "tool_fingerprints": {name: value[1] for name, value in tools.items()},
        }
    finally:
        make_writable(view)
        shutil.rmtree(workspace, ignore_errors=True)


def load_closed_json(path: Path, subject: str) -> dict:
    """Parse one closed JSON object, refusing a repeated key.

    `json.loads` keeps the last of a repeated key and drops the rest, so an
    object carrying `"schema": 1` twice — or once with each of two values —
    passes a field-set check while meaning different things to different
    readers. A closed protocol cannot be parser-dependent.
    """

    def reject_duplicates(pairs: list[tuple[str, object]]) -> dict:
        seen: set[str] = set()
        for key, _ in pairs:
            require(key not in seen, f"{subject} receipt repeats the key {key!r}")
            seen.add(key)
        return dict(pairs)

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)


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
    try:
        receipt_mode = os.lstat(receipt_path).st_mode
    except OSError:
        receipt_mode = 0
    require(receipt_mode != 0, f"{test.id} exited 10 without its receipt")
    require(
        stat.S_ISREG(receipt_mode),
        f"{test.id} wrote its receipt as something other than a regular file; a "
        f"link there would let the payload live outside the output mount",
    )
    receipt = load_closed_json(receipt_path, test.id)
    require(
        set(receipt) == {"schema", "test_id", "failure_fingerprint", "completed"},
        f"{test.id} wrote a receipt outside the closed shape",
    )
    schema = receipt["schema"]
    require(
        isinstance(schema, int) and not isinstance(schema, bool) and schema == 1,
        f"{test.id} receipt schema must be the integer 1",
    )
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


def command_run(
    policy: Policy,
    root: Path,
    selected: str | None,
    tag: str | None = None,
    receipts_path: Path | None = None,
) -> int:
    tests = load_inventory(policy, root)
    if selected is not None:
        tests = tuple(test for test in tests if test.id == selected)
        require(tests, f"no inventory test has id {selected}")
    subjects = {path for test in tests for path in test.program_paths}
    subjects.update(path for test in tests for path in test.fixture_paths)
    subjects.update(canonical_artifacts(policy))
    if tag is not None:
        subjects.add(manifest_path(policy, tag))
    require_clean_worktree(policy, root, tuple(sorted(subjects)))
    pins = computed_pins(policy, root)
    failures = []
    receipts = []
    for test in tests:
        receipt = observe(test, policy, root, pins, tag)
        receipts.append(receipt)
        print(f"{receipt['assertion_result']:>16}  {test.id}")
        if receipt["assertion_result"] != "passed":
            failures.append((test, receipt))
    # The receipts are the durable half of the run. A friction or reset-replay
    # record embeds them verbatim, so discarding them at exit would leave a
    # caller with a summary line and nothing to submit.
    if receipts_path is not None:
        receipts_path.write_text(
            json.dumps(receipts, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"wrote {len(receipts)} payload receipt(s) to {receipts_path}")
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
    require_clean_worktree(policy, root)
    computed = computed_pins(policy, root)
    for name, value in pending.items():
        require(
            value == computed[name],
            f"armed policy {name} does not equal this tree's value",
        )
    require_regular_file(root, policy.tag_public_key, "the final-tag public key")
    require_fixed_tagger(root)
    require_armed_workflow(root)
    print("PASS: enforcement armed; every activation pin matches this tree")
    return 0


TAG_OBJECT_SCHEMA = "tests/tenkz/release-support/final-tag-object-v1.schema.json"


def require_fixed_tagger(root: Path) -> None:
    """The tagger identity must be two byte constants before arming.

    The publisher constructs one byte-deterministic tag object, so every field
    it does not derive from its needs tuple has to be fixed in the pinned
    schema. `tagger_name` and `tagger_email` are left open while the signing
    key is absent; arming with them still open would pin a support tree that
    cannot produce a deterministic object, and the failure would not appear
    until the publisher ran.
    """

    require_regular_file(root, TAG_OBJECT_SCHEMA, "the final-tag object schema")
    schema = json.loads((root / TAG_OBJECT_SCHEMA).read_text(encoding="utf-8"))
    properties = schema.get("properties", {})
    open_fields = [
        field
        for field in ("tagger_name", "tagger_email")
        if not isinstance(properties.get(field, {}).get("const"), str)
    ]
    require(
        not open_fields,
        f"armed policy but {TAG_OBJECT_SCHEMA} leaves {open_fields} without a "
        f"fixed const value, so the tag object would not be byte-deterministic",
    )


ARMED_WORKFLOW = ".github/workflows/tenkz-release-policy.yml"
YAML_COMMENT = re.compile(r"(?m)(?:(?<=^)|(?<=\s))#.*$")
MUTABLE_ACTION = re.compile(r"uses:\s*\S+@(?!\b[0-9a-f]{40}\b)\S+")
JOBS_KEY = re.compile(r"(?m)^jobs:\s*$")
JOB_HEADER = re.compile(r"(?m)^(\s+)([A-Za-z_][\w-]*):\s*$")
# `environment: name` and the block form `environment:\n  name: name` are both
# legal GitHub spellings of the same thing, so both must match.
PUBLISHER_ENVIRONMENT = re.compile(
    r"(?m)^\s+environment:\s*(?:tenkz-release-publisher\s*$"
    r"|\s*\n\s+name:\s*tenkz-release-publisher\s*$)"
)
PUBLISHER_REQUIREMENTS = (
    (
        re.compile(r"(?m)^\s+contents:\s*write\s*$"),
        "a job-level `contents: write` permission",
    ),
    (
        re.compile(r"\$\{\{\s*secrets\.TENKZ_FINAL_TAG_SIGNING_KEY\s*\}\}"),
        "a reference to the TENKZ_FINAL_TAG_SIGNING_KEY secret",
    ),
    (
        re.compile(r"(?m)^\s+needs:\s*\S"),
        "its own `needs:` dependency, which is what orders it after post-merge "
        "validation",
    ),
)
NETWORK_DENIAL = re.compile(r"(?m)^\s+(?:-\s+)?(?:id|name):\s*tenkz-network-denied\s*$")


def workflow_jobs(text: str) -> dict[str, str]:
    """Split a workflow's `jobs:` mapping into one text block per job.

    This is not a YAML parser and does not need to be: job keys are the only
    mapping at their indentation under `jobs:`, so a block runs from one such
    key to the next. Splitting matters because the publisher's requirements are
    requirements *on the publisher job* — a `needs:` belonging to a validation
    job says nothing about what orders the publisher.
    """

    start = JOBS_KEY.search(text)
    if start is None:
        return {}
    body = text[start.end() :]
    headers = list(JOB_HEADER.finditer(body))
    if not headers:
        return {}
    indent = min(len(header.group(1)) for header in headers)
    jobs: dict[str, str] = {}
    tops = [header for header in headers if len(header.group(1)) == indent]
    for index, header in enumerate(tops):
        stop = tops[index + 1].start() if index + 1 < len(tops) else len(body)
        jobs[header.group(2)] = body[header.start() : stop]
    return jobs


def require_armed_workflow(root: Path) -> None:
    """Check the mechanisms the armed enforcement workflow must carry.

    The workflow's own header says `check-readiness` fails closed when these
    are missing, so this is where that promise is kept.

    The checks read the file with its comments stripped and are scoped to the
    job they are about. A whole-file substring search would be satisfied by
    this very file's header, which names the publisher environment and
    `contents: write` while explaining that neither exists yet; a whole-file
    pattern search would be satisfied by any other job's `needs:`. A check that
    its own documentation passes is not a check.
    """

    require_regular_file(root, ARMED_WORKFLOW, "the enforcement workflow")
    text = YAML_COMMENT.sub("", (root / ARMED_WORKFLOW).read_text(encoding="utf-8"))
    jobs = workflow_jobs(text)
    publishers = [
        name for name, block in jobs.items() if PUBLISHER_ENVIRONMENT.search(block)
    ]
    require(
        publishers,
        f"armed policy but {ARMED_WORKFLOW} has no job whose `environment:` is "
        f"tenkz-release-publisher",
    )
    require(
        len(publishers) == 1,
        f"{ARMED_WORKFLOW} has {len(publishers)} publisher jobs {publishers}; the "
        f"campaign has one terminal publisher",
    )
    publisher = jobs[publishers[0]]
    missing = [
        description
        for pattern, description in PUBLISHER_REQUIREMENTS
        if pattern.search(publisher) is None
    ]
    if NETWORK_DENIAL.search(text) is None:
        missing.append(
            "a step named tenkz-network-denied, which denies network access "
            "before repository code runs"
        )
    require(
        not missing,
        f"armed policy but the {publishers[0]} job in {ARMED_WORKFLOW} lacks "
        f"{'; '.join(missing)}",
    )
    mutable = sorted(set(MUTABLE_ACTION.findall(text)))
    require(
        not mutable,
        f"{ARMED_WORKFLOW} pins {mutable} by a mutable reference rather than a "
        f"full commit SHA",
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check-inventory")
    run = subparsers.add_parser("run")
    run.add_argument("--test", help="run only the inventory test with this id")
    run.add_argument("--tag", help="bind the observation to this release tag")
    run.add_argument(
        "--receipts", type=Path, help="write the payload receipts to this JSON file"
    )
    run_all = subparsers.add_parser("run-all")
    run_all.add_argument("--tag", help="bind the observations to this release tag")
    run_all.add_argument(
        "--receipts", type=Path, help="write the payload receipts to this JSON file"
    )
    subparsers.add_parser("pins")
    subparsers.add_parser("check-readiness")
    args = parser.parse_args(argv)

    root = args.root.resolve()
    try:
        policy = read_policy(root)
        if args.command == "check-inventory":
            return command_check_inventory(policy, root)
        if args.command == "run":
            return command_run(policy, root, args.test, args.tag, args.receipts)
        if args.command == "run-all":
            return command_run(policy, root, None, args.tag, args.receipts)
        if args.command == "pins":
            return command_pins(policy, root)
        return command_check_readiness(policy, root)
    except (SupervisorError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
