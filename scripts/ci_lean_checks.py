#!/usr/bin/env python3
"""Generic early builds and strict Lean checks for pull-request CI.

`pr-ci.yml` used to carry one hand-written step per new module ("Build X
early", "Test X strictly and audit axioms").  Every topic pull request edited
the same lines of the workflow, so unrelated pull requests conflicted there.
This script derives the same checks from the change set instead.

Commands
--------
``early``   Build the changed production modules with ``lake --fail-fast build``
            before the full library build, so a failure surfaces quickly.
            If any changed source is not confidently import-only, defer
            import-only aggregators to the mandatory full library build.
``focused`` Check the PR's directly changed sources and regression scripts
            before the full build. Select against the explicit feature head's
            merge base, but build and elaborate the actual (possibly merged)
            checkout. Failures remain failures while independent targets are
            still diagnosed.
``strict``  After the full build, elaborate with warnings as errors

            * every changed production source file, and
            * every standalone regression ``scripts/*_regression.lean`` that
              is changed or whose repository import closure contains a
              changed module (or a module the change deleted or renamed).

Pull-request merge checkouts use their actual base parent after verifying the
second parent matches the event's PR head. Pushes use the previous head as the base.
When a dependency pin, the
toolchain, this script or the workflow changes, ``strict`` checks every test
file; early selection still applies, and all changed sources remain strict.
Without a base revision (manual dispatch, an unfetchable base) ``strict``
checks every test file and ``early`` does nothing; the full build covers it.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

from lean_import_syntax import pure_import_modules

LEAN_FLAGS = [
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-Dpp.unicode.fun=true",
    "-DmaxSynthPendingDepth=3",
    "-Dlinter.mathlibStandardSet=true",
    "-DwarningAsError=true",
]

# A change to any of these can affect every test, so check all of them.
FULL_RUN_PATHS = (
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
    "scripts/ci_lean_checks.py",
    ".github/workflows/pr-ci.yml",
)

# Keep aligned with EXCLUDED_TOP_LEVEL_DIRECTORIES in
# scripts/generate_import_aggregators.py; pr-ci.yml builds changed archive
# modules separately.
EXCLUDED_PREFIXES = ("TNLean/Archive/",)

# Standalone regression files, the only test files; they are not modules of
# any Lake library.
REGRESSION_RE = re.compile(r"scripts/[^/]+_regression\.lean")

IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$")


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def is_production(path: str) -> bool:
    return (
        path.startswith("TNLean/")
        and path.endswith(".lean")
        and not path.startswith(EXCLUDED_PREFIXES)
    )


def is_test(path: str) -> bool:
    return REGRESSION_RE.fullmatch(path) is not None


def is_internal(module: str) -> bool:
    return module == "TNLean" or module.startswith("TNLean.")


def parse_imports(text: str) -> list[str]:
    """Return the modules imported by the header of a Lean file."""
    imports: list[str] = []
    in_block_comment = 0
    for raw in text.splitlines():
        line = raw.strip()
        if in_block_comment:
            in_block_comment += line.count("/-") - line.count("-/")
            continue
        if line.startswith("/-!"):
            break  # the module docstring follows the import header
        if line.startswith("/-"):
            in_block_comment = line.count("/-") - line.count("-/")
            continue
        if not line or line.startswith("--"):
            continue
        if line == "module" or line.startswith("prelude"):
            continue
        match = IMPORT_RE.match(line)
        if not match:
            break
        imports.extend(match.group(1).split("--")[0].split())
    return imports


def lean_files(root: Path) -> list[str]:
    files = []
    library = root / "TNLean"
    if library.is_dir():
        files.extend(str(p.relative_to(root)) for p in library.rglob("*.lean"))
    if (root / "TNLean.lean").is_file():
        files.append("TNLean.lean")
    scripts = root / "scripts"
    if scripts.is_dir():
        files.extend(str(p.relative_to(root)) for p in scripts.glob("*_regression.lean"))
    return sorted(files)


def import_graph(root: Path, files: list[str]) -> dict[str, set[str]]:
    """Map each repository file's module to the repository modules it imports.

    Imports of repository-internal modules are kept even when the module no
    longer exists, so deleting or renaming a module marks its importers."""
    modules = {module_of(f) for f in files}
    graph: dict[str, set[str]] = {}
    for f in files:
        text = (root / f).read_text(encoding="utf-8", errors="replace")
        graph[module_of(f)] = {m for m in parse_imports(text)
                               if m in modules or is_internal(m)}
    return graph


def closure(graph: dict[str, set[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        m = stack.pop()
        for d in graph.get(m, ()):
            if d not in seen:
                seen.add(d)
                stack.append(d)
    return seen


def selection_base(base: str | None, pr_head: str | None) -> str | None:
    """Use the tested merge's base parent, not a possibly stale event base.

    GitHub's pull-request checkout has the base as its first parent and the
    PR head as its second. Verify that shape before narrowing the selection;
    unknown/shallow/mismatched checkouts must retain the full-suite fallback.
    Push and local invocations without a PR head keep their explicit base.
    """
    if not pr_head:
        return base
    result = subprocess.run(
        ["git", "rev-list", "--parents", "-n", "1", "HEAD"],
        capture_output=True, text=True,
    )
    commits = result.stdout.split()
    if result.returncode == 0 and len(commits) == 3 and commits[2] == pr_head:
        parent = commits[1]
        available = subprocess.run(
            ["git", "cat-file", "-e", f"{parent}^{{commit}}"],
            capture_output=True,
        )
        if available.returncode == 0:
            print(f"Selecting changes against tested PR merge base parent {parent}.",
                  file=sys.stderr)
            return parent
    print("::warning::Cannot verify the PR merge parents; checking every test.",
          file=sys.stderr)
    return None


def changed_paths(base: str | None) -> list[str] | None:
    """Changed paths against `base`, or None without a base revision."""
    if not base:
        return None
    return [p for p in subprocess.run(
        ["git", "diff", "-z", "--name-only", "--no-renames", "--diff-filter=ACDM", base, "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.split("\0") if p]


def early_modules(root: Path, sources: list[str]) -> list[str]:
    """Prefer substantive sources; retain every target if all are import-only."""
    substantive = []
    for path in sources:
        try:
            text = (root / path).read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            # An unreadable source is never safe to defer as import-only.
            substantive.append(path)
            continue
        imports, error = pure_import_modules(text)
        if error is not None or not imports:
            substantive.append(path)
    return [module_of(path) for path in substantive or sources]


def select(root: Path, base: str | None) -> tuple[list[str], list[str], list[str]]:
    """Return (early modules, strict source files, test files)."""
    files = lean_files(root)
    tests = [f for f in files if is_test(f)]
    changed = changed_paths(base)
    # All changed production files remain strict sources, including import-only
    # aggregators deferred from the early shortcut to the full library build.
    changed_lean = [p for p in changed or [] if p.endswith(".lean")]
    existing = set(files)
    sources = sorted(p for p in changed_lean if is_production(p) and p in existing)
    early = early_modules(root, sources)
    if changed is None or any(p in FULL_RUN_PATHS for p in changed):
        selected_tests = set(tests)
    else:
        graph = import_graph(root, files)
        changed_modules = {module_of(p) for p in changed_lean}
        selected_tests = {
            t for t in tests
            if t in changed_lean or closure(graph, module_of(t)) & changed_modules
        }
    return early, sources, sorted(selected_tests)


def select_focused(
    root: Path, base: str | None, head: str | None
) -> tuple[list[str], list[str], dict[str, set[str]]]:
    """Select direct PR edits, without attributing synthetic-merge edits to the PR.

    Deleted files absent from the checkout have no elaboration target; a merge
    resolution that restores one is checked. Renamed destinations are additions.
    A file present in the feature head may not silently disappear from the checkout
    being tested. Dependencies use that checkout, not the feature head's older
    contents. The full selector above is intentionally unchanged.
    """
    if not base or not head:
        raise ValueError("focused checks require both --base and --head")

    def git(*args: str) -> str:
        return subprocess.run(["git", *args], check=True, capture_output=True,
                              text=True).stdout.strip()

    base_commit = git("rev-parse", "--verify", "--end-of-options", f"{base}^{{commit}}")
    head_commit = git("rev-parse", "--verify", "--end-of-options", f"{head}^{{commit}}")
    git("merge-base", "--is-ancestor", head_commit, "HEAD")
    fork = git("merge-base", base_commit, head_commit)
    changed = [p for p in git("diff", "--name-only", "--no-renames", "-z",
                             "--diff-filter=ACDMT", fork, head_commit, "--").split("\0") if p]
    head_files = set(git("ls-tree", "-r", "--name-only", "-z", head_commit).split("\0"))
    files = lean_files(root)
    existing = set(files)
    direct = {p for p in changed if is_production(p) or is_test(p)}
    missing = sorted((direct & head_files) - existing)
    if missing:
        raise ValueError("changed PR targets missing from the checkout: " + ", ".join(missing))
    changed_sources = sorted(p for p in direct & existing if is_production(p))
    # Defer pure import-only aggregators to the mandatory full build, mirroring
    # `early_modules`. Such a file declares nothing, so a strict elaboration only
    # reconfirms that its imports resolve -- which the root build already does --
    # yet preparing it forces a cold build of its entire import closure. For a
    # top aggregator that closure can span the whole library (for example
    # TNLean.MPS.AreaLaw reaches PEPS.AreaLaw and Lattice), which on a cache
    # invalidated by a toolchain or dependency bump makes this diagnostic step
    # redo most of the root build. An unreadable file is never safe to defer.
    sources: list[str] = []
    deferred: list[str] = []
    for path in changed_sources:
        try:
            text = (root / path).read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            sources.append(path)
            continue
        imports, error = pure_import_modules(text)
        if error is None and imports:
            deferred.append(path)
        else:
            sources.append(path)
    tests = sorted(p for p in direct & existing if is_test(p))
    graph = import_graph(root, files)
    print(f"Focused PR range: {fork}..{head_commit}; elaborating checkout HEAD.", flush=True)
    print(f"Focused selection: {len(sources)} direct source(s), "
          f"{len(tests)} direct regression script(s).", flush=True)
    if deferred:
        print(f"Focused deferral: {len(deferred)} import-only aggregator(s) left "
              f"to the mandatory full build: {', '.join(deferred)}.", flush=True)
    return sources, tests, graph


def run_lean(path: str, timeout: int) -> tuple[str, int, str]:
    cmd = ["lake", "env", "timeout", "--signal=INT", "--kill-after=5s", f"{timeout}s",
           "lean", "-j1", *LEAN_FLAGS, path]
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
    return path, proc.returncode, proc.stdout + proc.stderr


def run_batch(paths: list[str], jobs: int, timeout: int) -> list[str]:
    failed: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for path, code, output in pool.map(lambda p: run_lean(p, timeout), paths):
            status = "ok" if code == 0 else ("timeout" if code == 124 else f"exit {code}")
            print(f"::group::{path}: {status}", flush=True)
            if output.strip():
                print(output.rstrip(), flush=True)
            print("::endgroup::", flush=True)
            if code != 0:
                print(f"::error file={path}::strict Lean check failed ({status})", flush=True)
                failed.append(path)
    return failed


def _signal_group(pid: int, sig: int) -> None:
    try:
        os.killpg(pid, sig)
    except ProcessLookupError:
        pass  # the whole group has already exited


def _stop_group(proc: subprocess.Popen, grace: int = 30) -> None:
    """Terminate the build's process group: SIGTERM, a grace period for `lake`,
    then SIGKILL for any descendant that ignored it or outlived `lake`."""
    _signal_group(proc.pid, signal.SIGTERM)
    try:
        proc.wait(timeout=grace)
    except subprocess.TimeoutExpired:
        pass
    _signal_group(proc.pid, signal.SIGKILL)
    proc.wait()


def early_build(modules: list[str], log_path: Path | None, budget: int) -> int:
    """Fail-fast `lake build` of `modules`. The early build is only a shortcut,
    since the root build compiles the same modules, so when it exceeds `budget`
    seconds (for example behind a cold dependency cache) it is stopped with a
    warning instead of failing the job."""
    deadline = time.monotonic() + budget if budget else None
    proc = subprocess.Popen(["lake", "--fail-fast", "build", *modules],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    assert proc.stdout is not None

    def pump(stream, log) -> None:
        for line in stream:
            sys.stdout.write(line)
            log.write(line)

    with open(log_path or os.devnull, "a") as log:
        reader = threading.Thread(target=pump, args=(proc.stdout, log), daemon=True)
        reader.start()
        try:
            code: int | None = proc.wait(
                timeout=max(0, deadline - time.monotonic()) if deadline is not None else None)
        except subprocess.TimeoutExpired:
            _stop_group(proc)
            code = None
        except BaseException:
            # The build runs in its own session, so an interrupt such as Ctrl-C
            # does not reach it; stop it before re-raising.
            _stop_group(proc, grace=5)
            raise
        finally:
            # A descendant that outlived `lake` would keep the pipe open.
            _signal_group(proc.pid, signal.SIGKILL)
            reader.join(timeout=60)
    if code is None:
        print(f"::warning::Early build stopped after {budget}s; "
              "the root build compiles the remaining modules.", flush=True)
        return 0
    return code


def focused_checks(
    sources: list[str], tests: list[str], graph: dict[str, set[str]],
    jobs: int, timeout: int, log_path: Path | None,
) -> int:
    """Prepare each target, then use the ordinary strict runner.

    Preparation has no success-on-timeout shortcut: the surrounding CI step's
    timeout is the upper bound. A failed preparation blocks its strict check,
    not independent targets, and always makes the final result nonzero.
    """
    failed: list[str] = []
    prepared: dict[str, bool] = {}

    def prepare(module: str) -> bool:
        if module not in prepared:
            print(f"Preparing focused target: {module}", flush=True)
            # Zero disables the early shortcut's warning-and-success budget.
            code = early_build([module], log_path, 0)
            prepared[module] = code == 0
            if code != 0:
                failed.append(f"{module}: dependency build exited {code}")
        return prepared[module]

    for source in sources:
        if prepare(module_of(source)):
            failed += run_batch([source], jobs, timeout)

    ready: list[str] = []
    for test in tests:
        module = module_of(test)
        required = closure(graph, module)
        missing = required - graph.keys()
        blocked = bool(missing or any(prepared.get(m) is False for m in required))
        if not blocked:
            # Build every immediate import, including a root module if the
            # regression script actually imports one; no allowlist.
            outcomes = [prepare(m) for m in sorted(graph.get(module, set()))]
            blocked = not all(outcomes)
        if blocked:
            failed.append(f"{test}: blocked by missing or failed dependencies")
        else:
            ready.append(test)
    failed += run_batch(ready, jobs, timeout)
    if failed:
        print("Focused checks failed:", *failed, sep="\n  ", flush=True)
        return 1
    print("All focused checks passed.", flush=True)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["early", "strict", "list", "focused"])
    parser.add_argument("--base", default=os.environ.get("BASE_SHA") or None,
                        help="base revision; omit to check every test")
    parser.add_argument("--head", default=os.environ.get("PR_HEAD_SHA") or None,
                        help="focused: explicit PR feature head contained in checkout HEAD")
    parser.add_argument("--pr-head", default=os.environ.get("PR_HEAD_SHA") or None,
                        help="event PR head SHA; verify synthetic merge parents")
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=240,
                        help="seconds allowed for each file")
    parser.add_argument("--log", type=Path, help="append early-build output here")
    parser.add_argument("--budget", type=int, default=0,
                        help="early: stop after this many seconds and leave the rest "
                             "to the root build (0 means no limit)")
    args = parser.parse_args(argv)

    os.chdir(args.root)
    if args.command == "focused":
        try:
            sources, tests, graph = select_focused(Path("."), args.base, args.head)
            return focused_checks(sources, tests, graph, args.jobs, args.timeout, args.log)
        except (ValueError, OSError, subprocess.CalledProcessError) as exc:
            print(f"::error::Focused checks could not complete: {exc}", file=sys.stderr)
            return 1
    args.base = selection_base(args.base, args.pr_head)
    early, sources, tests = select(Path("."), args.base)

    if args.command == "list":
        for m in early:
            print("early", m)
        for s in sources:
            print("source", s)
        for t in tests:
            print("test", t)
        return 0

    if args.command == "early":
        if not early:
            print("No changed production modules to build early.")
            return 0
        print("Building changed modules early:", *early, sep="\n  ", flush=True)
        return early_build(early, args.log, args.budget)

    print(f"Strict checks: {len(sources)} changed source file(s), {len(tests)} test file(s).",
          flush=True)
    failed = run_batch(sources + tests, args.jobs, args.timeout)
    if failed:
        print(f"{len(failed)} strict Lean check(s) failed:", *failed, sep="\n  ")
        return 1
    print("All strict Lean checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
