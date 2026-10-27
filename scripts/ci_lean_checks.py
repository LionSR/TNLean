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
            After a successful build, use the remaining budget for advisory
            changed-fixture diagnostics. All later checks still run.
``strict``  After the full build, elaborate with warnings as errors

            * every changed production source file, and
            * every test file that is changed or whose repository import
              closure contains a changed module (or a module the change
              deleted or renamed), together with the test files it imports.
              Test files are those under ``TNLeanTest/`` and the standalone
              regressions ``scripts/*_regression.lean``.

            Tests are elaborated in import order. Each test writes its object
            file to a fresh overlay directory placed first on ``LEAN_PATH``, so
            a test may import another test (for example ``TNLeanTest.Support``).

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
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable
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

# Standalone regression files elaborated like tests; they are not modules
# of any Lake library.
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
    return ((path.startswith("TNLeanTest/") and path.endswith(".lean"))
            or REGRESSION_RE.fullmatch(path) is not None)


def is_internal(module: str) -> bool:
    return module == "TNLean" or module.startswith(("TNLean.", "TNLeanTest."))


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
    for top in ("TNLean", "TNLeanTest"):
        base = root / top
        if base.is_dir():
            files.extend(str(p.relative_to(root)) for p in base.rglob("*.lean"))
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


def select(
    root: Path, base: str | None
) -> tuple[list[str], list[str], list[str], dict[str, set[str]]]:
    """Return (early modules, strict source files, ordered test files, import graph)."""
    files = lean_files(root)
    graph = import_graph(root, files)
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
        changed_modules = {module_of(p) for p in changed_lean}
        selected_tests = {
            t for t in tests
            if t in changed_lean or closure(graph, module_of(t)) & changed_modules
        }
    # Tests imported by selected tests must be elaborated first.
    test_modules = {module_of(t): t for t in tests}
    needed = set(selected_tests)
    for t in selected_tests:
        needed |= {test_modules[m] for m in closure(graph, module_of(t)) if m in test_modules}
    return early, sources, order_tests(sorted(needed), graph), graph


def order_tests(tests: list[str], graph: dict[str, set[str]]) -> list[str]:
    """Order tests so every imported test precedes its importers."""
    by_module = {module_of(t): t for t in tests}
    ordered: list[str] = []
    done: set[str] = set()

    def visit(m: str, active: frozenset[str]) -> None:
        if m in done or m in active:
            return
        for d in sorted(graph.get(m, ())):
            if d in by_module:
                visit(d, active | {m})
        done.add(m)
        ordered.append(by_module[m])

    for m in sorted(by_module):
        visit(m, frozenset())
    return ordered


def levels(tests: list[str], graph: dict[str, set[str]]) -> list[list[str]]:
    """Group ordered tests into batches whose members import no batch member."""
    by_module = {module_of(t): t for t in tests}
    depth: dict[str, int] = {}
    for t in tests:  # `tests` is already in dependency order
        deps = [depth[d] for d in graph.get(module_of(t), ()) if d in by_module]
        depth[module_of(t)] = 1 + max(deps, default=-1)
    batches: list[list[str]] = [[] for _ in range(max(depth.values(), default=-1) + 1)]
    for t in tests:
        batches[depth[module_of(t)]].append(t)
    return batches


def lean_command(
    path: str, overlay: Path | None, timeout: int | None
) -> tuple[list[str], dict[str, str]]:
    """Share strict arguments; early diagnostics use their own process-group timer."""
    cmd = ["lean", "-j1", *LEAN_FLAGS]
    if overlay is not None:
        target = overlay / (path[: -len(".lean")] + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        cmd += ["-o", str(target)]
    cmd.append(path)
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    # Lake prepends package paths, so put the overlay first inside `lake env`.
    script = ('[ -n "$1" ] && export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; shift; '
              'exec timeout --signal=INT --kill-after=5s "$0" "$@"')
    full = ["lake", "env", "bash", "-c", script, str(timeout) + "s",
            str(overlay) if overlay is not None else "", *cmd]
    if timeout is None:
        script = ('[ -n "$1" ] && export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; shift; '
                  'exec "$@"')
        full = ["lake", "env", "bash", "-c", script, "early-fixture",
                str(overlay) if overlay is not None else "", *cmd]
    return full, env


def run_lean(path: str, overlay: Path | None, timeout: int) -> tuple[str, int, str]:
    full, env = lean_command(path, overlay, timeout)
    proc = subprocess.run(full, env=env, capture_output=True, text=True)
    return path, proc.returncode, proc.stdout + proc.stderr


def run_batch(paths: list[str], overlay: Path | None, jobs: int, timeout: int) -> list[str]:
    failed: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for path, code, output in pool.map(lambda p: run_lean(p, overlay, timeout), paths):
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


def early_build(
    modules: list[str], log_path: Path | None, budget: int,
    on_success: Callable[[float | None], None] | None = None,
) -> int:
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
    if code == 0 and on_success is not None:
        on_success(deadline)
    return code


def run_early_command(
    command: list[str], deadline: float | None, timeout: int,
    env: dict[str, str] | None = None,
) -> tuple[int | None, str, str]:
    """Run within the remaining shared budget; None means explicitly deferred.

    Early elaboration does not start an inner GNU timeout process group, so
    the same session supervisor can terminate all its descendants.
    """
    remaining = None if deadline is None else deadline - time.monotonic()
    if remaining is not None and remaining <= 0:
        return None, "", ""
    limit = min(remaining, timeout) if remaining is not None and timeout > 0 else (
        remaining if remaining is not None else timeout or None)
    proc = subprocess.Popen(command, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        output, errors = proc.communicate(timeout=limit)
        code = proc.returncode
    except subprocess.TimeoutExpired:
        _stop_group(proc, grace=5)
        output, errors = proc.communicate()
        code = None
    except BaseException:
        _stop_group(proc, grace=5)
        raise
    finally:
        _signal_group(proc.pid, signal.SIGKILL)
        if proc.stdout is not None:
            proc.stdout.close()
        if proc.stderr is not None:
            proc.stderr.close()
    return code, output, errors


def native_fixture_imports(path: str, deadline: float | None, timeout: int) -> set[str]:
    """Use Lake's pinned native parser only for early diagnostic prerequisites.

    --deps-json can exit 0 with per-file errors. Its data must never replace
    the mandatory selector or certify a proof.
    """
    code, output, errors = run_early_command(
        ["lake", "env", "lean", "--deps-json", path], deadline, timeout)
    if errors.strip():
        print(errors.rstrip(), flush=True)
    if code != 0:
        raise ValueError(f"{path}: import inspection "
                         + ("deferred (timeout)" if code is None else f"exited {code}"))
    try:
        data = json.loads(output)
    except ValueError as exc:
        raise ValueError(f"{path}: invalid import-inspection JSON: {exc}") from exc
    results = data.get("imports") if isinstance(data, dict) else None
    if not isinstance(results, list) or len(results) != 1 or not isinstance(results[0], dict):
        raise ValueError(f"{path}: invalid import-inspection result count/schema")
    result = results[0]
    if result.get("errors") != []:
        raise ValueError(f"{path}: import inspection errors: {result.get('errors')!r}")
    header = result.get("result")
    if not isinstance(header, dict) or not isinstance(header.get("isModule"), bool):
        raise ValueError(f"{path}: missing import-inspection header")
    imports = header.get("imports")
    if not isinstance(imports, list) or any(
        not isinstance(item, dict) or not isinstance(item.get("module"), str)
        or not item["module"] for item in imports
    ):
        raise ValueError(f"{path}: invalid import-inspection module list")
    return {item["module"] for item in imports}


def early_fixture_plan(
    roots: list[str], tests: list[str], deadline: float | None, timeout: int,
) -> tuple[list[str], dict[str, set[str]]]:
    """Changed fixtures plus their native-parsed fixture prerequisites only."""
    by_module = {module_of(path): path for path in tests}
    graph: dict[str, set[str]] = {}
    needed = set(roots)
    pending = list(reversed(sorted(roots)))
    while pending:
        path = pending.pop()
        imports = native_fixture_imports(path, deadline, timeout)
        missing = sorted(m for m in imports if m.startswith("TNLeanTest.") and m not in by_module)
        if missing:
            raise ValueError(f"{path}: missing fixture source(s): {', '.join(missing)}")
        graph[module_of(path)] = imports & by_module.keys()
        for module in sorted(graph[module_of(path)], reverse=True):
            dependency = by_module[module]
            if dependency not in needed:
                needed.add(dependency)
                pending.append(dependency)
    ordered = order_tests(sorted(needed), graph)
    positions = {module_of(path): index for index, path in enumerate(ordered)}
    if any(positions[dep] >= positions[module] for module in positions for dep in graph[module]):
        raise ValueError("cyclic fixture imports; early diagnostics deferred")
    return ordered, graph


def early_fixture_diagnostics(
    base: str | None, deadline: float | None, timeout: int, log_path: Path | None,
) -> None:
    """Advisory only: later full/strict/axiom checks always remain mandatory."""
    overlay: Path | None = None
    try:
        tests = [path for path in lean_files(Path(".")) if is_test(path)]
        roots = sorted(set(changed_paths(base) or []) & set(tests))
        if not roots:
            print("No changed fixtures for early diagnostics.", flush=True)
            return
        print("Early fixture diagnostics (advisory; mandatory strict checks still follow):",
              *roots, sep="\n  ", flush=True)
        ordered, graph = early_fixture_plan(roots, tests, deadline, timeout)
        overlay = Path(tempfile.mkdtemp(prefix="tnlean-early-test-overlay-"))
        completed: set[str] = set()
        for path in ordered:
            if not graph[module_of(path)] <= completed:
                print(f"::warning file={path}::Early diagnostic deferred: fixture prerequisite "
                      "did not complete successfully.", flush=True)
                continue
            print(f"::group::Early fixture preparation: {path}", flush=True)
            code, output, errors = run_early_command(
                ["lake", "--fail-fast", "setup-file", path], deadline, timeout)
            # setup-file emits JSON on stdout and ordinary build records on stderr.
            # Keep preparation timings, but never fixture text or JSON, in this log.
            with open(log_path or os.devnull, "a") as log:
                log.write(errors)
            if errors.strip():
                print(errors.rstrip(), flush=True)
            print("::endgroup::", flush=True)
            if code != 0:
                if output.strip():
                    print(output.rstrip(), flush=True)
                status = "timeout" if code is None else f"exit {code}"
                print(f"::warning file={path}::Early diagnostic deferred: dependency "
                      f"preparation {status}; mandatory checks still follow.", flush=True)
                continue
            try:
                setup = json.loads(output)
            except ValueError as exc:
                raise ValueError(f"{path}: invalid setup-file JSON: {exc}") from exc
            if not isinstance(setup, dict) or not isinstance(setup.get("name"), str):
                raise ValueError(f"{path}: invalid setup-file JSON")
            command, env = lean_command(path, overlay, None)
            code, output, errors = run_early_command(command, deadline, timeout, env)
            status = "completed" if code == 0 else ("deferred (timeout)" if code is None
                                                   else f"diagnostic failure (exit {code})")
            print(f"::group::Early fixture {path}: {status}", flush=True)
            if (output + errors).strip():
                print((output + errors).rstrip(), flush=True)
            print("::endgroup::", flush=True)
            if code == 0:
                completed.add(module_of(path))
            else:
                print(f"::warning file={path}::Early fixture {status}; "
                      "mandatory checks still follow.", flush=True)
        print(f"Early fixture diagnostics: {len(completed)}/{len(ordered)} completed; "
              "full build and mandatory strict checks still follow.", flush=True)
    except Exception as exc:
        print(f"::warning::Early fixture diagnostics deferred: {exc}. "
              "Full build and mandatory strict checks still follow.", flush=True)
    finally:
        if overlay is not None:
            shutil.rmtree(overlay, ignore_errors=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["early", "strict", "list"])
    parser.add_argument("--base", default=os.environ.get("BASE_SHA") or None,
                        help="base revision; omit to check every test")
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
    args.base = selection_base(args.base, args.pr_head)
    early, sources, tests, graph = select(Path("."), args.base)

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
        return early_build(early, args.log, args.budget, on_success=lambda deadline:
                           early_fixture_diagnostics(args.base, deadline, args.timeout, args.log))

    print(f"Strict checks: {len(sources)} changed source file(s), {len(tests)} test file(s).",
          flush=True)
    failed = run_batch(sources, None, args.jobs, args.timeout)
    overlay = Path(tempfile.mkdtemp(prefix="tnlean-test-overlay-"))
    try:
        for batch in levels(tests, graph):
            failed += run_batch(batch, overlay, args.jobs, args.timeout)
    finally:
        shutil.rmtree(overlay, ignore_errors=True)
    if failed:
        print(f"{len(failed)} strict Lean check(s) failed:", *failed, sep="\n  ")
        return 1
    print("All strict Lean checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
