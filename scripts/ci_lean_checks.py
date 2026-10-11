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
``strict``  After the full build, elaborate with warnings as errors

            * every changed production source file, and
            * every ``TNLeanTest`` file that is changed or whose repository
              import closure contains a changed module, together with the
              test files it imports.

            Tests are elaborated in import order. Each test writes its object
            file to a fresh overlay directory placed first on ``LEAN_PATH``, so
            a test may import another test (for example ``TNLeanTest.Support``).

Pushes use the previous head as the base. Without a base revision (manual
dispatch, an unfetchable base), or when a dependency pin, the toolchain, this
script or the workflow changes, ``strict`` checks every test file and ``early``
does nothing; the full build covers it.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

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
    "lakefile.toml",
    "lean-toolchain",
    "scripts/ci_lean_checks.py",
    ".github/workflows/pr-ci.yml",
)

# Keep aligned with EXCLUDED_TOP_LEVEL_DIRECTORIES in
# scripts/generate_import_aggregators.py; pr-ci.yml builds changed archive
# modules separately.
EXCLUDED_PREFIXES = ("TNLean/Archive/",)

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
    return path.startswith("TNLeanTest/") and path.endswith(".lean")


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
    return sorted(files)


def import_graph(root: Path, files: list[str]) -> dict[str, set[str]]:
    """Map each repository module to the repository modules it imports."""
    modules = {module_of(f) for f in files}
    graph: dict[str, set[str]] = {}
    for f in files:
        text = (root / f).read_text(encoding="utf-8", errors="replace")
        graph[module_of(f)] = {m for m in parse_imports(text) if m in modules}
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


def changed_paths(base: str | None) -> list[str] | None:
    """Changed paths against `base`, or None when every test must run."""
    if not base:
        return None
    out = [p for p in subprocess.run(
        ["git", "diff", "-z", "--name-only", "--diff-filter=ACDMR", base, "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.split("\0") if p]
    if any(p in FULL_RUN_PATHS for p in out):
        return None
    return out


def select(
    root: Path, base: str | None
) -> tuple[list[str], list[str], list[str], dict[str, set[str]]]:
    """Return (early modules, strict source files, ordered test files, import graph)."""
    files = lean_files(root)
    graph = import_graph(root, files)
    tests = [f for f in files if is_test(f)]
    changed = changed_paths(base)
    if changed is None:
        selected_tests = set(tests)
        early: list[str] = []
        sources: list[str] = []
    else:
        existing = set(files)
        changed_lean = [p for p in changed if p.endswith(".lean")]
        changed_modules = {module_of(p) for p in changed_lean}
        sources = sorted(p for p in changed_lean if is_production(p) and p in existing)
        early = [module_of(p) for p in sources]
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


def run_lean(path: str, overlay: Path | None, timeout: int) -> tuple[str, int, str]:
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["early", "strict", "list"])
    parser.add_argument("--base", default=os.environ.get("BASE_SHA") or None,
                        help="base revision; omit to check every test")
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=240,
                        help="seconds allowed for each file")
    parser.add_argument("--log", type=Path, help="append early-build output here")
    args = parser.parse_args(argv)

    os.chdir(args.root)
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
        proc = subprocess.Popen(["lake", "--fail-fast", "build", *early],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        assert proc.stdout is not None
        with open(args.log or os.devnull, "a") as log:
            for line in proc.stdout:
                sys.stdout.write(line)
                log.write(line)
        return proc.wait()

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
