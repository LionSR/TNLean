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
``focused`` Check the PR's directly changed sources before the full build.
            Select against the explicit feature head's merge base, but build
            and elaborate the actual (possibly merged) checkout. Defer
            confidently import-only production sources to the full build and
            post-build strict checks. Failures remain failures
            while independent targets are still diagnosed. With ``--budget``
            the step is a shortcut like ``early``: once the budget is spent
            (a cold dependency cache, a change near the bottom of the import
            graph) the remaining targets are left, with a warning, to the
            mandatory full build and post-build strict checks.
``strict``  After the full build, elaborate every changed production source
            file with warnings as errors.

Pull-request merge checkouts use their actual base parent after verifying the
second parent matches the event's PR head. Pushes use the previous head as the base.
Without a base revision (manual dispatch, an unfetchable base) ``strict`` and
``early`` do nothing; the full build covers the library.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
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

# Keep aligned with EXCLUDED_TOP_LEVEL_DIRECTORIES in
# scripts/generate_import_aggregators.py; pr-ci.yml builds changed archive
# modules separately.
EXCLUDED_PREFIXES = ("TNLean/Archive/",)


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def is_production(path: str) -> bool:
    return (
        path.startswith("TNLean/")
        and path.endswith(".lean")
        and not path.startswith(EXCLUDED_PREFIXES)
    )


def selection_base(base: str | None, pr_head: str | None) -> str | None:
    """Use the tested merge's base parent, not a possibly stale event base.

    GitHub's pull-request checkout has the base as its first parent and the
    PR head as its second. Verify that shape before narrowing the selection;
    unknown/shallow/mismatched checkouts fall back to no base, leaving the
    changed sources to the full build.
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
    print("::warning::Cannot verify the PR merge parents; no changed source is selected.",
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


def focused_sources(root: Path, sources: list[str], strict_sources: list[str]) -> list[str]:
    """Defer confidently import-only sources; full strict selection is unchanged."""
    retained = []
    for path in sources:
        if path not in strict_sources:
            retained.append(path)
            continue
        try:
            text = (root / path).read_bytes().decode("utf-8")
        except (OSError, UnicodeError):
            retained.append(path)
            continue
        # Python whitespace/comment rules are not Lean's lexer. Keep uncertain
        # spellings and doc-comment tokens focused, even inside other comments.
        if any(c.isspace() and c not in " \n" for c in text) or "/--" in text or "/-!" in text:
            retained.append(path)
            continue
        # Comments separate tokens in Lean. Do not let the shared comment
        # stripper join e.g. im/- comment -/port into an import command.
        spaced = text.replace("/-", " /-").replace("-/", "-/ ")
        imports, error = pure_import_modules(spaced)
        if error is not None or not imports:
            retained.append(path)
        else:
            print(f"Deferring import-only source to full build and post-build strict: {path}",
                  flush=True)
    return retained


def changed_sources(root: Path, base: str | None) -> list[str]:
    """Changed production source files present in the checkout."""
    return sorted(p for p in changed_paths(base) or []
                  if is_production(p) and os.path.lexists(root / p))


def select(root: Path, base: str | None) -> tuple[list[str], list[str]]:
    """Return (early modules, strict source files)."""
    # All changed production files remain strict sources, including import-only
    # aggregators deferred from the early shortcut to the full library build.
    sources = changed_sources(root, base)
    return early_modules(root, sources), sources


def select_focused(root: Path, base: str | None, head: str | None) -> list[str]:
    """Select direct PR edits, without attributing synthetic-merge edits to the PR.

    Deleted files absent from the checkout have no elaboration target; a merge
    resolution that restores one is checked. Renamed destinations are additions.
    A file present in the feature head may not silently disappear from the checkout
    being tested. Dependencies use that checkout, not the feature head's older
    contents.
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
    direct = {p for p in changed if is_production(p)}
    existing = {p for p in direct if os.path.lexists(root / p)}
    missing = sorted((direct & head_files) - existing)
    if missing:
        raise ValueError("changed PR targets missing from the checkout: " + ", ".join(missing))
    sources = sorted(existing)
    print(f"Focused PR range: {fork}..{head_commit}; elaborating checkout HEAD.", flush=True)
    print(f"Focused selection: {len(sources)} direct source(s).", flush=True)
    return sources


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


def build_until(modules: list[str], log_path: Path | None, budget: float | None) -> int | None:
    """Fail-fast `lake build` of `modules`: its exit code, or `None` when it
    was stopped because it ran for `budget` seconds (`None` means no limit)."""
    deadline = time.monotonic() + budget if budget is not None else None
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
    return code


def early_build(modules: list[str], log_path: Path | None, budget: int) -> int:
    """Fail-fast `lake build` of `modules`. The early build is only a shortcut,
    since the root build compiles the same modules, so when it exceeds `budget`
    seconds (for example behind a cold dependency cache) it is stopped with a
    warning instead of failing the job. Zero means no limit."""
    code = build_until(modules, log_path, budget or None)
    if code is None:
        print(f"::warning::Early build stopped after {budget}s; "
              "the root build compiles the remaining modules.", flush=True)
        return 0
    return code


def focused_checks(
    sources: list[str], jobs: int, timeout: int, log_path: Path | None, budget: int = 0,
) -> int:
    """Prepare the targets, then use the ordinary strict runner.

    A failed preparation blocks its strict check, not independent targets, and
    always makes the final result nonzero. Without a `budget` the surrounding
    CI step's timeout is the only bound. With one, the step is a shortcut:
    targets not prepared or not checked within `budget` seconds are left, with
    a warning, to the root build and the post-build strict checks, which
    remain mandatory. Failures found before the budget is spent still fail.
    """
    failed: list[str] = []
    deferred: list[str] = []
    prepared: dict[str, bool] = {}
    unprepared: set[str] = set()
    deadline = time.monotonic() + budget if budget else None

    def expired() -> bool:
        return deadline is not None and time.monotonic() >= deadline

    def build(modules: list[str]) -> int | None:
        """Exit code of the dependency build, or `None` if the budget ended it."""
        if deadline is None:
            # Zero disables the early shortcut's warning-and-success budget.
            return early_build(modules, log_path, 0)
        left = deadline - time.monotonic()
        return build_until(modules, log_path, left) if left > 0 else None

    def prepare(module: str) -> bool:
        if module in unprepared:
            return False
        if module not in prepared:
            print(f"Preparing focused target: {module}", flush=True)
            code = build([module])
            if code is None:
                unprepared.add(module)
                return False
            prepared[module] = code == 0
            if code != 0:
                failed.append(f"{module}: dependency build exited {code}")
        return prepared[module]

    def check(paths: list[str]) -> list[str]:
        if deadline is None:
            return run_batch(paths, jobs, timeout)
        # One batch per `jobs` files, so that the budget is consulted at most
        # one per-file timeout late.
        out: list[str] = []
        for start in range(0, len(paths), max(1, jobs)):
            if expired():
                deferred.extend(paths[start:])
                break
            out += run_batch(paths[start:start + max(1, jobs)], jobs, timeout)
        return out

    # One `lake build` for every changed module: each separate invocation
    # re-traverses the whole dependency graph, which for a change touching
    # hundreds of modules costs more than the step's timeout. A failure falls
    # back to one build per module, so that each failure is attributed to its
    # own source and independent sources are still checked.
    source_modules = sorted({module_of(source) for source in sources})
    joint_failure: int | None = None
    if len(source_modules) > 1:
        print(f"Preparing {len(source_modules)} focused targets together", flush=True)
        code = build(source_modules)
        if code == 0:
            prepared.update(dict.fromkeys(source_modules, True))
        elif code is None:
            unprepared.update(source_modules)
        else:
            joint_failure = code
    ready_sources = [source for source in sources if prepare(module_of(source))]
    if joint_failure is not None and unprepared and not failed:
        # The budget ended before the fallback reached the failing module; the
        # failure was observed all the same.
        failed.append(f"joint dependency build exited {joint_failure}; the budget ended "
                      "before the failing module was identified")
    deferred += [source for source in sources if module_of(source) in unprepared]
    if ready_sources:
        failed += check(ready_sources)
    if failed:
        print("Focused checks failed:", *failed, sep="\n  ", flush=True)
        return 1
    if deferred:
        print(f"::warning::Focused checks stopped at their {budget}s budget; the root build "
              f"and the post-build strict checks cover the remaining {len(deferred)} "
              "target(s).", flush=True)
        return 0
    print("All focused checks passed.", flush=True)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["early", "strict", "list", "focused"])
    parser.add_argument("--base", default=os.environ.get("BASE_SHA") or None,
                        help="base revision; omit to select no changed source")
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
                        help="early, focused: stop after this many seconds and leave the "
                             "rest to the root build and the post-build strict checks "
                             "(0 means no limit)")
    args = parser.parse_args(argv)

    os.chdir(args.root)
    if args.command == "focused":
        try:
            sources = select_focused(Path("."), args.base, args.head)
            # Match the later strict phase's verified-merge selection. In a
            # feature-head/unknown checkout it has no production-source coverage.
            strict_base = selection_base(args.base, args.pr_head or args.head)
            strict_sources = changed_sources(Path("."), strict_base) if strict_base else []
            sources = focused_sources(Path("."), sources, strict_sources)
            return focused_checks(sources, args.jobs, args.timeout, args.log, args.budget)
        except (ValueError, OSError, subprocess.CalledProcessError) as exc:
            print(f"::error::Focused checks could not complete: {exc}", file=sys.stderr)
            return 1
    args.base = selection_base(args.base, args.pr_head)
    early, sources = select(Path("."), args.base)

    if args.command == "list":
        for m in early:
            print("early", m)
        for s in sources:
            print("source", s)
        return 0

    if args.command == "early":
        if not early:
            print("No changed production modules to build early.")
            return 0
        print("Building changed modules early:", *early, sep="\n  ", flush=True)
        return early_build(early, args.log, args.budget)

    print(f"Strict checks: {len(sources)} changed source file(s).", flush=True)
    failed = run_batch(sources, args.jobs, args.timeout)
    if failed:
        print(f"{len(failed)} strict Lean check(s) failed:", *failed, sep="\n  ")
        return 1
    print("All strict Lean checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
