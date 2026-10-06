#!/usr/bin/env python3
"""Fail-closed, dependency-only CI seed across an additive QICLean pin update.

This never saves a cache or edits Lake traces. It deliberately drops TNLean's
cross-commit build; the existing exact-input restore path is unchanged.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib
import urllib.parse
import urllib.request

from lean_import_syntax import pure_import_modules

INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
PATHS = (".lake/build", *(f".lake/packages/{p}/.lake/build" for p in
                         ("Gametheory", "checkdecls", "qiclean")))
KEY = "tnlean-build-${{ hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.toml') }}-${{ github.sha }}"
QIC_URL = "https://github.com/LionSR/QICLean.git"
SHA = re.compile(r"[0-9a-f]{40}")
MANIFEST_FIELDS = {"version", "packagesDir", "packages", "name", "lakeDir", "fixedToolchain"}
PACKAGE_FIELDS = {"url", "type", "subDir", "scope", "rev", "name", "manifestFile",
                  "inputRev", "inherited", "configFile"}
WINDOW = 64


class Refusal(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise Refusal(reason)


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], stderr=subprocess.PIPE)


def file_at(repo, commit, path):
    return git(repo, "show", f"{commit}:{path}")


def config_at(repo, commit):
    require(not git(repo, "ls-tree", commit, "--", "lakefile.lean").strip(),
            "unvalidated root lakefile.lean")
    return {p: file_at(repo, commit, p) for p in INPUTS}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate manifest field")
        result[key] = value
    return result


def manifest(raw):
    data = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(data, dict) and set(data) == MANIFEST_FIELDS,
            "unknown root manifest schema")
    require(data["version"] == "1.3.0" and data["packagesDir"] == ".lake/packages"
            and data["lakeDir"] == ".lake" and data["name"] == "TNLean"
            and data["fixedToolchain"] is False, "unsupported root manifest layout")
    require(isinstance(data["packages"], list), "packages is not a list")
    names = set()
    for package in data["packages"]:
        require(isinstance(package, dict) and set(package) == PACKAGE_FIELDS,
                "unknown resolved package schema")
        require(package["type"] == "git" and isinstance(package["rev"], str)
                and SHA.fullmatch(package["rev"]), "dependency is not an immutable Git pin")
        require(isinstance(package["name"], str) and package["name"] not in names,
                "missing or duplicate package name")
        names.add(package["name"])
    require({"qiclean", "mathlib", "Gametheory", "checkdecls"} <= names,
            "required resolved dependency missing")
    return data


def compatible_configs(old, new):
    """Only the two resolved QIC revisions and its TOML revision may differ."""
    require(set(old) == set(INPUTS) and set(new) == set(INPUTS), "missing root input")
    require(old["lean-toolchain"] == new["lean-toolchain"], "toolchain differs")
    a, b = manifest(old["lake-manifest.json"]), manifest(new["lake-manifest.json"])
    qa = next(p for p in a["packages"] if p["name"] == "qiclean")
    qb = next(p for p in b["packages"] if p["name"] == "qiclean")
    revisions = (qa["rev"], qb["rev"])
    require(revisions[0] != revisions[1], "QIC pin did not change")
    for q in (qa, qb):
        require(q["url"] == QIC_URL and q["subDir"] is None
                and q["configFile"] == "lakefile.toml"
                and q["manifestFile"] == "lake-manifest.json"
                and q["inputRev"] == q["rev"], "unsupported QIC identity or revision")
        q["rev"] = q["inputRev"] = "<QIC revision>"
    require(a == b, "root resolved dependencies differ beyond QIC revision")
    configs = [tomllib.loads(c["lakefile.toml"].decode()) for c in (old, new)]
    for config, rev in zip(configs, revisions):
        requirements = config.get("require")
        require(isinstance(requirements, list), "missing TOML requirements")
        qs = [p for p in requirements if p.get("name") == "qiclean"]
        require(len(qs) == 1 and qs[0].get("rev") == rev
                and qs[0].get("git") == QIC_URL, "TOML QIC pin disagrees with manifest")
        qs[0]["rev"] = "<QIC revision>"
    require(configs[0] == configs[1], "root options/configuration differ")
    return revisions


def tree(repo, commit):
    entries = {}
    for line in git(repo, "ls-tree", "-rz", commit).split(b"\0"):
        if line:
            header, path = line.split(b"\t", 1)
            mode, kind, blob = header.decode().split()
            entries[path.decode()] = (mode, kind, blob)
    return entries


def additive_qic(repo, old, new):
    """Existing proof source is identical; aggregators may only import additions."""
    require(SHA.fullmatch(old) and SHA.fullmatch(new), "QIC revisions must be full SHAs")
    a, b = tree(repo, old), tree(repo, new)
    for p in INPUTS:
        require(p in a and p in b and a[p] == b[p], f"QIC metadata differs/missing: {p}")
    require("lakefile.lean" not in a and "lakefile.lean" not in b,
            "unvalidated QIC lakefile.lean")
    added = {p[:-5].replace("/", ".") for p in b.keys() - a.keys()
             if p.startswith("QICLean/") and p.endswith(".lean")}
    require(added, "no added QIC module")
    aggregators = []
    for p in a.keys() | b.keys():
        if a.get(p) == b.get(p):
            continue
        if ((p.startswith("docs/") and p.endswith(".md"))
                or (p.startswith("blueprint/") and p.endswith((".md", ".tex")))):
            continue
        require(p.startswith("QICLean/") and p.endswith(".lean")
                and p in b and b[p][:2] == ("100644", "blob"),
                f"QIC change is not a regular added module/aggregator: {p}")
        if p not in a:
            continue
        before, e1 = pure_import_modules(file_at(repo, old, p).decode())
        after, e2 = pure_import_modules(file_at(repo, new, p).decode())
        require(not e1 and not e2 and set(before) <= set(after)
                and set(after) - set(before) <= added,
                f"QIC existing source is not an additive aggregator: {p}")
        aggregators.append(p[:-5].replace("/", "."))
    return aggregators


def aggregator_closure(read_source, root):
    """Modules guaranteed built by a root's ordinary import-only aggregators.

    Non-aggregator modules are leaves here; Lake itself follows their imports.
    This under-approximation is safe: unrecognized/unreachable artifacts go away.
    """
    seen, pending = set(), [root]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = read_source(module)
        if source is None:
            continue
        imports, error = pure_import_modules(source)
        if not error:
            pending.extend(imports)
    return seen


def require_qic_build(root):
    config = tomllib.loads((root / "lakefile.toml").read_text())
    require(config.get("defaultTargets") == ["TNLean"], "unvalidated default build target")
    def read(module):
        path = root / (module.replace(".", "/") + ".lean")
        return path.read_text() if path.is_file() else None
    require("QICLean" in aggregator_closure(read, "TNLean"),
            "full TNLean build is not guaranteed to import QICLean")


def output(**values):
    with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
        for key, value in values.items():
            stream.write(f"{key}={value}\n")


def select_baseline(root, current, commits):
    for commit in commits[:WINDOW]:
        try:
            baseline = config_at(root, commit)
            revisions = compatible_configs(baseline, current)
            return commit, baseline, revisions
        except (Refusal, subprocess.CalledProcessError, ValueError):
            continue
    raise Refusal(f"no compatible main configuration in {WINDOW}-commit window")


def prepare(root, state, inputs, qic):
    require_qic_build(root)
    current = config_at(root, "HEAD")
    # Freeze main independently of the PR base (including stacked PRs). Never
    # search the PR's first-parent history for a supposedly trusted baseline.
    git(root, "fetch", "--no-tags", "origin",
        "+refs/heads/main:refs/remotes/origin/ci-cache-main")
    commits = git(root, "rev-list", "--first-parent", f"--max-count={WINDOW}",
                  "refs/remotes/origin/ci-cache-main").decode().splitlines()
    selected, baseline, revisions = select_baseline(root, current, commits)
    require(not qic.exists(), "QIC evidence directory already exists")
    qic.mkdir(parents=True)
    git(qic, "init", "--bare")
    for rev in revisions:
        git(qic, "fetch", "--no-tags", "--depth=1", QIC_URL, rev)
    changed = additive_qic(qic, *revisions)
    require(not inputs.exists(), "baseline input directory already exists")
    inputs.mkdir(parents=True)
    for path, data in baseline.items():
        (inputs / path).write_bytes(data)
    state.write_text(json.dumps({"commits": commits, "baseline": selected,
                                 "revisions": revisions, "aggregators": changed}))
    output(eligible="true", baseline=selected)
    print(f"Eligible additive QIC transition {revisions[0]} -> {revisions[1]}; baseline {selected}")


def api(path):
    # This repository is public. Read public metadata without collecting a token
    # or requesting any Actions permissions; unavailable evidence refuses reuse.
    repo = os.environ["GITHUB_REPOSITORY"]
    require(repo == "LionSR/TNLean", "public TNLean provenance only")
    request = urllib.request.Request(f"https://api.github.com/repos/{repo}/{path}", headers={
        "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"})
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def source_workflow(raw):
    # A parsed comparison, not a substring that could accidentally match a
    # comment, a different job, or an obsolete save step.
    import yaml
    workflow = yaml.safe_load(raw)
    build = workflow["jobs"]["build"]
    require(build["runs-on"] == "ubuntu-latest", "source runner platform differs")
    require(tuple(workflow["env"]["BUILD_CACHE_PATHS"].split()) == PATHS,
            "source cache paths differ")
    saves = [s for s in build["steps"] if s.get("uses", "").startswith("actions/cache/save@")]
    require(len(saves) == 1, "source save provenance is ambiguous")
    save = saves[0]
    require(save["uses"] == "actions/cache/save@v6"
            and save.get("if") == "success() && github.ref == 'refs/heads/main'"
            and save["with"] == {"path": "${{ env.BUILD_CACHE_PATHS }}", "key": KEY},
            "source does not follow successful-main-only exact-input save policy")


def validate_provenance(key, commit, caches, runs, jobs):
    require(caches.get("total_count") == 1 and len(caches.get("actions_caches", [])) == 1,
            "cache key has missing/ambiguous scope or version")
    cache = caches["actions_caches"][0]
    require(cache.get("key") == key and cache.get("ref") == "refs/heads/main",
            "cache is not uniquely main-scoped")
    trusted_runs = [r for r in runs.get("workflow_runs", [])
                    if r.get("head_sha") == commit and r.get("head_branch") == "main"
                    and r.get("event") == "push" and r.get("status") == "completed"
                    and r.get("path") == ".github/workflows/pr-ci.yml"]
    for run in trusted_runs:
        for job in jobs.get(run["id"], {}).get("jobs", []):
            if (job.get("name") == "build" and job.get("conclusion") == "success"
                    and job.get("head_sha") == commit
                    and job.get("labels") == ["ubuntu-latest"]):
                saves = [s for s in job.get("steps", [])
                         if s.get("name") == "Save Lean build cache (main only)"]
                if len(saves) == 1 and saves[0].get("conclusion") == "success":
                    return
    raise Refusal("no successful main build/save on the same runner platform")


def validate(root, state, prefix, matched):
    require(re.fullmatch(r"tnlean-build-[0-9a-f]{64}-", prefix), "invalid baseline prefix")
    require(matched.startswith(prefix) and SHA.fullmatch(matched[len(prefix):]),
            "lookup key is not an exact baseline prefix plus full commit")
    require(os.environ.get("RUNNER_OS") == "Linux" and os.environ.get("RUNNER_ARCH") == "X64",
            "current runner platform differs")
    require_qic_build(root)
    require({p: (root / p).read_bytes() for p in INPUTS} == config_at(root, "HEAD"),
            "working root configuration changed since checkout")
    data = json.loads(state.read_text())
    commit = matched[len(prefix):]
    require(commit in data["commits"], "cache commit is not in frozen main first-parent window")
    require(config_at(root, commit) == config_at(root, data["baseline"]),
            "matched commit inputs differ from verified baseline bytes")
    compatible_configs(config_at(root, commit), config_at(root, "HEAD"))
    source_workflow(file_at(root, commit, ".github/workflows/pr-ci.yml"))
    caches = api("actions/caches?" + urllib.parse.urlencode({"key": matched, "per_page": 100}))
    runs = api("actions/workflows/pr-ci.yml/runs?" + urllib.parse.urlencode(
        {"head_sha": commit, "event": "push", "per_page": 20}))
    jobs = {r["id"]: api(f"actions/runs/{r['id']}/jobs?per_page=100")
            for r in runs.get("workflow_runs", [])[:20]
            if r.get("head_sha") == commit and r.get("event") == "push"}
    validate_provenance(matched, commit, caches, runs, jobs)
    output(key=matched)
    print(f"Validated uniquely main-scoped cache {matched}; full build still required")


def discard_unvalidated(root):
    """Cross-commit TNLean and all QIC aggregators must never reach direct Lean.

    Delete QIC compiled artifacts too unless their module has byte-identical
    non-aggregator source. Aggregators can depend on other changed aggregators;
    clearing all of them is deliberately conservative. Other dependency pins
    are immutable and identical. Remove their orphan artifacts as well.
    """
    require_qic_build(root)
    require(not (root / ".lake").is_symlink()
            and not (root / ".lake/packages").is_symlink(), "symlinked Lake directory")
    packages = manifest((root / "lake-manifest.json").read_bytes())["packages"]
    for package in ("Gametheory", "checkdecls", "qiclean"):
        directory = root / ".lake/packages" / package
        expected = next(p["rev"] for p in packages if p["name"] == package)
        require(git(directory, "rev-parse", "HEAD").decode().strip() == expected,
                f"dependency checkout pin mismatch: {package}")
        require(not git(directory, "status", "--porcelain", "--untracked-files=no").strip(),
                f"dependency checkout is modified: {package}")
    qic = root / ".lake/packages/qiclean"
    qic_tree = tree(qic, "HEAD")
    def read(module):
        path = module.replace(".", "/") + ".lean"
        return file_at(qic, "HEAD", path).decode() if path in qic_tree else None
    closure = aggregator_closure(read, "QICLean")
    build = root / ".lake/build"
    require(not build.is_symlink(), "symlinked root build")
    if build.exists():
        shutil.rmtree(build)
    for package in ("Gametheory", "checkdecls", "qiclean"):
        directory = root / ".lake/packages" / package
        build = directory / ".lake/build"
        require(not directory.is_symlink() and not build.is_symlink(), "symlinked dependency build")
        if not build.exists():
            continue
        source_tree = tree(directory, "HEAD")
        # Prune complete artifact families, including .olean.private/server,
        # trace and hash sidecars and IR/C output. Never rewrite a trace/hash.
        for path in sorted(build.rglob("*")):
            require(not path.is_symlink(), "symlinked cached artifact")
            if not path.is_file():
                continue
            rel = path.relative_to(build)
            if rel.parts[:2] == ("lib", "lean"):
                module = Path(*rel.parts[2:])
            elif rel.parts[:1] == ("ir",):
                module = Path(*rel.parts[1:])
            else:
                path.unlink()  # Rebuild executables and any unknown output.
                continue
            stem = str(module).split(".", 1)[0]
            sources = [directory / f"{stem}.lean", directory / "scripts" / f"{stem}.lean"]
            sources = [p for p in sources if source_tree.get(p.relative_to(directory).as_posix(), ())[:2] == ("100644", "blob")
                       and p.is_file() and not p.is_symlink()]
            keep = len(sources) == 1
            if keep and package == "qiclean":
                _, error = pure_import_modules(sources[0].read_text())
                keep = error is not None and stem.replace("/", ".") in closure
                # Rebuild every QIC aggregator; drop unreachable modules.
            if not keep:
                path.unlink()
    print("Dropped cross-commit TNLean, QIC aggregators, orphan and unknown cached artifacts")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "validate", "prune"))
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--state", type=Path)
    parser.add_argument("--inputs", type=Path)
    parser.add_argument("--qic", type=Path)
    parser.add_argument("--prefix", default="")
    parser.add_argument("--matched", default="")
    args = parser.parse_args()
    try:
        if args.phase == "prepare":
            prepare(args.root, args.state, args.inputs, args.qic)
        elif args.phase == "validate":
            validate(args.root, args.state, args.prefix, args.matched)
        else:
            discard_unvalidated(args.root)
    except (Refusal, OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"Compatible cache refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
