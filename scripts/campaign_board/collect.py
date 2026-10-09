#!/usr/bin/env python3
"""Collect a snapshot of a formalization campaign from GitHub and git.

    python3 scripts/campaign_board/collect.py CAMPAIGN_DIR OUT.json

CAMPAIGN_DIR holds the campaign's config.json (see docs/campaign/README.md).
Run from the root of the primary repository. Requires `gh` with read access
(GH_TOKEN) and a checkout with an `origin/main` ref for every repository in the
config; a repository's checkout path can be overridden by the environment
variable named in its `checkoutEnv` field.

The snapshot holds:
- the issues of the primary repository carrying the campaign label, with their
  parent, sub-issue and blocking relations;
- pull requests of every repository that carry the label, or that were opened
  since `since` and cite a campaign issue of the primary repository;
- per pull request: Lean lines added and deleted, `sorry` added to Lean files,
  `\\leanok` added to blueprint chapters, and paper-gap notes touched;
- the paper-result tables of the stream trackers;
- paper-gap notes and blueprint chapters on `main` that cite the sources;
- `sorry` on `main` in Lean files touched by merged campaign pull requests.
"""
from __future__ import annotations

import datetime
import json
import os
import pathlib
import re
import subprocess
import sys
import time

# The sorry badge's Lean-aware stripper (nested block comments and string literals).
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from generate_badges import strip_lean_comments_and_strings  # noqa: E402

THEOREM_KINDS = r"Theorem|Lemma|Proposition|Corollary|Definition|Remark"


# --------------------------------------------------------------------------- tools

TRANSIENT = re.compile(r"rate limit|secondary|abuse|timed? ?out|50[0234]|Something went wrong|EOF|connection reset", re.I)


class CommandError(subprocess.CalledProcessError):
    """A failed command whose message includes its error output."""

    def __str__(self) -> str:
        return f"{' '.join(map(str, self.cmd[:3]))} failed: {(self.stderr or self.output or '').strip()[:800]}"


def run(*args: str, attempts: int = 4) -> str:
    """Run a command and return its output.

    The workflow's token shares an hourly quota with every other workflow of the
    repository, so rate limits, timeouts and 5xx responses are retried with
    growing waits. Other failures, such as a missing file, are raised at once.
    """
    for attempt in range(attempts):
        proc = subprocess.run(args, capture_output=True, text=True)
        if proc.returncode == 0:
            return proc.stdout
        if attempt + 1 == attempts or not TRANSIENT.search(proc.stderr + proc.stdout):
            raise CommandError(proc.returncode, args, proc.stdout, proc.stderr)
        time.sleep(30 * 2 ** attempt)
    raise AssertionError("unreachable")


def gh_api(path: str) -> list | dict:
    """GET a REST endpoint, following pagination; list endpoints return one flat list."""
    pages = json.loads(run("gh", "api", "--paginate", "--slurp", path))
    if pages and isinstance(pages[0], list):
        return [item for page in pages for item in page]
    return pages[0] if len(pages) == 1 else pages


def graphql(query: str, **variables) -> dict:
    args = ["gh", "api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        args += ["-F" if isinstance(value, int) else "-f", f"{key}={value}"]
    return json.loads(run(*args))["data"]


def search(query: str, fields: str) -> list[dict]:
    """All results of a GitHub issue/PR search."""
    results, cursor = [], None
    gql = """query($q: String!, $after: String) {
      search(query: $q, type: ISSUE, first: 50, after: $after) {
        pageInfo { hasNextPage endCursor }
        nodes { %s }
      }
    }""" % fields
    while True:
        data = graphql(gql, q=query, **({"after": cursor} if cursor else {}))["search"]
        results += [node for node in data["nodes"] if node]
        if not data["pageInfo"]["hasNextPage"]:
            return results
        cursor = data["pageInfo"]["endCursor"]


class Checkout:
    """Read-only access to `origin/main` of a local clone."""

    def __init__(self, path: str):
        self.path = path

    def fetch(self) -> None:
        subprocess.run(["git", "-C", self.path, "fetch", "-q", "origin", "main"], check=False)

    def files(self, directory: str) -> list[str]:
        try:
            return run("git", "-C", self.path, "ls-tree", "-r", "--name-only", "origin/main", directory).split()
        except subprocess.CalledProcessError:
            return []

    def read(self, path: str) -> str | None:
        try:
            return run("git", "-C", self.path, "show", f"origin/main:{path}")
        except subprocess.CalledProcessError:
            return None

    def short_head(self) -> str:
        return run("git", "-C", self.path, "rev-parse", "--short", "origin/main").strip()


def count_sorry(source: str) -> int:
    """Occurrences of `sorry` outside comments and string literals of a complete Lean file."""
    return len(re.findall(r"\bsorry\b", strip_lean_comments_and_strings(source)))


def raw_file(repo_slug: str, path: str, ref: str) -> str:
    """A file at a commit, or the empty string when it does not exist there."""
    try:
        return run("gh", "api", f"repos/{repo_slug}/contents/{path}?ref={ref}", "-H", "Accept: application/vnd.github.raw")
    except subprocess.CalledProcessError:
        return ""


# ------------------------------------------------------------------------- issues

ISSUE_FIELDS = """... on Issue {
  number title state url createdAt closedAt
  labels(first: 20) { nodes { name } }
  parent { number }
  subIssues(first: 100) { nodes { number } }
  blockedBy(first: 50) { nodes { number } }
}"""


def collect_issues(repo: dict, label: str) -> list[dict]:
    issues = search(f"repo:{repo['slug']} is:issue label:{label}", ISSUE_FIELDS)
    for issue in issues:
        issue["labels"] = [l["name"] for l in issue["labels"]["nodes"]]
        issue["parent"] = (issue["parent"] or {}).get("number")
        issue["subIssues"] = [s["number"] for s in issue["subIssues"]["nodes"]]
        issue["blockedBy"] = [b["number"] for b in issue["blockedBy"]["nodes"]]
    return sorted(issues, key=lambda i: i["number"])


def streams_of(tracker: int, issues: list[dict], names: dict[str, str]) -> list[dict]:
    """The tracker's sub-issues that have sub-issues of their own, in tracker order."""
    by_number = {i["number"]: i for i in issues}
    streams = []
    for number in by_number.get(tracker, {}).get("subIssues", []):
        issue = by_number.get(number)
        if issue and issue["subIssues"]:
            name = names.get(str(number)) or re.sub(r"^Tracking:\s*", "", issue["title"])
            streams.append({"issue": number, "name": name})
    return streams


def result_table(body: str) -> list[dict]:
    """Rows of the markdown tables in a tracker body that name a numbered paper result.

    A row qualifies when one of its first two cells names a result such as
    `Lemma 2.1`. The source label is the first backticked `kind:name` token, the
    issues are the `#NNNN` references in the third cell, and a name, if any,
    follows an em dash after the label.
    """
    rows = []
    for line in body.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        head = " ".join(cells[:2])
        kind = re.search(rf"\b({THEOREM_KINDS}) (\d+(?:\.\d+)*)", head)
        label = re.search(r"`([a-z]+:[^`]+)`", head)
        if not kind or not label:
            continue
        link = re.search(r"\]\((https?://[^)\s]+)\)", line)
        name = re.search(r"`[^`]+`\)?\s+—\s+(.+)$", cells[1])
        rows.append({
            "kind": kind.group(1), "num": kind.group(2), "label": label.group(1),
            "url": link.group(1) if link else None,
            "name": name.group(1).strip() if name else None,
            "issues": [int(n) for n in re.findall(r"#(\d{4,})", cells[2])],
            "gate": cells[3] if len(cells) > 3 else None,
        })
    return rows


# -------------------------------------------------------------------- pull requests

PR_FIELDS = """... on PullRequest {
  number title state isDraft url createdAt mergedAt closedAt
  additions deletions changedFiles headRefOid baseRefOid baseRefName mergeable body
  labels(first: 20) { nodes { name } }
  closingIssuesReferences(first: 20) { nodes { number } }
  commits(last: 1) { nodes { commit { statusCheckRollup { state } } } }
}"""


def file_stats(repo_slug: str, number: int, head: str, base: str) -> dict:
    """Line, `sorry` and `\\leanok` counts from the full, paginated file list of a PR.

    `sorry` is counted exactly, as the change in occurrences between the base and
    head versions of each Lean file. The two files are fetched only when an added
    line mentions `sorry`, which keeps the request count low.
    """
    stats = {"leanAdd": 0, "leanDel": 0, "sorryAdded": 0, "leanokAdded": 0, "leanFiles": [], "gapFiles": []}
    for f in gh_api(f"repos/{repo_slug}/pulls/{number}/files?per_page=100"):
        path = f["filename"]
        added = [l[1:] for l in (f.get("patch") or "").splitlines() if l.startswith("+") and not l.startswith("+++")]
        if path.endswith(".lean"):
            stats["leanAdd"] += f["additions"]
            stats["leanDel"] += f["deletions"]
            stats["leanFiles"].append(path)
            if any("sorry" in line for line in added):
                before = "" if f["status"] == "added" else raw_file(repo_slug, f.get("previous_filename", path), base)
                stats["sorryAdded"] += max(0, count_sorry(raw_file(repo_slug, path, head)) - count_sorry(before))
        elif path.startswith("blueprint/") and path.endswith(".tex"):
            stats["leanokAdded"] += sum(l.count("\\leanok") for l in added)
        if re.match(r"docs/paper-gaps/.*\.tex$", path):
            stats["gapFiles"].append(path)
    return stats


def collect_prs(cfg: dict, campaign_issues: set[int], cache: dict | None = None) -> list[dict]:
    """Campaign pull requests. File statistics are reused from `cache`, keyed by
    (repository, number, head commit), so unchanged pull requests cost no request."""
    cache = cache or {}
    primary = next(r for r in cfg["repos"] if r.get("primary"))
    # A companion repository refers to primary issues as `TNLean#123` or by URL.
    cross_ref = re.compile(rf"{re.escape(primary['name'])}(?:#|/issues/)(\d{{4,}})")
    local_ref = re.compile(r"#(\d{4,})\b")
    prs = []
    for repo in cfg["repos"]:
        found = {p["number"]: p for p in search(f"repo:{repo['slug']} is:pr label:{cfg['label']}", PR_FIELDS)}
        if not repo.get("primary"):
            # Companion repositories may lag in labelling: also take recent PRs citing a campaign issue.
            for p in search(f"repo:{repo['slug']} is:pr created:>={cfg['since']}", PR_FIELDS):
                if {int(n) for n in cross_ref.findall(p["body"] or "")} & campaign_issues:
                    found.setdefault(p["number"], p)
        refs = local_ref if repo.get("primary") else cross_ref
        for p in found.values():
            referenced = {int(n) for n in refs.findall(p.pop("body") or "")}
            closing = {n["number"] for n in p.pop("closingIssuesReferences")["nodes"]}
            rollup = p.pop("commits")["nodes"]
            prs.append({
                **p,
                "repo": repo["name"],
                "labels": [l["name"] for l in p["labels"]["nodes"]],
                "closes": sorted(closing & campaign_issues),
                "refs": sorted((referenced & campaign_issues) - closing),
                "ci": (rollup[0]["commit"]["statusCheckRollup"] or {}).get("state") if rollup else None,
                **(cache.get((repo["name"], p["number"], p["headRefOid"], p["baseRefOid"]))
                   or file_stats(repo["slug"], p["number"], p["headRefOid"], p["baseRefOid"])),
            })
    return sorted(prs, key=lambda p: (p["repo"], p["number"]))


# ------------------------------------------------------------- notes and blueprint

def note_meta(source: str) -> dict:
    title = re.search(r"\\title\{(.*?)\}", source, re.S)
    verdict = re.search(r"\\gapnote\{([^}]*)\}\{([^}]*)\}", source)
    return {"title": " ".join(title.group(1).split()) if title else "",
            "kind": verdict.group(1) if verdict else "", "status": verdict.group(2) if verdict else ""}


def gap_notes(cfg: dict, checkouts: dict[str, Checkout], prs: list[dict], cites: re.Pattern) -> list[dict]:
    """Paper-gap notes that cite the sources, on main and in campaign pull requests."""
    notes: dict[tuple[str, str], dict] = {}
    for repo in cfg["repos"]:
        checkout = checkouts[repo["name"]]
        for path in checkout.files("docs/paper-gaps"):
            source = checkout.read(path) if path.endswith(".tex") else None
            if source and cites.search(source):
                notes[(repo["name"], path)] = {"repo": repo["name"], "path": path, "onMain": True, "prs": [], **note_meta(source)}
    slugs = {r["name"]: r["slug"] for r in cfg["repos"]}
    # A note touched by open pull requests is read from the newest of them, which
    # carries its latest version (for example a status changed to resolved).
    refreshed: set[tuple[str, str]] = set()
    for pr in sorted(prs, key=lambda p: p["number"], reverse=True):
        for path in pr["gapFiles"]:
            key = (pr["repo"], path)
            if key not in refreshed and (pr["state"] == "OPEN" or key not in notes):
                source = raw_file(slugs[pr["repo"]], path, pr["headRefOid"])
                if source and cites.search(source):
                    on_main = key in notes and notes[key]["onMain"]
                    notes[key] = {"repo": pr["repo"], "path": path, "onMain": on_main,
                                  "prs": notes.get(key, {}).get("prs", []), **note_meta(source)}
                    refreshed.add(key)
            if key in notes:
                notes[key]["prs"].append({"number": pr["number"], "state": pr["state"]})
    return list(notes.values())


BLUEPRINT_ENV = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}(.*?)\\end\{\1\}"
    r"(\s*\\begin\{proof\}(.*?)\\end\{proof\})?", re.S)


def blueprint_status(cfg: dict, checkouts: dict[str, Checkout], cites: re.Pattern) -> list[dict]:
    """Per blueprint chapter on main that cites the sources: statements by formalization status."""
    chapters = []
    for repo in cfg["repos"]:
        checkout = checkouts[repo["name"]]
        for path in checkout.files("blueprint/src/chapter"):
            source = checkout.read(path) if path.endswith(".tex") else None
            if not source or not cites.search(source):
                continue
            count = {"proved": 0, "stated": 0, "unformalized": 0, "notready": 0}
            for kind, statement, _, proof in BLUEPRINT_ENV.findall(source):
                if "\\notready" in statement:
                    count["notready"] += 1
                elif "\\leanok" not in statement:
                    count["unformalized"] += 1
                elif kind == "definition" or not proof or "\\leanok" in proof:
                    count["proved"] += 1
                else:
                    count["stated"] += 1
            title = re.search(r"\\chapter\{(.*?)\}", source)
            chapters.append({"repo": repo["name"], "path": path,
                             "title": title.group(1) if title else pathlib.Path(path).stem, **count})
    return chapters


def sorry_on_main(cfg: dict, checkouts: dict[str, Checkout], prs: list[dict]) -> list[dict]:
    hits = []
    for repo in cfg["repos"]:
        files = sorted({f for p in prs if p["repo"] == repo["name"] and p["state"] == "MERGED" for f in p["leanFiles"]})
        for path in files:
            source = checkouts[repo["name"]].read(path)
            if source and (n := count_sorry(source)):
                hits.append({"repo": repo["name"], "path": path, "count": n})
    return hits


def lean_footprint(checkout: Checkout, directories: list[str]) -> list[dict]:
    files = []
    for directory in directories:
        for path in checkout.files(directory):
            if path.endswith(".lean") and (source := checkout.read(path)) is not None:
                files.append({"path": path, "lines": source.count("\n"), "sorry": count_sorry(source)})
    return files


# ---------------------------------------------------------------------------- main

STAT_KEYS = ("leanAdd", "leanDel", "sorryAdded", "leanokAdded", "leanFiles", "gapFiles")


def previous_stats() -> dict:
    """File statistics from the previously published snapshot ($PREVIOUS_SNAPSHOT), if any."""
    path = os.environ.get("PREVIOUS_SNAPSHOT")
    if not path or not pathlib.Path(path).exists():
        return {}
    try:
        prs = json.loads(pathlib.Path(path).read_text()).get("prs", [])
    except json.JSONDecodeError:
        return {}
    # The file statistics depend on the base commit as well as the head: the
    # diff of an open pull request moves with its base branch.
    return {(p["repo"], p["number"], p.get("headRefOid"), p.get("baseRefOid")): {k: p[k] for k in STAT_KEYS}
            for p in prs if p.get("headRefOid") and p.get("baseRefOid") and all(k in p for k in STAT_KEYS)}


def collect(campaign_dir: pathlib.Path) -> dict:
    cfg = json.loads((campaign_dir / "config.json").read_text())
    checkouts = {r["name"]: Checkout(os.environ.get(r.get("checkoutEnv", ""), r["checkout"])) for r in cfg["repos"]}
    for checkout in checkouts.values():
        checkout.fetch()
    primary = next(r for r in cfg["repos"] if r.get("primary"))
    cites = re.compile(cfg["citationPattern"], re.I)

    issues = collect_issues(primary, cfg["label"])
    by_number = {i["number"]: i for i in issues}
    streams = streams_of(cfg["tracker"], issues, cfg.get("streamNames", {}))
    results = []
    for paper, spec in cfg["papers"].items():
        body = run("gh", "api", f"repos/{primary['slug']}/issues/{spec['stream']}", "--jq", ".body")
        results += [{"paper": paper, **row} for row in result_table(body)]
    prs = collect_prs(cfg, set(by_number), previous_stats())
    return {
        "generatedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="minutes"),
        "mainCommit": checkouts[primary["name"]].short_head(),
        "streams": streams,
        "issues": issues,
        "prs": prs,
        "results": results,
        "gapNotes": gap_notes(cfg, checkouts, prs, cites),
        "blueprint": blueprint_status(cfg, checkouts, cites),
        "sorryOnMain": sorry_on_main(cfg, checkouts, prs),
        "mainFiles": lean_footprint(checkouts[primary["name"]], cfg.get("leanDirs", [])),
    }


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    snapshot = collect(pathlib.Path(sys.argv[1]))
    pathlib.Path(sys.argv[2]).write_text(json.dumps(snapshot, indent=1, ensure_ascii=False))
    print(f"{len(snapshot['issues'])} issues, {len(snapshot['prs'])} pull requests, "
          f"{len(snapshot['gapNotes'])} gap notes -> {sys.argv[2]}")


if __name__ == "__main__":
    main()
