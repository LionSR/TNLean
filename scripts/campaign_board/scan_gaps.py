#!/usr/bin/env python3
"""List candidate source-gap reports in a campaign's issues and pull requests.

    python3 scripts/campaign_board/scan_gaps.py CAMPAIGN_DIR [--since ISO_TIME]

Prints, for every labelled issue or pull request of every repository in the
campaign config, the passages of its body and comments that mention a gap,
counterexample, deviation marker or similar wording, followed by the deviation
markers in the campaign's Lean directories on main. Passages repeated across
many items (checklist boilerplate) are printed once. The output is for a reader
deciding whether docs/campaign/<slug>/gaps.json needs a new entry; this script
decides nothing.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import subprocess
import sys

PATTERN = re.compile(
    r"paper[- ]gap|source gap|gap in (?:the )?(?:source|paper|proof|manuscript)|counterexample|erratum|typo|"
    r"as printed|printed (?:statement|claim|bound|proof)|does not (?:hold|follow)|is false|fails (?:for|when|on)|"
    r"missing hypothes|extra hypothes|unfaithful|local fix|scope restriction|incorrect|off[- ]by[- ]one|"
    r"wrong (?:sign|exponent|constant)|cannot be proved|unprovable|unjustified|no paper gap", re.I)
MARKERS = r"\*\*(Unfaithful|Local fix|Scope restriction)"


def passages(text: str, width: int = 260) -> list[str]:
    found = []
    for m in PATTERN.finditer(text or ""):
        start, end = max(0, m.start() - width // 2), min(len(text), m.end() + width // 2)
        found.append(" ".join(text[start:end].split()))
    return found


def main() -> None:
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    since = args[args.index("--since") + 1] if "--since" in args else None
    cfg = json.loads((pathlib.Path(args[0]) / "config.json").read_text())

    items = []
    for repo in cfg["repos"]:
        for kind in ("issue", "pr"):
            listing = subprocess.check_output(
                ["gh", kind, "list", "-R", repo["slug"], "--label", cfg["label"], "--state", "all", "--limit", "500",
                 "--json", "number,title,body,comments,updatedAt,url"], text=True)
            for item in json.loads(listing):
                if since and item["updatedAt"] < since:
                    continue
                texts = [("body", item.get("body") or "")]
                texts += [(f"comment by {c['author']['login']} at {c['createdAt'][:16]}", c.get("body") or "") for c in item.get("comments", [])]
                hits = [(where, p) for where, text in texts for p in passages(text)]
                if hits:
                    items.append((repo["name"], kind, item, hits))

    seen = collections.Counter(p[:120] for *_, hits in items for _, p in hits)
    printed_boilerplate = set()
    for repo, kind, item, hits in items:
        lines = []
        for where, p in hits:
            key = p[:120]
            if seen[key] > 3:
                if key in printed_boilerplate:
                    continue
                printed_boilerplate.add(key)
                where += f", repeated in {seen[key]} items"
            lines.append(f"  [{where}] …{p}…")
        if lines:
            print(f"\n## {repo} {kind} #{item['number']}: {item['title']}\n{item['url']}")
            print("\n".join(dict.fromkeys(lines)))

    primary = next(r for r in cfg["repos"] if r.get("primary"))
    try:
        markers = subprocess.check_output(["git", "-C", primary["checkout"], "grep", "-n", "-E", MARKERS, "origin/main", "--",
                                           *cfg.get("leanDirs", [])], text=True)
    except subprocess.CalledProcessError:
        markers = ""
    if markers.strip():
        print("\n## Deviation markers on main\n" + markers)


if __name__ == "__main__":
    main()
