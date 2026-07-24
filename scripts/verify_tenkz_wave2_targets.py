#!/usr/bin/env python3
"""Check that documented wave-2 ranges are in-bounds and unowned."""

from __future__ import annotations

import argparse
import re
import tomllib
from collections import Counter
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
SECTIONS = {
    "II": "ImagesReview Section II/ImagesReview Section II.tex",
    "III": "ImagesReview Section III/ImagesReview Section III.tex",
    "IV": "ImagesReview Section IV/ImagesReview Section IV.tex",
    "V": "ImagesReview Section V/ImagesReview Section V.tex",
}
ROW = re.compile(
    r"^\| `(?P<id>rmp-w2-[^`]+)` .* "
    r"\| (?P<section>II|III|IV|V):(?P<start>\d+)-(?P<end>\d+) "
    r"\| (?P<capabilities>[^|]+) \|$"
)
DEMAND_ROW = re.compile(
    r"^\| `(?P<capability>[^`]+)` \| (?P<blocked>\d+) "
    r"\| (?P<wave2>\d+) \| (?P<total>\d+) \|$"
)
NON_LABEL_PREFIXES = (
    "\\",
    "}",
    "every picture/.style",
    "baseline=",
    "scale=",
    "transform shape",
    "font=",
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source-root",
        type=Path,
        default=REPO / "tex" / "RMP_TIKZ_SOURCE_CODE",
    )
    args = parser.parse_args()

    manifest = tomllib.loads(
        (REPO / "tests" / "tenkz" / "rmp" / "manifest.toml").read_text()
    )
    owned: dict[str, list[tuple[int, int, str]]] = {}
    for target in manifest["target"]:
        source = target.get("author_source")
        line_range = target.get("author_lines")
        if source is None or line_range is None:
            continue
        start_text, _, end_text = line_range.partition("-")
        start = int(start_text)
        end = int(end_text or start_text)
        owned.setdefault(source, []).append((start, end, target["id"]))

    document = (REPO / "docs" / "tenkz" / "wave2-targets.md").read_text()
    rows = [match.groupdict() for line in document.splitlines() if (match := ROW.match(line))]
    if not rows:
        raise SystemExit("no rmp-w2 target rows found")

    seen_ids: set[str] = set()
    proposed_starts: set[tuple[str, int]] = set()
    proposed: Counter[str] = Counter()
    allowed = {capability for target in manifest["target"] for capability in target["capabilities"]}
    verdicts = tomllib.loads(
        (REPO / "tests" / "tenkz" / "rmp" / "verdicts.toml").read_text()
    )
    blocked: Counter[str] = Counter()
    for verdict in verdicts["verdict"]:
        if verdict.get("status") == "blocked":
            blocked.update(verdict.get("missing", []))
    allowed.update(blocked)

    for row in rows:
        target_id = row["id"]
        if target_id in seen_ids:
            raise SystemExit(f"duplicate target id: {target_id}")
        seen_ids.add(target_id)

        source = SECTIONS[row["section"]]
        start, end = int(row["start"]), int(row["end"])
        proposed_starts.add((source, start))
        source_path = args.source_root / source
        line_count = len(source_path.read_text(encoding="utf-8").splitlines())
        if not 1 <= start <= end <= line_count:
            raise SystemExit(
                f"{target_id}: {start}-{end} lies outside {source} (1-{line_count})"
            )
        overlaps = [
            owner
            for owned_start, owned_end, owner in owned.get(source, [])
            if start <= owned_end and owned_start <= end
        ]
        if overlaps:
            raise SystemExit(
                f"{target_id}: {source} {start}-{end} overlaps {', '.join(overlaps)}"
            )

        capabilities = re.findall(r"`([^`]+)`", row["capabilities"])
        unknown = sorted(set(capabilities) - allowed)
        if unknown:
            raise SystemExit(f"{target_id}: unknown capabilities: {', '.join(unknown)}")
        proposed.update(capabilities)

    unowned_labels: set[tuple[str, int]] = set()
    for source in SECTIONS.values():
        source_path = args.source_root / source
        for line_number, line in enumerate(source_path.read_text(encoding="utf-8").splitlines(), 1):
            match = re.match(r"^\s*%{2,4}(?!%)(.*)$", line)
            if match is None:
                continue
            label = match.group(1).strip()
            if not label or label.startswith(NON_LABEL_PREFIXES):
                continue
            if not any(start <= line_number <= end for start, end, _ in owned.get(source, [])):
                unowned_labels.add((source, line_number))
    if proposed_starts != unowned_labels:
        raise SystemExit("proposed targets do not exhaust the unowned labelled blocks")

    reported = {}
    for line in document.splitlines():
        if match := DEMAND_ROW.match(line):
            values = match.groupdict()
            reported[values["capability"]] = (
                int(values["blocked"]),
                int(values["wave2"]),
                int(values["total"]),
            )
    expected = {
        capability: (
            blocked[capability],
            proposed[capability],
            blocked[capability] + proposed[capability],
        )
        for capability in blocked.keys() | proposed.keys()
    }
    if reported != expected:
        raise SystemExit("capability demand table does not match targets and verdicts")

    print(
        f"verified {len(rows)} exhaustive wave-2 ranges: in-bounds, unique, "
        "and unowned; capability demand matches verdicts"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
