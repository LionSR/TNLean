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
    proposed_ranges: set[tuple[str, int, int]] = set()
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
        proposed_range = (source, start, end)
        if proposed_range in proposed_ranges:
            raise SystemExit(f"duplicate target range: {source} {start}-{end}")
        proposed_ranges.add(proposed_range)
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

    unowned_blocks: set[tuple[str, int, int]] = set()
    for source in SECTIONS.values():
        source_path = args.source_root / source
        lines = source_path.read_text(encoding="utf-8").splitlines()
        label_groups: list[list[int]] = []
        for line_number, line in enumerate(lines, 1):
            match = re.match(r"^\s*%{2,4}(?!%)(.*)$", line)
            if match is None:
                continue
            label = match.group(1).strip()
            if not label or label.startswith(NON_LABEL_PREFIXES):
                continue
            if label_groups:
                previous_label = label_groups[-1][-1]
                between = lines[previous_label : line_number - 1]
                if all(not item.strip().lstrip("%").strip() for item in between):
                    label_groups[-1].append(line_number)
                    continue
            label_groups.append([line_number])

        for index, group in enumerate(label_groups):
            block_start = group[0]
            block_end = (
                label_groups[index + 1][0] - 1
                if index + 1 < len(label_groups)
                else len(lines)
            )
            for line_number in range(block_start + 1, block_end + 1):
                if lines[line_number - 1].strip().startswith(
                    ("\\end{tikzpicture}", "\\end{document}")
                ):
                    block_end = line_number - 1
                    break
            if not any(
                block_start <= end and start <= block_end
                for start, end, _ in owned.get(source, [])
            ):
                unowned_blocks.add((source, block_start, block_end))
    if proposed_ranges != unowned_blocks:
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
