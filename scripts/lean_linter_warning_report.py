#!/usr/bin/env python3
"""Parse Lean build logs into linter-warning reports."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

KNOWN_LINTER_NAMES = (
    "style.setOption",
    "flexible",
    "unnecessarySimpa",
    "unusedDecidableInType",
    "unusedFintypeInType",
    "unusedSimpArgs",
    "unusedVariables",
    "unreachableTactic",
    "simpNF",
    "omegaNF",
    "dupNamespace",
    "docPrime",
)

WARNING_RE = re.compile(
    r"^(?P<path>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+): warning: (?P<message>.*)$"
)
LINTER_NOTE_RE = re.compile(r"set_option\s+linter\.([A-Za-z0-9_.]+)\s+false")


@dataclass(frozen=True)
class LeanWarning:
    """A single Lean compiler warning from a build log."""

    path: str
    line: int
    column: int
    category: str
    message: str
    raw: str


def warning_category(message: str, note_lines: Sequence[str]) -> str:
    """Classify a Lean warning using linter note lines when available."""
    note_text = "\n".join(note_lines)
    if note_match := LINTER_NOTE_RE.search(note_text):
        return note_match.group(1)
    return next((name for name in KNOWN_LINTER_NAMES if name in message), "other")


def parse_warnings(log_text: str) -> list[LeanWarning]:
    """Extract Lean warning entries from a build log."""
    raw_lines = log_text.splitlines()
    warnings: list[LeanWarning] = []
    for index, raw_line in enumerate(raw_lines):
        match = WARNING_RE.match(raw_line)
        if not match:
            continue
        note_lines: list[str] = []
        for follow in raw_lines[index + 1 :]:
            if WARNING_RE.match(follow):
                break
            if "set_option linter." in follow:
                note_lines.append(follow)
        message = match.group("message")
        warnings.append(
            LeanWarning(
                path=match.group("path"),
                line=int(match.group("line")),
                column=int(match.group("col")),
                category=warning_category(message, note_lines),
                message=message,
                raw=raw_line,
            )
        )
    return warnings


def report_dict(warnings: Iterable[LeanWarning]) -> dict[str, object]:
    """Return the JSON-serializable summary for a warning collection."""
    warning_list = list(warnings)
    counts = Counter(warning.category for warning in warning_list)
    return {
        "warning_count": len(warning_list),
        "category_counts": dict(sorted(counts.items())),
        "warnings": [asdict(warning) for warning in warning_list],
    }


def render_text_report(warnings: Iterable[LeanWarning]) -> str:
    """Render a human-readable warning report."""
    warning_list = list(warnings)
    counts = Counter(warning.category for warning in warning_list)
    lines = [
        "Lean linter-warning sweep report",
        "=================================",
        f"warnings found: {len(warning_list)}",
        "",
        "category counts:",
    ]
    if counts:
        for category, count in sorted(counts.items()):
            lines.append(f"  - {category}: {count}")
    else:
        lines.append("  - none")
    lines.extend(["", "warnings:"])
    if warning_list:
        for warning in warning_list:
            lines.append(
                f"  - {warning.path}:{warning.line}:{warning.column} "
                f"[{warning.category}] {warning.message}"
            )
    else:
        lines.append("  - none")
    return "\n".join(lines) + "\n"


def write_reports(
    *,
    log_path: Path,
    json_path: Path | None,
    text_path: Path | None,
    github_summary_path: Path | None = None,
) -> list[LeanWarning]:
    """Parse log_path and write the requested report files."""
    if not log_path.exists():
        log_path.touch()
    warnings = parse_warnings(log_path.read_text(encoding="utf-8", errors="replace"))
    if json_path is not None:
        json_path.write_text(json.dumps(report_dict(warnings), indent=2) + "\n", encoding="utf-8")
    text_report = render_text_report(warnings)
    if text_path is not None:
        text_path.write_text(text_report, encoding="utf-8")
    if github_summary_path is not None:
        counts = Counter(warning.category for warning in warnings)
        with github_summary_path.open("a", encoding="utf-8") as summary:
            summary.write("## Lean linter-warning sweep\n\n")
            summary.write(
                "This workflow captures Lean compiler warnings from "
                "`lake exe cache get && lake build -q --log-level=info` "
                "and uploads the report for maintainer triage.\n\n"
            )
            summary.write(f"- Warnings found: {len(warnings)}\n")
            if counts:
                summary.write(
                    "- Categories: "
                    + ", ".join(
                        f"{category}={count}" for category, count in sorted(counts.items())
                    )
                    + "\n"
                )
            if warnings:
                preview = text_report.splitlines()[:120]
                summary.write("\n```text\n")
                summary.write("\n".join(preview))
                if len(text_report.splitlines()) > len(preview):
                    summary.write("\n... truncated; see artifact for full report")
                summary.write("\n```\n")
    return warnings


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, required=True, help="Lean build log to parse")
    parser.add_argument("--json", type=Path, help="path for JSON report")
    parser.add_argument("--text", type=Path, help="path for text report")
    parser.add_argument("--github-summary", type=Path, help="GITHUB_STEP_SUMMARY to append")
    parser.add_argument("--count-output", type=Path, help="GITHUB_OUTPUT to append counts to")
    args = parser.parse_args(argv)

    warnings = write_reports(
        log_path=args.log,
        json_path=args.json,
        text_path=args.text,
        github_summary_path=args.github_summary,
    )
    if args.count_output is not None:
        with args.count_output.open("a", encoding="utf-8") as output:
            print(f"warning_count={len(warnings)}", file=output)
            print(f"actionable_warnings={'true' if warnings else 'false'}", file=output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
