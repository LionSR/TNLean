#!/usr/bin/env python3
"""Classify Claude provider-limit failures in GitHub Actions logs.

The classifier is deliberately narrow.  It reports a provider-limit failure only
for lines that look like API quota, credit, or HTTP 429 failures, so ordinary
Lean, blueprint, or review failures do not disable automation.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PROVIDER_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("deepseek", re.compile(r"\bdeepseek\b", re.IGNORECASE)),
    ("anthropic", re.compile(r"\banthropic\b|\bclaude\b", re.IGNORECASE)),
]

LIMIT_PATTERNS: list[re.Pattern[str]] = [
    re.compile(
        r"\b(?:error|failed|exception|request failed|api error|status code)"
        r"[^\n]{0,80}\b429\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b429\b[^\n]{0,80}\b(?:too many requests|rate[_ -]?limit|quota|credit)",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:anthropic|claude|deepseek|api|provider)\b[^\n]{0,120}"
        r"\b(?:rate[_ -]?limit(?:ed|s)?|too many requests|quota exceeded|"
        r"insufficient[_ -]?quota|credit balance|usage limit|billing hard limit)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:rate[_ -]?limit(?:ed|s)?|too many requests|quota exceeded|"
        r"insufficient[_ -]?quota|credit balance|usage limit|billing hard limit)\b"
        r"[^\n]{0,120}\b(?:anthropic|claude|deepseek|api|provider)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:insufficient[_ -]?quota|quota exceeded|credit balance is too low|"
        r"usage limit exceeded|billing hard limit)\b",
        re.IGNORECASE,
    ),
]


def iter_log_files(paths: list[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            files.extend(p for p in path.rglob("*") if p.is_file())
    return sorted(files)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return ""


def clean_line(line: str) -> str:
    line = re.sub(r"\x1b\[[0-9;]*m", "", line)
    line = "".join(
        ch if ch == "\t" or ch == "\n" or 32 <= ord(ch) <= 126 else " " for ch in line
    )
    line = re.sub(r"\s+", " ", line).strip()
    return line[:500]


def detect_provider(text: str, fallback: str) -> str:
    for provider, pattern in PROVIDER_PATTERNS:
        if pattern.search(text):
            return provider
    return fallback


def classify(paths: list[Path], fallback_provider: str, max_excerpts: int) -> dict[str, object]:
    matches: list[dict[str, str]] = []
    provider_votes: dict[str, int] = {}

    for path in iter_log_files(paths):
        text = read_text(path)
        if not text:
            continue
        for raw_line in text.splitlines():
            line = clean_line(raw_line)
            if not line:
                continue
            if any(pattern.search(line) for pattern in LIMIT_PATTERNS):
                provider = detect_provider(line, fallback_provider)
                if provider == "unknown":
                    continue
                provider_votes[provider] = provider_votes.get(provider, 0) + 1
                if len(matches) < max_excerpts:
                    matches.append({"file": str(path), "provider": provider, "line": line})

    matched = bool(provider_votes)
    provider = fallback_provider
    if provider_votes:
        provider = max(provider_votes.items(), key=lambda item: item[1])[0]

    return {
        "matched": matched,
        "category": "provider-limit" if matched else "none",
        "provider": provider,
        "match_count": sum(provider_votes.values()),
        "excerpts": matches,
    }


def write_github_output(path: Path, result: dict[str, object]) -> None:
    def write_one(name: str, value: str) -> None:
        delimiter = f"__{name}_EOF__"
        with path.open("a", encoding="utf-8") as out:
            out.write(f"{name}<<{delimiter}\n")
            out.write(value)
            out.write(f"\n{delimiter}\n")

    write_one("matched", "true" if result["matched"] else "false")
    write_one("category", str(result["category"]))
    write_one("provider", str(result["provider"]))
    write_one("match_count", str(result["match_count"]))
    write_one("json", json.dumps(result, sort_keys=True))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path, help="Log files or directories to inspect.")
    parser.add_argument("--provider", default="unknown", help="Provider fallback when logs do not name it.")
    parser.add_argument("--max-excerpts", type=int, default=5, help="Maximum evidence lines to report.")
    parser.add_argument("--github-output", type=Path, help="Optional GITHUB_OUTPUT file.")
    args = parser.parse_args()

    result = classify(args.paths, args.provider, args.max_excerpts)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.github_output:
        write_github_output(args.github_output, result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
