#!/usr/bin/env python3
"""Verify that the tenkz migration ledger matches the tracked TeX sources."""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from tenkzlib.texcase import strip_comments


DOCUMENT = ROOT / "docs/tenkz/DISPOSITIONS.md"
BLUEPRINT_ROOT = ROOT / "blueprint/src/chapter"
FIXTURE_ROOT = ROOT / "tests/tenkz"
ENVIRONMENT = re.compile(r"\\begin\{(tenkz(?:free|cd|lattice|planes)?)\}")
COMMAND = re.compile(r"\\(tnpic|tntree)\b")
DISPOSITIONS = ("preserve", "codemod", "redraw")


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def occurrences(path: Path) -> list[tuple[int, str]]:
    """Return every public picture construct in a comment-stripped TeX file."""
    source = strip_comments(path.read_text(errors="replace"))
    matches = [
        (match.start(), match.group(1))
        for pattern in (ENVIRONMENT, COMMAND)
        for match in pattern.finditer(source)
    ]
    return [
        (source.count("\n", 0, offset) + 1, name)
        for offset, name in sorted(matches)
    ]


def section(text: str, heading: str, next_heading: str | None = None) -> str:
    try:
        result = text.split(heading, 1)[1]
    except IndexError:
        fail(f"missing document heading: {heading}")
    if next_heading is not None:
        result = result.split(next_heading, 1)[0]
    return result


def parse_counter_table(text: str, heading: str) -> Counter[str]:
    result: Counter[str] = Counter()
    started = False
    for row in section(text, heading).splitlines():
        if started and not row.strip():
            break
        match = re.match(r"\| `?([^|`]+?)`? \| \**([0-9]+)\** \|$", row)
        started |= bool(match)
        label = match.group(1).strip().strip("*") if match else ""
        if match and label.lower() != "total":
            result[label] = int(match.group(2))
    if not result:
        fail(f"could not parse counter table below {heading}")
    return result


def parse_fixture_table(text: str) -> Counter[str]:
    body = section(text, "| Disposition | Fixtures |")
    body = body.split("\n\n", 1)[0]
    files: Counter[str] = Counter()
    for row in body.splitlines():
        match = re.match(r"\| ([a-z]+) \| ([0-9]+) \|$", row)
        if match and match.group(1) in DISPOSITIONS:
            files[match.group(1)] = int(match.group(2))
    if set(files) != set(DISPOSITIONS):
        fail("could not parse standalone fixture reconciliation table")
    return files


def documented_blueprint(
    text: str,
) -> tuple[Counter[tuple[str, int, str]], Counter[str]]:
    body = section(text, "## Blueprint inventory", "### Blueprint reconciliation")
    listed: Counter[tuple[str, int, str]] = Counter()
    dispositions: Counter[str] = Counter()
    for row in body.splitlines():
        cells = [cell.strip() for cell in row.split("|")[1:-1]]
        if len(cells) != 4 or not re.fullmatch(r"`[^`]+\.tex`", cells[0]):
            continue
        filename = cells[0].strip("`")
        for disposition, cell in zip(DISPOSITIONS, cells[1:]):
            for use in re.finditer(r"L([0-9]+(?:, [0-9]+)*) `([^`]+)` →", cell):
                for line in map(int, use.group(1).split(", ")):
                    listed[(filename, line, use.group(2))] += 1
                    dispositions[disposition] += 1
    return listed, dispositions


def documented_fixtures(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for disposition in DISPOSITIONS:
        heading = rf"### {disposition.capitalize()} fixtures \(([0-9]+)\)\n"
        ending = r"(?=\n### |\nThe preserved list)"
        match = re.search(
            heading + r"(.*?)" + ending,
            text,
            flags=re.DOTALL,
        )
        if not match:
            fail(f"missing {disposition} fixture list")
        names = re.findall(r"`([^`]+\.tex)`", match.group(2))
        if len(names) != int(match.group(1)):
            fail(
                f"{disposition} heading says {match.group(1)} fixtures, "
                f"but lists {len(names)}"
            )
        for name in names:
            if name in result:
                fail(f"fixture is listed more than once: {name}")
            result[name] = disposition
    return result


def main() -> int:
    text = DOCUMENT.read_text()

    blueprint_occurrences: Counter[tuple[str, int, str]] = Counter()
    blueprint_raw: Counter[str] = Counter()
    for path in sorted(BLUEPRINT_ROOT.glob("*.tex")):
        for line, name in occurrences(path):
            blueprint_occurrences[(path.name, line, name)] += 1
            blueprint_raw[name] += 1

    listed_blueprint, blueprint_dispositions = documented_blueprint(text)
    if blueprint_occurrences != listed_blueprint:
        fail(
            "blueprint inventory mismatch: "
            f"missing={blueprint_occurrences - listed_blueprint}, "
            f"extra={listed_blueprint - blueprint_occurrences}"
        )
    if blueprint_raw != parse_counter_table(text, "| Raw construct | Occurrences |"):
        fail("blueprint raw-count table does not match the source inventory")
    documented_blueprint_dispositions = parse_counter_table(
        text, "| Disposition | Occurrences |"
    )
    if blueprint_dispositions != documented_blueprint_dispositions:
        fail("blueprint disposition totals do not match the line inventory")

    fixtures = documented_fixtures(text)
    expected_fixtures = {path.name for path in FIXTURE_ROOT.glob("*.tex")}
    if set(fixtures) != expected_fixtures:
        fail(
            "fixture inventory mismatch: "
            f"missing={sorted(expected_fixtures - set(fixtures))}, "
            f"extra={sorted(set(fixtures) - expected_fixtures)}"
        )

    fixture_raw: Counter[str] = Counter()
    fixture_files: Counter[str] = Counter(fixtures.values())
    environment_files = 0
    consumer_files = 0
    for path in sorted(FIXTURE_ROOT.glob("*.tex")):
        uses = occurrences(path)
        names = Counter(name for _, name in uses)
        fixture_raw.update(names)
        environment_files += any(name.startswith("tenkz") for name in names)
        consumer_files += bool(uses)

    documented_files = parse_fixture_table(text)
    if fixture_files != documented_files:
        fail("fixture disposition totals do not match the fixture lists")
    fixture_heading = "### Fixture raw-count reconciliation"
    if fixture_raw != parse_counter_table(text, fixture_heading):
        fail("fixture raw-count table does not match the source inventory")

    census = re.search(
        r"Of the ([0-9]+) top-level fixtures, ([0-9]+) open at least one tenkz\n"
        r"environment, ([0-9]+) are command-only consumers, and ([0-9]+)\n"
        r"contain no picture construct\.",
        text,
    )
    actual_census = (
        len(expected_fixtures),
        environment_files,
        consumer_files - environment_files,
        len(expected_fixtures) - consumer_files,
    )
    if not census or tuple(map(int, census.groups())) != actual_census:
        fail(f"fixture consumer census does not match {actual_census}")

    print(
        f"PASS: {sum(blueprint_raw.values())} blueprint occurrences and "
        f"{len(expected_fixtures)} standalone fixtures reconcile exactly"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
