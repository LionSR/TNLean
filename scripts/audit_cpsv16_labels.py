#!/usr/bin/env python3
"""Validate the every-label CPSV16 source audit.

The archived source contains one commented-out label and four repeated label
names. This script counts literal ``\\label{...}`` occurrences, derives active
occurrences by stripping unescaped TeX comments, compares the occurrence-level
activity with the maintained TSV ledger, and checks theorem-contained status
inheritance for equation and figure labels.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Papers/1606.00608/MPDO-22-12-17-2.tex"
LEDGER = ROOT / "docs/audits/data/cpsv16-label-dispositions.tsv"
EXPECTED_LEXICAL_OCCURRENCES = 187
EXPECTED_LEXICAL_NAMES = 183
EXPECTED_ACTIVE_OCCURRENCES = 186
EXPECTED_ACTIVE_NAMES = 182
EXPECTED_DUPLICATES = {
    "thm1": (350, 1168),
    "II_cor2": (355, 1173),
    "eq:II_auxcor": (358, 1176),
    "eq1:proof.IV.12": (1838, 1882),
}
ALLOWED_ACTIVITY = {"active", "inactive"}
ALLOWED_CLASSES = {
    "section", "definition", "equation", "figure", "example", "theorem-like"
}
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
THEOREM_BEGIN_RE = re.compile(r"\\begin\{(thm\*?|prop\*?|lem\*?|cor\*?|proof)\}")
THEOREM_END_RE = re.compile(r"\\end\{(thm\*?|prop\*?|lem\*?|cor\*?|proof)\}")
INHERIT_RE = re.compile(r"\binherit(?:s|ance|ances)?\b", re.IGNORECASE)
STATUS_RE = re.compile(r"\bstatus\b", re.IGNORECASE)
BOUNDARY_RE = re.compile(
    r"\b(boundar(?:y|ies)|correction(?:s)?|orientation|hypothes(?:is|es)|"
    r"restriction|interpretation|assumption(?:s)?)\b",
    re.IGNORECASE,
)


def strip_unescaped_comment(line: str) -> str:
    """Remove the first unescaped TeX comment and everything following it."""
    for index, char in enumerate(line):
        if char != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return line[:index]
    return line


def source_inventory() -> tuple[list[tuple[str, int, int, bool]], list[str]]:
    """Return lexical occurrences with derived activity and uncommented lines."""
    inventory: list[tuple[str, int, int, bool]] = []
    active_lines: list[str] = []
    for line_no, line in enumerate(SOURCE.read_text().splitlines(), 1):
        active_line = strip_unescaped_comment(line)
        active_lines.append(active_line)
        for match in LABEL_RE.finditer(line):
            inventory.append(
                (match.group(1), line_no, match.start(), match.start() < len(active_line))
            )
    return inventory, active_lines


def theorem_contained_labels(
    active_lines: list[str], ledger: dict[str, dict[str, str]]
) -> set[str]:
    """Find equation and figure labels inside theorem statements or proofs."""
    stack: list[str] = []
    result: set[str] = set()
    for line in active_lines:
        begin = THEOREM_BEGIN_RE.search(line)
        if begin:
            stack.append(begin.group(1))
        if stack:
            for label in LABEL_RE.findall(line):
                row = ledger.get(label)
                if row and row["classification"] in {"equation", "figure"}:
                    result.add(label)
        end = THEOREM_END_RE.search(line)
        if end:
            for index in range(len(stack) - 1, -1, -1):
                if stack[index] == end.group(1):
                    stack.pop(index)
                    break
    return result


def read_ledger() -> dict[str, dict[str, str]]:
    with LEDGER.open(newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_fields = [
            "label", "occurrences", "lines", "activity", "classification", "disposition"
        ]
        if reader.fieldnames != expected_fields:
            raise ValueError(f"ledger columns must be exactly {expected_fields}")
        rows = list(reader)
    if not rows:
        raise ValueError("ledger must contain at least one row")
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        label = row["label"]
        if not label:
            raise ValueError("empty label in ledger")
        if label in result:
            raise ValueError(f"duplicate ledger row for {label}")
        if row["activity"] not in ALLOWED_ACTIVITY:
            raise ValueError(f"invalid activity for {label}: {row['activity']}")
        if row["classification"] not in ALLOWED_CLASSES:
            raise ValueError(f"invalid classification for {label}: {row['classification']}")
        if not row["disposition"].strip():
            raise ValueError(f"empty disposition for {label}")
        result[label] = row
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list-duplicates", action="store_true")
    args = parser.parse_args()

    inventory, active_lines = source_inventory()
    counts = Counter(label for label, _, _, _ in inventory)
    lines: dict[str, list[int]] = defaultdict(list)
    activities: dict[str, list[tuple[int, bool]]] = defaultdict(list)
    for label, line, _, active in inventory:
        lines[label].append(line)
        activities[label].append((line, active))
    line_tuples = {label: tuple(locations) for label, locations in lines.items()}
    ledger = read_ledger()

    errors: list[str] = []
    if len(inventory) != EXPECTED_LEXICAL_OCCURRENCES:
        errors.append(
            f"lexical occurrences: expected {EXPECTED_LEXICAL_OCCURRENCES}, got {len(inventory)}"
        )
    if len(counts) != EXPECTED_LEXICAL_NAMES:
        errors.append(f"lexical names: expected {EXPECTED_LEXICAL_NAMES}, got {len(counts)}")
    actual_duplicates = {
        label: locations for label, locations in line_tuples.items() if len(locations) > 1
    }
    if actual_duplicates != EXPECTED_DUPLICATES:
        errors.append(f"duplicate map differs: {actual_duplicates!r}")
    if set(ledger) != set(counts):
        missing = sorted(set(counts) - set(ledger))
        extra = sorted(set(ledger) - set(counts))
        errors.append(f"ledger/source label mismatch; missing={missing}, extra={extra}")

    for label in sorted(set(ledger) & set(counts)):
        row = ledger[label]
        expected_occurrences = str(counts[label])
        expected_lines = ",".join(map(str, line_tuples[label]))
        if row["occurrences"] != expected_occurrences:
            errors.append(
                f"{label}: occurrence field {row['occurrences']!r}, expected {expected_occurrences!r}"
            )
        if row["lines"] != expected_lines:
            errors.append(f"{label}: line field {row['lines']!r}, expected {expected_lines!r}")
        source_activity = {active for _, active in activities[label]}
        if len(source_activity) != 1:
            errors.append(
                f"{label}: source occurrences have mixed activity: {activities[label]!r}"
            )
            continue
        expected_activity = "active" if source_activity.pop() else "inactive"
        if row["activity"] != expected_activity:
            errors.append(
                f"{label}: activity field {row['activity']!r}, expected {expected_activity!r} "
                f"from source occurrences {activities[label]!r}"
            )

    active_inventory = [entry for entry in inventory if entry[3]]
    active_names = {label for label, _, _, _ in active_inventory}
    inactive_names = set(counts) - active_names
    if len(active_inventory) != EXPECTED_ACTIVE_OCCURRENCES:
        errors.append(
            f"active occurrences: expected {EXPECTED_ACTIVE_OCCURRENCES}, got {len(active_inventory)}"
        )
    if len(active_names) != EXPECTED_ACTIVE_NAMES:
        errors.append(f"active names: expected {EXPECTED_ACTIVE_NAMES}, got {len(active_names)}")

    contained = theorem_contained_labels(active_lines, ledger)
    for label in sorted(contained):
        disposition = ledger[label]["disposition"]
        if not (
            INHERIT_RE.search(disposition)
            and STATUS_RE.search(disposition)
            and BOUNDARY_RE.search(disposition)
        ):
            errors.append(
                f"{label}: theorem/proof-contained {ledger[label]['classification']} disposition "
                "must explicitly inherit the enclosing result's status and boundary"
            )

    if args.list_duplicates:
        for label, locations in actual_duplicates.items():
            suffix = "\taccidental" if label == "eq1:proof.IV.12" else ""
            print(f"{label}\t{','.join(map(str, locations))}{suffix}")

    duplicate_occurrences = sum(n - 1 for n in counts.values())
    print(
        f"CPSV16 labels: {len(inventory)} lexical occurrences, {len(counts)} lexical names; "
        f"{len(active_inventory)} active occurrences, {len(active_names)} active names; "
        f"{duplicate_occurrences} duplicate occurrences"
    )
    print(
        f"Disposition ledger: {len(ledger)} lexical names "
        f"({len(active_names)} active, {len(inactive_names)} inactive)"
    )
    print(
        f"Theorem/proof inheritance: {len(contained)} equation or figure labels checked"
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("Every lexical source label has exactly one activity, classification, and disposition.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
