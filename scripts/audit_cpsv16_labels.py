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

from tenkz_paths import ensure_pythonpath

ensure_pythonpath()
from tenkzlib.texcase import scan_environments, strip_comments

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Papers/1606.00608/MPDO-22-12-17-2.tex"
LEDGER = ROOT / "docs/audits/data/cpsv16-label-dispositions.tsv"
CLASSIFICATION_SNAPSHOT = ROOT / "docs/audits/data/cpsv16-label-classifications.tsv"
CONTAINED_RESULT_ANCHORS = (
    ROOT / "docs/audits/data/cpsv16-contained-result-anchors.tsv"
)
EXPECTED_LEXICAL_OCCURRENCES = 187
EXPECTED_LEXICAL_NAMES = 183
EXPECTED_ACTIVE_OCCURRENCES = 186
EXPECTED_ACTIVE_NAMES = 182
EXPECTED_THEOREM_CONTAINED_OCCURRENCES = 60
EXPECTED_THEOREM_CONTAINED_NAMES = 58
EXPECTED_LEXICAL_CLASSIFICATIONS = {
    "section": 10,
    "definition": 10,
    "equation": 81,
    "figure": 45,
    "example": 3,
    "theorem-like": 34,
}
EXPECTED_ACTIVE_CLASSIFICATIONS = {
    "section": 10,
    "definition": 10,
    "equation": 81,
    "figure": 44,
    "example": 3,
    "theorem-like": 34,
}
EXPECTED_DUPLICATES = {
    "thm1": (350, 1168),
    "II_cor2": (355, 1173),
    "eq:II_auxcor": (358, 1176),
    "eq1:proof.IV.12": (1838, 1882),
}
EXPECTED_DUPLICATE_CONTAINED_OCCURRENCES = frozenset(
    {
        ("eq:II_auxcor", 358),
        ("eq:II_auxcor", 1176),
        ("eq1:proof.IV.12", 1838),
        ("eq1:proof.IV.12", 1882),
    }
)
ALLOWED_ACTIVITY = {"active", "inactive"}
ALLOWED_CLASSES = {
    "section", "definition", "equation", "figure", "example", "theorem-like"
}
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
THEOREM_ENVIRONMENTS = frozenset(
    {"thm", "thm*", "prop", "prop*", "lem", "lem*", "cor", "cor*", "proof"}
)
INHERIT_RE = re.compile(r"\binherit(?:s|ance|ances)?\b", re.IGNORECASE)
STATUS_RE = re.compile(r"\bstatus\b", re.IGNORECASE)
BOUNDARY_RE = re.compile(
    r"\b(boundar(?:y|ies)|correction(?:s)?|orientation|hypothes(?:is|es)|"
    r"restriction|interpretation|assumption(?:s)?)\b",
    re.IGNORECASE,
)


def source_inventory(
    path: Path = SOURCE,
) -> tuple[list[tuple[str, int, int, bool]], str]:
    """Return lexical occurrences with activity and comment-blanked source."""
    source = path.read_text()
    active_source = strip_comments(source)
    inventory: list[tuple[str, int, int, bool]] = []
    for match in LABEL_RE.finditer(source):
        line_no = source.count("\n", 0, match.start()) + 1
        line_start = source.rfind("\n", 0, match.start()) + 1
        active = active_source[match.start() : match.end()] == match.group(0)
        inventory.append((match.group(1), line_no, match.start() - line_start, active))
    return inventory, active_source


def theorem_contained_labels(
    active_source: str, ledger: dict[str, dict[str, str]]
) -> list[tuple[str, int]]:
    """Find equation and figure label occurrences inside theorems or proofs."""
    environments = scan_environments(active_source, THEOREM_ENVIRONMENTS)
    result: list[tuple[str, int]] = []
    for match in LABEL_RE.finditer(active_source):
        label = match.group(1)
        row = ledger.get(label)
        if not row or row["classification"] not in {"equation", "figure"}:
            continue
        if any(
            environment.start <= match.start() < environment.end
            for environment in environments
        ):
            line_no = active_source.count("\n", 0, match.start()) + 1
            result.append((label, line_no))
    return result


def inheritance_count_errors(
    contained_occurrences: list[tuple[str, int]],
) -> list[str]:
    """Return errors when theorem/proof containment inventory totals drift."""
    errors: list[str] = []
    if len(contained_occurrences) != EXPECTED_THEOREM_CONTAINED_OCCURRENCES:
        errors.append(
            "theorem/proof-contained occurrences: expected "
            f"{EXPECTED_THEOREM_CONTAINED_OCCURRENCES}, got {len(contained_occurrences)}"
        )
    contained_names = {label for label, _ in contained_occurrences}
    if len(contained_names) != EXPECTED_THEOREM_CONTAINED_NAMES:
        errors.append(
            "theorem/proof-contained names: expected "
            f"{EXPECTED_THEOREM_CONTAINED_NAMES}, got {len(contained_names)}"
        )
    return errors


def inheritance_errors(
    contained_occurrences: list[tuple[str, int]],
    ledger: dict[str, dict[str, str]],
    expected_result_anchors: dict[
        tuple[str, int], tuple[str, re.Pattern[str], re.Pattern[str]]
    ] | None = None,
) -> list[str]:
    """Validate inheritance dispositions for every contained occurrence."""
    if expected_result_anchors is None:
        expected_result_anchors = read_contained_result_anchors()
    errors: list[str] = []
    actual_occurrences = set(contained_occurrences)
    expected_occurrences = set(expected_result_anchors)
    if actual_occurrences != expected_occurrences:
        missing = sorted(expected_occurrences - actual_occurrences)
        extra = sorted(actual_occurrences - expected_occurrences)
        errors.append(
            "theorem/proof-contained result-anchor snapshot mismatch; "
            f"missing={missing}, extra={extra}"
        )
    occurrence_counts = Counter(label for label, _ in contained_occurrences)
    duplicate_occurrences = {
        occurrence
        for occurrence in contained_occurrences
        if occurrence_counts[occurrence[0]] > 1
    }
    expected_duplicate_occurrences = set(EXPECTED_DUPLICATE_CONTAINED_OCCURRENCES)
    if duplicate_occurrences != expected_duplicate_occurrences:
        errors.append(
            "duplicate theorem/proof-contained occurrence map differs: expected "
            f"{sorted(expected_duplicate_occurrences)!r}, "
            f"got {sorted(duplicate_occurrences)!r}"
        )

    for label, line_no in contained_occurrences:
        disposition = ledger[label]["disposition"]
        if not (
            INHERIT_RE.search(disposition)
            and STATUS_RE.search(disposition)
            and BOUNDARY_RE.search(disposition)
        ):
            errors.append(
                f"{label} at line {line_no}: theorem/proof-contained "
                f"{ledger[label]['classification']} disposition must explicitly "
                "inherit the enclosing result's status and boundary"
            )
        result_anchor = expected_result_anchors.get((label, line_no))
        if result_anchor is not None:
            anchor_name, anchor_pattern, boundary_pattern = result_anchor
            if anchor_pattern.search(disposition) is None:
                errors.append(
                    f"{label} at line {line_no}: disposition must exactly match "
                    f"enclosing result anchor {anchor_name!r}"
                )
            if boundary_pattern.search(disposition) is None:
                errors.append(
                    f"{label} at line {line_no}: disposition must retain its "
                    "occurrence-specific semantic boundary"
                )
    return errors


def read_tsv_rows(
    path: Path,
    expected_fields: list[str],
    table_name: str,
    *,
    require_rows: bool = False,
    key_fields: tuple[str, ...] | None = ("label",),
) -> list[dict[str, str]]:
    """Read a labelled TSV with shared schema and row validation."""
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if reader.fieldnames != expected_fields:
            raise ValueError(f"{table_name} columns must be exactly {expected_fields}")
        rows = list(reader)
    if require_rows and not rows:
        raise ValueError(f"{table_name} must contain at least one row")
    keys: set[tuple[str, ...]] = set()
    for row in rows:
        if None in row:
            raise ValueError(f"{table_name} row has surplus fields: {row[None]!r}")
        if any(value is None for value in row.values()):
            raise ValueError(f"{table_name} row has missing fields: {row!r}")
        label = row["label"]
        if not label:
            raise ValueError(f"empty label in {table_name}")
        if key_fields is not None:
            key = tuple(row[field] for field in key_fields)
            if key in keys:
                if key_fields == ("label",):
                    raise ValueError(f"duplicate {table_name} row for {label}")
                raise ValueError(
                    f"duplicate {table_name} row for "
                    f"{dict(zip(key_fields, key, strict=True))!r}"
                )
            keys.add(key)
    return rows


def read_contained_result_anchors(
    path: Path = CONTAINED_RESULT_ANCHORS,
) -> dict[tuple[str, int], tuple[str, re.Pattern[str], re.Pattern[str]]]:
    """Read exact enclosing-result matchers for every contained occurrence."""
    rows = read_tsv_rows(
        path,
        ["label", "line", "result_anchor", "anchor_regex", "boundary_regex"],
        "contained result-anchor snapshot",
        require_rows=True,
        key_fields=None,
    )
    result: dict[
        tuple[str, int], tuple[str, re.Pattern[str], re.Pattern[str]]
    ] = {}
    for row in rows:
        label = row["label"]
        try:
            line = int(row["line"])
        except ValueError as error:
            raise ValueError(
                f"invalid contained result-anchor line for {label}: {row['line']!r}"
            ) from error
        if line <= 0:
            raise ValueError(
                f"invalid contained result-anchor line for {label}: {line}"
            )
        key = (label, line)
        if key in result:
            raise ValueError(
                "duplicate normalized contained result-anchor row for "
                f"{label} at line {line}"
            )
        anchor = row["result_anchor"].strip()
        if not anchor:
            raise ValueError(
                f"empty contained result anchor for {label} at line {line}"
            )
        anchor_regex = row["anchor_regex"].strip()
        if not anchor_regex:
            raise ValueError(
                f"empty contained result-anchor regex for {label} at line {line}"
            )
        boundary_regex = row["boundary_regex"].strip()
        if not boundary_regex:
            raise ValueError(
                f"empty contained boundary regex for {label} at line {line}"
            )
        try:
            anchor_pattern = re.compile(anchor_regex)
            boundary_pattern = re.compile(boundary_regex, re.IGNORECASE)
        except re.error as error:
            raise ValueError(
                f"invalid contained result-anchor regex for {label} at line {line}: "
                f"{error.pattern!r}"
            ) from error
        result[key] = (anchor, anchor_pattern, boundary_pattern)
    if len(rows) != EXPECTED_THEOREM_CONTAINED_OCCURRENCES:
        raise ValueError(
            "contained result-anchor snapshot must contain exactly "
            f"{EXPECTED_THEOREM_CONTAINED_OCCURRENCES} physical rows, "
            f"got {len(rows)}"
        )
    return result


def read_classification_snapshot(
    path: Path = CLASSIFICATION_SNAPSHOT,
) -> dict[str, str]:
    """Read the exact expected classification of every lexical label."""
    rows = read_tsv_rows(
        path, ["label", "classification"], "classification snapshot"
    )
    result: dict[str, str] = {}
    for row in rows:
        label = row["label"]
        classification = row["classification"]
        if classification not in ALLOWED_CLASSES:
            raise ValueError(
                f"invalid snapshot classification for {label}: {classification}"
            )
        result[label] = classification
    return result


def classification_count_errors(
    ledger: dict[str, dict[str, str]],
    expected_by_label: dict[str, str] | None = None,
) -> list[str]:
    """Return per-label and aggregate classification errors."""
    if expected_by_label is None:
        expected_by_label = read_classification_snapshot()
    actual_by_label = {
        label: row["classification"] for label, row in ledger.items()
    }
    lexical = Counter(actual_by_label.values())
    active = Counter(
        row["classification"]
        for row in ledger.values()
        if row["activity"] == "active"
    )
    errors: list[str] = []
    if set(actual_by_label) != set(expected_by_label):
        missing = sorted(set(expected_by_label) - set(actual_by_label))
        extra = sorted(set(actual_by_label) - set(expected_by_label))
        errors.append(
            "classification snapshot label mismatch; "
            f"missing={missing}, extra={extra}"
        )
    for label in sorted(set(actual_by_label) & set(expected_by_label)):
        if actual_by_label[label] != expected_by_label[label]:
            errors.append(
                f"{label}: classification {actual_by_label[label]!r}, "
                f"expected {expected_by_label[label]!r}"
            )
    if lexical != EXPECTED_LEXICAL_CLASSIFICATIONS:
        errors.append(
            "lexical classification totals: expected "
            f"{EXPECTED_LEXICAL_CLASSIFICATIONS!r}, got {dict(lexical)!r}"
        )
    if active != EXPECTED_ACTIVE_CLASSIFICATIONS:
        errors.append(
            "active classification totals: expected "
            f"{EXPECTED_ACTIVE_CLASSIFICATIONS!r}, got {dict(active)!r}"
        )
    return errors


def read_ledger(path: Path = LEDGER) -> dict[str, dict[str, str]]:
    rows = read_tsv_rows(
        path,
        [
            "label",
            "occurrences",
            "lines",
            "activity",
            "classification",
            "disposition",
        ],
        "ledger",
        require_rows=True,
    )
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        label = row["label"]
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

    inventory, active_source = source_inventory()
    counts = Counter(label for label, _, _, _ in inventory)
    lines: dict[str, list[int]] = defaultdict(list)
    activities: dict[str, list[tuple[int, bool]]] = defaultdict(list)
    for label, line, _, active in inventory:
        lines[label].append(line)
        activities[label].append((line, active))
    line_tuples = {label: tuple(locations) for label, locations in lines.items()}
    ledger = read_ledger()

    errors: list[str] = []
    errors.extend(classification_count_errors(ledger))
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

    contained_occurrences = theorem_contained_labels(active_source, ledger)
    contained = {label for label, _ in contained_occurrences}
    errors.extend(inheritance_count_errors(contained_occurrences))
    errors.extend(inheritance_errors(contained_occurrences, ledger))

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
        "Theorem/proof inheritance: "
        f"{len(contained)} unique equation or figure labels, "
        f"{len(contained_occurrences)} occurrences checked"
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("Every lexical source label has exactly one activity, classification, and disposition.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
