#!/usr/bin/env python3
r"""Report the blueprint boundary for the planned QICLean extraction.

The report combines the import-closed mover set from
``check_import_direction.py`` with the declaration index from
``blueprint_lean_sync.py``. It classifies every theorem-like blueprint item,
using Lean declaration locations when ``\lean{...}`` is present and an explicit
ledger otherwise. It also inventories ``\uses`` edges across the future package
boundary and emits the deterministic blueprint freeze manifests.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess

from blueprint_lean_sync import collect_lean_decls
from check_import_direction import manifest_entries, mover_files


ENVIRONMENTS = (
    "definition",
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "remark",
    "example",
)
ENV_BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}")
ENV_END_RE = re.compile(r"\\end\{(" + "|".join(ENVIRONMENTS) + r")\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.DOTALL)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.DOTALL)
INPUT_RE = re.compile(r"(?m)^[ \t]*\\input\{([^}]+)\}")
LEDGER_COLUMNS = ("label", "source", "environment", "disposition", "reason")
DEFAULT_LEDGER = Path("scripts/qic_blueprint_label_dispositions.csv")
BLUEPRINT_ROOT_SUPPORT = (
    Path("blueprint/.chktexrc"),
    Path("blueprint/README.md"),
    Path("blueprint/latexindent.yaml"),
    Path("blueprint/library.bib"),
)
BLUEPRINT_EXCLUDED_SUPPORT = {
    Path("blueprint/src/content_ft_mps.tex"),
    Path("blueprint/src/print.pdf"),
    Path("blueprint/src/print_ft_mps.tex"),
}


def normalized_relative_path(path: str) -> str:
    """Return a repository-relative path with platform-independent separators."""
    return path.replace("\\", "/")


def _split_comma_payload(payload: str) -> list[str]:
    payload = re.sub(r"%[^\n]*\n\s*", "", payload)
    payload = re.sub(r"%[^\n]*$", "", payload)
    normalized = re.sub(r"\s+", " ", payload)
    return [item.strip() for item in normalized.split(",") if item.strip()]


def blueprint_content_files(blueprint_src: Path) -> list[Path]:
    """Return theorem-bearing blueprint files in stable order."""
    files = list((blueprint_src / "chapter").glob("*.tex"))
    files.extend((blueprint_src / "appendix").rglob("*.tex"))
    return sorted(files)


@dataclass(frozen=True)
class BlueprintEnvironment:
    """One theorem-like blueprint environment."""

    environment: str
    file: str
    line: int
    end_line: int
    labels: tuple[str, ...]
    declarations: tuple[str, ...]
    uses: tuple[str, ...]

    @property
    def primary_label(self) -> str | None:
        return self.labels[0] if self.labels else None


def blueprint_environments(blueprint_src: Path) -> list[BlueprintEnvironment]:
    """Parse theorem-like environments, including every label on each item."""
    records: list[BlueprintEnvironment] = []
    for path in blueprint_content_files(blueprint_src):
        rel = path.relative_to(blueprint_src.parent).as_posix()
        stack: list[dict[str, object]] = []
        for line_no, line in enumerate(path.read_text(errors="replace").splitlines(), start=1):
            begin = ENV_BEGIN_RE.search(line)
            if begin is not None:
                stack.append(
                    {
                        "environment": begin.group(1),
                        "file": rel,
                        "line": line_no,
                        "lines": [line],
                    }
                )
                continue
            if stack:
                lines = stack[-1]["lines"]
                assert isinstance(lines, list)
                lines.append(line)
            end = ENV_END_RE.search(line)
            if end is None or not stack:
                continue
            record = stack.pop()
            record_lines = record["lines"]
            assert isinstance(record_lines, list)
            body = "\n".join(record_lines)
            labels = tuple(LABEL_RE.findall(body))
            declarations: list[str] = []
            for payload in LEAN_RE.findall(body):
                declarations.extend(_split_comma_payload(payload))
            uses: list[str] = []
            for payload in USES_RE.findall(body):
                uses.extend(_split_comma_payload(payload))
            records.append(
                BlueprintEnvironment(
                    environment=str(record["environment"]),
                    file=str(record["file"]),
                    line=int(record["line"]),
                    end_line=line_no,
                    labels=labels,
                    declarations=tuple(sorted(set(declarations))),
                    uses=tuple(sorted(set(uses))),
                )
            )
    return sorted(records, key=lambda item: (item.file, item.line, item.primary_label or ""))


def environment_uses(blueprint_src: Path) -> list[dict[str, object]]:
    r"""Return labelled theorem-like items and their ``\uses`` targets."""
    return [
        {
            "environment": item.environment,
            "file": item.file,
            "line": item.line,
            "label": item.primary_label,
            "labels": list(item.labels),
            "uses": list(item.uses),
        }
        for item in blueprint_environments(blueprint_src)
        if item.primary_label is not None
    ]


def source_sha(root: Path) -> str:
    """Return the exact source commit for the report."""
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def read_disposition_ledger(path: Path) -> dict[str, dict[str, str]]:
    r"""Read the explicit disposition of every labelled item without ``\lean``."""
    try:
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            if tuple(reader.fieldnames or ()) != LEDGER_COLUMNS:
                raise ValueError(f"{path}: expected columns {','.join(LEDGER_COLUMNS)}")
            rows: dict[str, dict[str, str]] = {}
            for line_no, raw in enumerate(reader, start=2):
                row = {key: (raw.get(key) or "").strip() for key in LEDGER_COLUMNS}
                label = row["label"]
                if not label:
                    raise ValueError(f"{path}:{line_no}: empty label")
                if label in rows:
                    raise ValueError(f"{path}:{line_no}: duplicate label {label}")
                if row["disposition"] not in {"qic", "tn"}:
                    raise ValueError(f"{path}:{line_no}: disposition must be qic or tn")
                if row["environment"] not in ENVIRONMENTS:
                    raise ValueError(
                        f"{path}:{line_no}: unknown environment {row['environment']}"
                    )
                if not row["source"] or not row["reason"]:
                    raise ValueError(f"{path}:{line_no}: source and reason must be nonempty")
                row["source"] = normalized_relative_path(row["source"])
                rows[label] = row
    except OSError as error:
        raise ValueError(f"cannot read disposition ledger {path}: {error}") from error
    return rows


def _validate_unique_labels(
    environments: list[BlueprintEnvironment],
) -> dict[str, BlueprintEnvironment]:
    owners: dict[str, BlueprintEnvironment] = {}
    for item in environments:
        for label in item.labels:
            previous = owners.get(label)
            if previous is not None:
                raise ValueError(
                    f"duplicate blueprint label {label}: "
                    f"{previous.file}:{previous.line} and {item.file}:{item.line}"
                )
            owners[label] = item
    return owners


def _classify_environments(
    root: Path,
    environments: list[BlueprintEnvironment],
    ledger: dict[str, dict[str, str]],
) -> tuple[list[dict[str, object]], dict[str, str]]:
    entries, manifest_errors = manifest_entries(root)
    if manifest_errors:
        raise ValueError("; ".join(manifest_errors))
    movers = {path.as_posix() for path in mover_files(root, entries)}
    lean_decls = collect_lean_decls(root / "TNLean")

    items: list[dict[str, object]] = []
    disposition_by_label: dict[str, str] = {}
    used_manual_labels: set[str] = set()
    for environment in environments:
        sources: list[str] = []
        unresolved: list[str] = []
        moving: list[bool] = []
        if environment.declarations:
            if environment.primary_label in ledger:
                raise ValueError(
                    f"{environment.primary_label}: tagged item must not have a manual disposition"
                )
            for name in environment.declarations:
                declaration = lean_decls.get(name)
                if declaration is None:
                    unresolved.append(name)
                    continue
                declaration_file = normalized_relative_path(declaration.file)
                sources.append(declaration_file)
                moving.append(declaration_file in movers)
            if unresolved:
                disposition = "unresolved"
            elif moving and all(moving):
                disposition = "qic"
            elif moving and any(moving):
                disposition = "mixed"
            else:
                disposition = "tn"
            disposition_source = "lean"
        elif environment.primary_label is not None:
            row = ledger.get(environment.primary_label)
            if row is None:
                raise ValueError(
                    f"missing manual disposition for {environment.primary_label} "
                    f"at {environment.file}:{environment.line}"
                )
            if row["source"] != environment.file:
                raise ValueError(
                    f"{environment.primary_label}: ledger source {row['source']} "
                    f"does not match {environment.file}"
                )
            if row["environment"] != environment.environment:
                raise ValueError(
                    f"{environment.primary_label}: ledger environment "
                    f"{row['environment']} does not match {environment.environment}"
                )
            disposition = row["disposition"]
            disposition_source = "manual"
            used_manual_labels.add(environment.primary_label)
        else:
            continue

        item = {
            "file": environment.file,
            "line": environment.line,
            "end_line": environment.end_line,
            "label": environment.primary_label,
            "labels": list(environment.labels),
            "environment": environment.environment,
            "declarations": list(environment.declarations),
            "declaration_sources": sorted(set(sources)),
            "unresolved_declarations": unresolved,
            "disposition": disposition,
            "disposition_source": disposition_source,
        }
        items.append(item)
        for label in environment.labels:
            disposition_by_label[label] = disposition

    stale = sorted(set(ledger) - used_manual_labels)
    if stale:
        raise ValueError("stale manual disposition labels: " + ", ".join(stale))
    return items, disposition_by_label


def _uses_edges(
    environments: list[BlueprintEnvironment],
    disposition_by_label: dict[str, str],
) -> list[dict[str, object]]:
    edges: list[dict[str, object]] = []
    for record in environments:
        source_label = record.primary_label
        if source_label is None:
            continue
        source_disposition = disposition_by_label.get(source_label, "unclassified")
        for target_label in record.uses:
            target_disposition = disposition_by_label.get(target_label, "unclassified")
            if source_disposition == target_disposition:
                direction = "internal"
            elif source_disposition == "qic" and target_disposition == "tn":
                direction = "qic_to_tn"
            elif source_disposition == "tn" and target_disposition == "qic":
                direction = "tn_to_qic"
            else:
                direction = "unclassified"
            edges.append(
                {
                    "source": source_label,
                    "target": target_label,
                    "source_disposition": source_disposition,
                    "target_disposition": target_disposition,
                    "direction": direction,
                    "file": record.file,
                    "line": record.line,
                }
            )
    return sorted(
        edges,
        key=lambda item: (item["source"], item["target"], item["file"], item["line"]),
    )


def _resolve_input(source: Path, payload: str, blueprint_src: Path) -> Path | None:
    candidate = payload if payload.endswith(".tex") else f"{payload}.tex"
    path = blueprint_src / candidate
    if path.is_file():
        return path
    local = source.parent / candidate
    return local if local.is_file() else None


def blueprint_file_manifest(root: Path, items: list[dict[str, object]]) -> list[str]:
    """Return the history-filter blueprint paths needed by the QIC document."""
    blueprint_src = root / "blueprint" / "src"
    selected = {
        root / str(item["file"]).replace("src/", "blueprint/src/", 1)
        for item in items
        if item["disposition"] == "qic"
    }

    tex_files = sorted(blueprint_src.rglob("*.tex"))
    changed = True
    while changed:
        changed = False
        for source in tex_files:
            if (
                source in selected
                or source.relative_to(root) in BLUEPRINT_EXCLUDED_SUPPORT
            ):
                continue
            targets = {
                resolved
                for payload in INPUT_RE.findall(source.read_text(errors="replace"))
                if (resolved := _resolve_input(source, payload, blueprint_src)) is not None
            }
            if targets & selected:
                selected.add(source)
                changed = True

    support = {
        path
        for path in blueprint_src.rglob("*")
        if path.is_file()
        and "chapter" not in path.relative_to(blueprint_src).parts
        and "appendix" not in path.relative_to(blueprint_src).parts
        and path.relative_to(root) not in BLUEPRINT_EXCLUDED_SUPPORT
    }
    support.update(root / path for path in BLUEPRINT_ROOT_SUPPORT if (root / path).is_file())
    selected.update(support)
    return sorted(path.relative_to(root).as_posix() for path in selected)


def tn_interface_labels(edges: list[dict[str, object]]) -> list[str]:
    """Return the direct QIC labels used by staying TN blueprint items."""
    return sorted(
        {
            str(edge["target"])
            for edge in edges
            if edge["direction"] == "tn_to_qic"
        }
    )


def boundary_report(root: Path, ledger_path: Path | None = None) -> dict[str, object]:
    r"""Build a deterministic label and ``\uses`` boundary report."""
    entries, manifest_errors = manifest_entries(root)
    if manifest_errors:
        raise ValueError("; ".join(manifest_errors))
    movers = mover_files(root, entries)
    environments = blueprint_environments(root / "blueprint" / "src")
    _validate_unique_labels(environments)
    ledger_file = ledger_path or root / DEFAULT_LEDGER
    ledger = read_disposition_ledger(ledger_file)
    items, disposition_by_label = _classify_environments(root, environments, ledger)
    edges = _uses_edges(environments, disposition_by_label)

    item_counts = Counter(str(item["disposition"]) for item in items)
    edge_counts = Counter(str(edge["direction"]) for edge in edges)
    dispositions_by_file: dict[str, set[str]] = {}
    for item in items:
        dispositions_by_file.setdefault(str(item["file"]), set()).add(
            str(item["disposition"])
        )
    mixed_files = sorted(
        file
        for file, dispositions in dispositions_by_file.items()
        if {"qic", "tn"} <= dispositions
    )
    interface_labels = tn_interface_labels(edges)
    blueprint_files = blueprint_file_manifest(root, items)
    try:
        ledger_display = ledger_file.relative_to(root).as_posix()
    except ValueError:
        ledger_display = ledger_file.as_posix()
    return {
        "schema_version": 2,
        "source_sha": source_sha(root),
        "disposition_ledger": ledger_display,
        "mover_path_count": len(movers),
        "labelled_environment_count": sum(bool(item.labels) for item in environments),
        "manual_disposition_count": len(ledger),
        "item_counts": dict(sorted(item_counts.items())),
        "edge_counts": dict(sorted(edge_counts.items())),
        "mixed_physical_file_count": len(mixed_files),
        "mixed_physical_files": mixed_files,
        "blueprint_file_count": len(blueprint_files),
        "tn_interface_label_count": len(interface_labels),
        "items": items,
        "uses_edges": edges,
        "qic_to_tn_uses_edges": [edge for edge in edges if edge["direction"] == "qic_to_tn"],
        "tn_to_qic_interface_edges": [
            edge for edge in edges if edge["direction"] == "tn_to_qic"
        ],
        "blueprint_files": blueprint_files,
        "tn_interface_labels": interface_labels,
    }


def _write_lines(items: list[str]) -> None:
    if items:
        print("\n".join(items))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="TNLean repository root")
    parser.add_argument(
        "--ledger",
        type=Path,
        help="manual disposition CSV, relative to the repository root by default",
    )
    parser.add_argument(
        "--mode",
        choices=("json", "blueprint-files", "tn-interface-labels"),
        default="json",
        help="deterministic output to emit",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    ledger = args.ledger
    if ledger is not None and not ledger.is_absolute():
        ledger = root / ledger
    try:
        report = boundary_report(root, ledger)
        for disposition in ("mixed", "unresolved"):
            if report["item_counts"].get(disposition, 0):
                raise ValueError(f"{disposition} blueprint items remain")
        if report["qic_to_tn_uses_edges"]:
            raise ValueError("QIC-to-TN blueprint dependencies remain")
        if report["edge_counts"].get("unclassified", 0):
            raise ValueError("unclassified blueprint dependencies remain")
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"::error title=QIC blueprint boundary report failed::{error}")
        return 1
    if args.mode == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    elif args.mode == "blueprint-files":
        _write_lines(report["blueprint_files"])
    else:
        _write_lines(report["tn_interface_labels"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
