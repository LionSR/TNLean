#!/usr/bin/env python3
r"""Report the blueprint boundary for the planned QICLean extraction.

The report combines the import-closed mover set from
``check_import_direction.py`` with the declaration index from
``blueprint_lean_sync.py``.  It classifies every theorem-like blueprint item
with a ``\lean{...}`` tag and inventories ``\uses`` edges that cross the
future package boundary.  Report mode is read-only and deterministic.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import subprocess

from blueprint_lean_sync import collect_blueprint_entries, collect_lean_decls
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
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.DOTALL)


def blueprint_content_files(blueprint_src: Path) -> list[Path]:
    """Return theorem-bearing blueprint files in stable order."""
    files = list((blueprint_src / "chapter").glob("*.tex"))
    files.extend((blueprint_src / "appendix").rglob("*.tex"))
    return sorted(files)


def environment_uses(blueprint_src: Path) -> list[dict[str, object]]:
    """Return labelled theorem-like items and their ``\\uses`` targets."""
    records: list[dict[str, object]] = []
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
                stack[-1]["lines"].append(line)
            end = ENV_END_RE.search(line)
            if end is None or not stack:
                continue
            record = stack.pop()
            body = "\n".join(record.pop("lines"))
            labels = LABEL_RE.findall(body)
            if not labels:
                continue
            uses: list[str] = []
            for payload in USES_RE.findall(body):
                payload = re.sub(r"%[^\n]*\n\s*", "", payload)
                uses.extend(item.strip() for item in payload.split(",") if item.strip())
            record["label"] = labels[0]
            record["uses"] = sorted(set(uses))
            records.append(record)
    return sorted(records, key=lambda item: (item["file"], item["line"], item["label"]))


def source_sha(root: Path) -> str:
    """Return the exact source commit for the report."""
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def boundary_report(root: Path) -> dict[str, object]:
    """Build a deterministic label and ``\\uses`` boundary report."""
    entries, manifest_errors = manifest_entries(root)
    if manifest_errors:
        raise ValueError("; ".join(manifest_errors))
    movers = {path.as_posix() for path in mover_files(root, entries)}
    lean_decls = collect_lean_decls(root / "TNLean")

    parsed_environments = environment_uses(root / "blueprint" / "src")
    label_by_location = {
        (str(item["file"]), int(item["line"]), str(item["environment"])): str(item["label"])
        for item in parsed_environments
    }
    grouped: dict[tuple[str, int, str | None, str], list[str]] = defaultdict(list)
    for entry in collect_blueprint_entries(root / "blueprint" / "src"):
        label = entry.label or label_by_location.get((entry.file, entry.line, entry.env_type))
        grouped[(entry.file, entry.line, label, entry.env_type)].append(entry.lean_decl)

    items: list[dict[str, object]] = []
    disposition_by_label: dict[str, str] = {}
    for (file, line, label, env_type), declarations in sorted(grouped.items()):
        sources: list[str] = []
        unresolved: list[str] = []
        moving: list[bool] = []
        for name in sorted(set(declarations)):
            declaration = lean_decls.get(name)
            if declaration is None:
                unresolved.append(name)
                continue
            sources.append(declaration.file)
            moving.append(declaration.file in movers)
        if unresolved:
            disposition = "unresolved"
        elif moving and all(moving):
            disposition = "qic"
        elif moving and any(moving):
            disposition = "mixed"
        else:
            disposition = "tn"
        item = {
            "file": file,
            "line": line,
            "label": label,
            "environment": env_type,
            "declarations": sorted(set(declarations)),
            "declaration_sources": sorted(set(sources)),
            "unresolved_declarations": unresolved,
            "disposition": disposition,
        }
        items.append(item)
        if label is not None:
            previous = disposition_by_label.get(label)
            if previous is None:
                disposition_by_label[label] = disposition
            elif previous != disposition:
                disposition_by_label[label] = "mixed"

    edges: list[dict[str, object]] = []
    for record in parsed_environments:
        source_label = str(record["label"])
        source_disposition = disposition_by_label.get(source_label, "unclassified")
        for target_label in record["uses"]:
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
                    "file": record["file"],
                    "line": record["line"],
                }
            )
    edges.sort(key=lambda item: (item["source"], item["target"], item["file"], item["line"]))

    item_counts = Counter(item["disposition"] for item in items)
    edge_counts = Counter(edge["direction"] for edge in edges)
    return {
        "schema_version": 1,
        "source_sha": source_sha(root),
        "mover_path_count": len(movers),
        "item_counts": dict(sorted(item_counts.items())),
        "edge_counts": dict(sorted(edge_counts.items())),
        "items": items,
        "uses_edges": edges,
        "qic_to_tn_uses_edges": [edge for edge in edges if edge["direction"] == "qic_to_tn"],
        "tn_to_qic_interface_edges": [
            edge for edge in edges if edge["direction"] == "tn_to_qic"
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="TNLean repository root")
    args = parser.parse_args()
    try:
        report = boundary_report(args.root.resolve())
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"::error title=QIC blueprint boundary report failed::{error}")
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
