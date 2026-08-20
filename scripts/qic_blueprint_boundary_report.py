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
PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
PROOF_END_RE = re.compile(r"\\end\{proof\}")
ENV_TOKEN_RE = re.compile(r"\\(begin|end)\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.DOTALL)
USES_RE = re.compile(r"\\uses\{([^}]*)\}", re.DOTALL)
REFERENCE_RE = re.compile(r"\\(?:ref|eqref)\{([^}]+)\}", re.DOTALL)
INPUT_LINE_RE = re.compile(r"^[ \t]*\\input\{([^}]+)\}[ \t]*$")
LEDGER_COLUMNS = ("item_id", "source", "environment", "disposition", "reason")
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


def _strip_tex_comments(text: str) -> str:
    """Remove TeX comments while preserving escaped percent signs."""
    cleaned: list[str] = []
    for line in text.splitlines():
        cut = len(line)
        for index, character in enumerate(line):
            if character != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        cleaned.append(line[:cut])
    return "\n".join(cleaned)


def _reference_payload(payload: str) -> str:
    """Normalize a possibly continued TeX label payload."""
    return re.sub(r"\s+", "", _strip_tex_comments(payload))


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
    references: tuple[str, ...]

    @property
    def primary_label(self) -> str | None:
        return self.labels[0] if self.labels else None

    @property
    def identifier(self) -> str:
        """Return the label or frozen source-line key that identifies this item."""
        return self.primary_label or f"@{self.file}:{self.line}"


@dataclass(frozen=True)
class NonItemBlock:
    """One maximal paragraph-like block outside every theorem-like item span."""

    file: str
    line: int
    end_line: int
    labels: tuple[str, ...]
    references: tuple[str, ...]
    input_payload: str | None = None

    @property
    def identifier(self) -> str:
        return f"@{self.file}:{self.line}-{self.end_line}"


def blueprint_environments(blueprint_src: Path) -> list[BlueprintEnvironment]:
    """Parse theorem-like items, including an attached proof and intervening lines."""
    records: list[BlueprintEnvironment] = []
    for path in blueprint_content_files(blueprint_src):
        rel = path.relative_to(blueprint_src.parent).as_posix()
        source_lines = path.read_text(errors="replace").splitlines()
        stack: list[dict[str, object]] = []
        statements: list[dict[str, object]] = []
        for line_no, line in enumerate(source_lines, start=1):
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
            statement = stack.pop()
            statement["end_line"] = line_no
            statements.append(statement)

        statements.sort(key=lambda item: int(item["line"]))
        for index, statement in enumerate(statements):
            start_line = int(statement["line"])
            statement_end_line = int(statement["end_line"])
            next_statement_line = (
                int(statements[index + 1]["line"])
                if index + 1 < len(statements)
                else len(source_lines) + 1
            )
            item_end_line = statement_end_line
            proof_depth = 0
            proof_started = False
            for line_no in range(statement_end_line + 1, next_statement_line):
                line = source_lines[line_no - 1]
                begins = len(PROOF_BEGIN_RE.findall(line))
                ends = len(PROOF_END_RE.findall(line))
                if not proof_started:
                    if begins == 0:
                        continue
                    proof_started = True
                proof_depth += begins - ends
                if proof_depth == 0:
                    item_end_line = line_no
                    break
            if proof_started and proof_depth != 0:
                raise ValueError(
                    f"unterminated proof after {rel}:{statement_end_line}"
                )

            raw_statement_body = "\n".join(
                source_lines[start_line - 1 : statement_end_line]
            )
            raw_body = "\n".join(source_lines[start_line - 1 : item_end_line])
            body = _strip_tex_comments(raw_body)
            labels = tuple(LABEL_RE.findall(body))
            declarations: list[str] = []
            for payload in LEAN_RE.findall(raw_statement_body):
                declarations.extend(_split_comma_payload(payload))
            uses: list[str] = []
            for payload in USES_RE.findall(raw_body):
                uses.extend(_split_comma_payload(payload))
            references = tuple(
                sorted(
                    {
                        normalized
                        for payload in REFERENCE_RE.findall(body)
                        if (normalized := _reference_payload(payload))
                    }
                )
            )
            records.append(
                BlueprintEnvironment(
                    environment=str(statement["environment"]),
                    file=str(statement["file"]),
                    line=start_line,
                    end_line=item_end_line,
                    labels=labels,
                    declarations=tuple(sorted(set(declarations))),
                    uses=tuple(sorted(set(uses))),
                    references=references,
                )
            )
    return sorted(records, key=lambda item: (item.file, item.line, item.primary_label or ""))


def _atomic_non_item_environment_ranges(
    source_lines: list[str], covered: set[int], relative_root: str
) -> dict[int, int]:
    """Return maximal balanced TeX environments that contain no item line."""
    stack: list[tuple[str, int]] = []
    ranges: list[tuple[int, int]] = []
    for line_no, line in enumerate(source_lines, start=1):
        cleaned_line = _strip_tex_comments(line)
        for token in ENV_TOKEN_RE.finditer(cleaned_line):
            action, environment = token.groups()
            if action == "begin":
                stack.append((environment, line_no))
                continue
            if not stack:
                raise ValueError(
                    f"unmatched \\end{{{environment}}} at {relative_root}:{line_no}"
                )
            opened, opened_line = stack.pop()
            if opened != environment:
                raise ValueError(
                    f"mismatched environment at {relative_root}:{line_no}: "
                    f"opened {opened} at line {opened_line}, closed {environment}"
                )
            ranges.append((opened_line, line_no))
    if stack:
        environment, opened_line = stack[-1]
        raise ValueError(
            f"unterminated environment {environment} opened at "
            f"{relative_root}:{opened_line}"
        )

    candidates = [
        (start, end)
        for start, end in ranges
        if not any(line in covered for line in range(start, end + 1))
    ]
    maximal: list[tuple[int, int]] = []
    for start, end in sorted(candidates, key=lambda span: (span[0], -span[1])):
        contained = any(
            parent_start <= start and end <= parent_end
            for parent_start, parent_end in maximal
        )
        if contained:
            continue
        maximal.append((start, end))
    return dict(maximal)


def blueprint_non_item_blocks(
    blueprint_src: Path, environments: list[BlueprintEnvironment]
) -> list[NonItemBlock]:
    """Partition text outside item spans into paragraph-like blocks.

    Complete balanced TeX environments containing no item line are atomic,
    including nested environments and blank or comment-only lines. Elsewhere,
    blank lines and item boundaries split blocks. Router ``\\input`` commands
    are single-line blocks so each simulated output can prune them without
    pulling in every sibling chapter.
    """
    spans_by_file: dict[str, list[tuple[int, int]]] = {}
    for item in environments:
        spans_by_file.setdefault(item.file, []).append((item.line, item.end_line))

    records: list[NonItemBlock] = []
    for path in sorted(blueprint_src.rglob("*.tex")):
        relative_root = path.relative_to(blueprint_src.parent).as_posix()
        if Path("blueprint") / relative_root in BLUEPRINT_EXCLUDED_SUPPORT:
            continue
        source_lines = path.read_text(errors="replace").splitlines()
        relative_parts = path.relative_to(blueprint_src).parts
        is_content_file = "chapter" in relative_parts or "appendix" in relative_parts
        covered: set[int] = set()
        for start, end in spans_by_file.get(relative_root, []):
            covered.update(range(start, end + 1))

        current: list[tuple[int, str]] = []
        atomic_ranges = (
            _atomic_non_item_environment_ranges(source_lines, covered, relative_root)
            if is_content_file
            else {}
        )

        def flush() -> None:
            nonlocal current
            if not current:
                return
            start_line = current[0][0]
            end_line = current[-1][0]
            body = _strip_tex_comments("\n".join(line for _, line in current))
            labels = tuple(LABEL_RE.findall(body))
            references = tuple(
                sorted(
                    {
                        normalized
                        for payload in REFERENCE_RE.findall(body)
                        if (normalized := _reference_payload(payload))
                    }
                )
            )
            records.append(
                NonItemBlock(
                    file=relative_root,
                    line=start_line,
                    end_line=end_line,
                    labels=labels,
                    references=references,
                )
            )
            current = []

        line_no = 1
        while line_no <= len(source_lines):
            line = source_lines[line_no - 1]
            if line_no in covered:
                flush()
                line_no += 1
                continue
            atomic_end = atomic_ranges.get(line_no)
            if atomic_end is not None:
                flush()
                current = [
                    (atomic_line, source_lines[atomic_line - 1])
                    for atomic_line in range(line_no, atomic_end + 1)
                ]
                flush()
                line_no = atomic_end + 1
                continue
            cleaned_line = _strip_tex_comments(line)
            input_match = INPUT_LINE_RE.fullmatch(cleaned_line)
            if input_match is not None:
                flush()
                records.append(
                    NonItemBlock(
                        file=relative_root,
                        line=line_no,
                        end_line=line_no,
                        labels=(),
                        references=(),
                        input_payload=input_match.group(1),
                    )
                )
                line_no += 1
                continue
            if not is_content_file:
                flush()
                line_no += 1
                continue
            if not cleaned_line.strip():
                flush()
                line_no += 1
                continue
            current.append((line_no, line))
            line_no += 1
        flush()
    return sorted(records, key=lambda item: (item.file, item.line, item.end_line))


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
    r"""Read the explicit disposition of every item without ``\lean``."""
    try:
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            if tuple(reader.fieldnames or ()) != LEDGER_COLUMNS:
                raise ValueError(f"{path}: expected columns {','.join(LEDGER_COLUMNS)}")
            rows: dict[str, dict[str, str]] = {}
            for line_no, raw in enumerate(reader, start=2):
                row = {key: (raw.get(key) or "").strip() for key in LEDGER_COLUMNS}
                item_id = row["item_id"]
                if not item_id:
                    raise ValueError(f"{path}:{line_no}: empty item_id")
                if item_id in rows:
                    raise ValueError(f"{path}:{line_no}: duplicate item_id {item_id}")
                if row["disposition"] not in {"qic", "tn"}:
                    raise ValueError(f"{path}:{line_no}: disposition must be qic or tn")
                if row["environment"] not in ENVIRONMENTS:
                    raise ValueError(
                        f"{path}:{line_no}: unknown environment {row['environment']}"
                    )
                if not row["source"] or not row["reason"]:
                    raise ValueError(f"{path}:{line_no}: source and reason must be nonempty")
                row["source"] = normalized_relative_path(row["source"])
                rows[item_id] = row
    except OSError as error:
        raise ValueError(f"cannot read disposition ledger {path}: {error}") from error
    return rows


def _validate_unique_labels(
    environments: list[BlueprintEnvironment], blocks: list[NonItemBlock]
) -> dict[str, BlueprintEnvironment | NonItemBlock]:
    owners: dict[str, BlueprintEnvironment | NonItemBlock] = {}
    for item in [*environments, *blocks]:
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
    used_manual_item_ids: set[str] = set()
    for environment in environments:
        sources: list[str] = []
        unresolved: list[str] = []
        moving: list[bool] = []
        identifier = environment.identifier
        if environment.declarations:
            if identifier in ledger:
                raise ValueError(
                    f"{identifier}: tagged item must not have a manual disposition"
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
        else:
            row = ledger.get(identifier)
            if row is None:
                raise ValueError(
                    f"missing manual disposition for {identifier} "
                    f"at {environment.file}:{environment.line}"
                )
            if row["source"] != environment.file:
                raise ValueError(
                    f"{identifier}: ledger source {row['source']} "
                    f"does not match {environment.file}"
                )
            if row["environment"] != environment.environment:
                raise ValueError(
                    f"{identifier}: ledger environment "
                    f"{row['environment']} does not match {environment.environment}"
                )
            disposition = row["disposition"]
            disposition_source = "manual"
            used_manual_item_ids.add(identifier)

        item = {
            "file": environment.file,
            "line": environment.line,
            "end_line": environment.end_line,
            "label": identifier,
            "labels": list(environment.labels),
            "environment": environment.environment,
            "declarations": list(environment.declarations),
            "declaration_sources": sorted(set(sources)),
            "unresolved_declarations": unresolved,
            "disposition": disposition,
            "disposition_source": disposition_source,
        }
        items.append(item)
        disposition_by_label[identifier] = disposition
        for label in environment.labels:
            disposition_by_label[label] = disposition

    stale = sorted(set(ledger) - used_manual_item_ids)
    if stale:
        raise ValueError("stale manual disposition item_ids: " + ", ".join(stale))
    return items, disposition_by_label


def _blueprint_support_files(root: Path) -> set[str]:
    blueprint_src = root / "blueprint" / "src"
    support = {
        path.relative_to(root / "blueprint").as_posix()
        for path in blueprint_src.rglob("*")
        if path.is_file()
        and "chapter" not in path.relative_to(blueprint_src).parts
        and "appendix" not in path.relative_to(blueprint_src).parts
        and path.relative_to(root) not in BLUEPRINT_EXCLUDED_SUPPORT
    }
    return support


def _input_targets(
    root: Path, blocks: list[NonItemBlock]
) -> dict[str, str]:
    blueprint_src = root / "blueprint" / "src"
    targets: dict[str, str] = {}
    for block in blocks:
        if block.input_payload is None:
            continue
        source = root / "blueprint" / block.file
        resolved = _resolve_input(source, block.input_payload, blueprint_src)
        if resolved is None:
            raise ValueError(
                f"unresolved blueprint input {block.input_payload} at "
                f"{block.file}:{block.line}"
            )
        targets[block.identifier] = resolved.relative_to(root / "blueprint").as_posix()
    return targets


def _add_input_ancestors(
    selected: set[str], blocks: list[NonItemBlock], input_targets: dict[str, str]
) -> None:
    changed = True
    while changed:
        changed = False
        for block in blocks:
            target = input_targets.get(block.identifier)
            if target is None or target not in selected or block.file in selected:
                continue
            selected.add(block.file)
            changed = True


def _simulate_blueprint_split(
    root: Path,
    environments: list[BlueprintEnvironment],
    blocks: list[NonItemBlock],
    items: list[dict[str, object]],
) -> dict[str, object]:
    """Simulate the item split and deterministic treatment of surrounding text.

    Item spans stay only on their classified side. Outside those spans, complete
    paragraph-like blocks are retained on every selected side where all of their
    references resolve. Router input lines are retained exactly when their target
    file is selected. Files defining non-item labels referenced directly by an
    item are selected without closing downward over unrelated router inputs.
    """
    item_by_id = {str(item["label"]): item for item in items}
    item_disposition: dict[str, str] = {}
    for item in items:
        for label in item["labels"]:
            item_disposition[str(label)] = str(item["disposition"])
    block_by_label: dict[str, NonItemBlock] = {
        label: block for block in blocks for label in block.labels
    }
    all_known_labels = set(item_disposition) | set(block_by_label)
    input_targets = _input_targets(root, blocks)
    support = _blueprint_support_files(root)

    selected: dict[str, set[str]] = {
        side: {
            str(item["file"])
            for item in items
            if item["disposition"] == side
        }
        | set(support)
        for side in ("qic", "tn")
    }
    item_files = {str(item["file"]) for item in items}
    files_with_inputs = {
        block.file for block in blocks if block.input_payload is not None
    }
    shared_leaf_prose = {
        input_targets[block.identifier]
        for block in blocks
        if block.file == "src/content.tex"
        and block.input_payload is not None
        and input_targets[block.identifier] not in item_files
        and input_targets[block.identifier] not in files_with_inputs
    }
    for side in ("qic", "tn"):
        selected[side].update(shared_leaf_prose)
    errors: list[str] = []

    for environment in environments:
        source = item_by_id[environment.identifier]
        side = str(source["disposition"])
        for target in environment.references:
            target_block = block_by_label.get(target)
            if target_block is not None:
                selected[side].add(target_block.file)
            elif target not in all_known_labels:
                errors.append(
                    f"{side} item {environment.identifier} has unknown reference {target}"
                )
        for target in environment.uses:
            if target not in all_known_labels:
                errors.append(
                    f"{side} item {environment.identifier} has unknown dependency {target}"
                )
    for block in blocks:
        for target in block.references:
            if target not in all_known_labels:
                errors.append(
                    f"prose {block.identifier} has unknown reference {target}"
                )

    for side in ("qic", "tn"):
        _add_input_ancestors(selected[side], blocks, input_targets)

    retained: dict[str, set[str]] = {
        side: {
            block.identifier
            for block in blocks
            if block.file in selected[side]
            and (
                block.input_payload is None
                or input_targets[block.identifier] in selected[side]
            )
        }
        for side in ("qic", "tn")
    }

    base_interface = {
        target
        for environment in environments
        if item_by_id[environment.identifier]["disposition"] == "tn"
        for target in [*environment.uses, *environment.references]
        if item_disposition.get(target) == "qic"
    }
    interface_labels = set(base_interface)

    changed = True
    while changed:
        changed = False
        interface_labels = set(base_interface)
        for block in blocks:
            if block.identifier not in retained["tn"]:
                continue
            interface_labels.update(
                target
                for target in block.references
                if item_disposition.get(target) == "qic"
            )

        available = {
            "qic": {
                label for label, disposition in item_disposition.items() if disposition == "qic"
            },
            "tn": {
                label for label, disposition in item_disposition.items() if disposition == "tn"
            }
            | interface_labels,
        }
        for side in ("qic", "tn"):
            for block in blocks:
                if block.identifier in retained[side]:
                    available[side].update(block.labels)

        for side in ("qic", "tn"):
            for block in blocks:
                if block.identifier not in retained[side] or block.input_payload is not None:
                    continue
                if any(target not in available[side] for target in block.references):
                    retained[side].remove(block.identifier)
                    changed = True

    interface_labels = set(base_interface)
    for block in blocks:
        if block.identifier in retained["tn"]:
            interface_labels.update(
                target
                for target in block.references
                if item_disposition.get(target) == "qic"
            )

    available = {
        "qic": {
            label for label, disposition in item_disposition.items() if disposition == "qic"
        },
        "tn": {
            label for label, disposition in item_disposition.items() if disposition == "tn"
        }
        | interface_labels,
    }
    for side in ("qic", "tn"):
        for block in blocks:
            if block.identifier in retained[side]:
                available[side].update(block.labels)

    for environment in environments:
        source = item_by_id[environment.identifier]
        side = str(source["disposition"])
        for target in [*environment.uses, *environment.references]:
            if target not in available[side]:
                errors.append(
                    f"{side} item {environment.identifier} cannot resolve {target}"
                )

    for side in ("qic", "tn"):
        for block in blocks:
            if block.identifier not in retained[side]:
                continue
            if block.input_payload is not None:
                target = input_targets[block.identifier]
                if target not in selected[side]:
                    errors.append(
                        f"{side} input {block.file}:{block.line} targets omitted {target}"
                    )
                continue
            for target in block.references:
                if target not in available[side]:
                    errors.append(
                        f"{side} prose {block.identifier} cannot resolve {target}"
                    )

    block_states = Counter()
    block_state_by_id: dict[str, str] = {}
    for block in blocks:
        qic = block.identifier in retained["qic"]
        tn = block.identifier in retained["tn"]
        state = "shared" if qic and tn else "qic" if qic else "tn" if tn else "dropped"
        block_states[state] += 1
        block_state_by_id[block.identifier] = state

    label_availability: dict[str, str] = dict(item_disposition)
    for label, block in block_by_label.items():
        qic = block.identifier in retained["qic"]
        tn = block.identifier in retained["tn"]
        label_availability[label] = (
            "shared" if qic and tn else "qic" if qic else "tn" if tn else "unavailable"
        )

    return {
        "errors": sorted(set(errors)),
        "selected_files": {side: sorted(selected[side]) for side in ("qic", "tn")},
        "retained_blocks": {side: sorted(retained[side]) for side in ("qic", "tn")},
        "block_state_counts": dict(sorted(block_states.items())),
        "block_state_by_id": block_state_by_id,
        "tn_interface_labels": sorted(interface_labels),
        "label_availability": label_availability,
        "input_targets": input_targets,
    }


def _dependency_edges(
    environments: list[BlueprintEnvironment],
    disposition_by_label: dict[str, str],
    attribute: str,
) -> list[dict[str, object]]:
    edges: list[dict[str, object]] = []
    for record in environments:
        source_label = record.identifier
        source_disposition = disposition_by_label.get(source_label, "unclassified")
        for target_label in getattr(record, attribute):
            target_disposition = disposition_by_label.get(target_label, "unclassified")
            if source_disposition == target_disposition or target_disposition == "shared":
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


def _uses_edges(
    environments: list[BlueprintEnvironment],
    disposition_by_label: dict[str, str],
) -> list[dict[str, object]]:
    return _dependency_edges(environments, disposition_by_label, "uses")


def _reference_edges(
    environments: list[BlueprintEnvironment],
    disposition_by_label: dict[str, str],
) -> list[dict[str, object]]:
    return _dependency_edges(environments, disposition_by_label, "references")


def _non_item_reference_edges(
    blocks: list[NonItemBlock], simulation: dict[str, object]
) -> list[dict[str, object]]:
    availability = simulation["label_availability"]
    retained = simulation["retained_blocks"]
    edges: list[dict[str, object]] = []
    for side in ("qic", "tn"):
        for block in blocks:
            if block.identifier not in retained[side]:
                continue
            for target in block.references:
                target_disposition = availability.get(target, "unclassified")
                if target_disposition in {side, "shared"}:
                    direction = "internal"
                elif side == "qic" and target_disposition == "tn":
                    direction = "qic_to_tn"
                elif side == "tn" and target_disposition == "qic":
                    direction = "tn_to_qic"
                else:
                    direction = "unclassified"
                edges.append(
                    {
                        "source": block.identifier,
                        "target": target,
                        "source_disposition": side,
                        "target_disposition": target_disposition,
                        "direction": direction,
                        "file": block.file,
                        "line": block.line,
                    }
                )
    return sorted(
        edges,
        key=lambda item: (
            item["source"],
            item["target"],
            item["source_disposition"],
            item["file"],
            item["line"],
        ),
    )


def _resolve_input(source: Path, payload: str, blueprint_src: Path) -> Path | None:
    candidate = payload if payload.endswith(".tex") else f"{payload}.tex"
    path = blueprint_src / candidate
    if path.is_file():
        return path
    local = source.parent / candidate
    return local if local.is_file() else None


def blueprint_file_manifest(root: Path, selected_files: list[str]) -> list[str]:
    """Return history-filter paths for the simulated QIC blueprint output."""
    selected = {root / "blueprint" / path for path in selected_files}
    selected.update(root / path for path in BLUEPRINT_ROOT_SUPPORT if (root / path).is_file())
    return sorted(path.relative_to(root).as_posix() for path in selected)


def tn_interface_labels(*edge_sets: list[dict[str, object]]) -> list[str]:
    """Return QIC labels used or referenced by staying TN blueprint items."""
    return sorted(
        {
            str(edge["target"])
            for edges in edge_sets
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
    non_item_blocks = blueprint_non_item_blocks(root / "blueprint" / "src", environments)
    _validate_unique_labels(environments, non_item_blocks)
    ledger_file = ledger_path or root / DEFAULT_LEDGER
    ledger = read_disposition_ledger(ledger_file)
    items, disposition_by_label = _classify_environments(root, environments, ledger)
    simulation = _simulate_blueprint_split(root, environments, non_item_blocks, items)
    disposition_by_label.update(simulation["label_availability"])
    edges = _uses_edges(environments, disposition_by_label)
    reference_edges = _reference_edges(environments, disposition_by_label)
    non_item_reference_edges = _non_item_reference_edges(non_item_blocks, simulation)

    item_counts = Counter(str(item["disposition"]) for item in items)
    edge_counts = Counter(str(edge["direction"]) for edge in edges)
    reference_edge_counts = Counter(str(edge["direction"]) for edge in reference_edges)
    non_item_reference_edge_counts = Counter(
        str(edge["direction"]) for edge in non_item_reference_edges
    )
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
    interface_labels = list(simulation["tn_interface_labels"])
    blueprint_files = blueprint_file_manifest(
        root, list(simulation["selected_files"]["qic"])
    )
    try:
        ledger_display = ledger_file.relative_to(root).as_posix()
    except ValueError:
        ledger_display = ledger_file.as_posix()
    return {
        "schema_version": 4,
        "source_sha": source_sha(root),
        "disposition_ledger": ledger_display,
        "mover_path_count": len(movers),
        "environment_count": len(environments),
        "labelled_environment_count": sum(bool(item.labels) for item in environments),
        "unlabelled_environment_count": sum(not item.labels for item in environments),
        "non_item_block_count": len(non_item_blocks),
        "non_item_label_count": sum(len(block.labels) for block in non_item_blocks),
        "non_item_reference_count": sum(len(block.references) for block in non_item_blocks),
        "non_item_block_state_counts": simulation["block_state_counts"],
        "non_item_blocks": [
            {
                "file": block.file,
                "line": block.line,
                "end_line": block.end_line,
                "labels": list(block.labels),
                "references": list(block.references),
                "input_target": simulation["input_targets"].get(block.identifier),
                "disposition": simulation["block_state_by_id"][block.identifier],
            }
            for block in non_item_blocks
        ],
        "simulated_output_errors": simulation["errors"],
        "manual_disposition_count": len(ledger),
        "item_counts": dict(sorted(item_counts.items())),
        "edge_counts": dict(sorted(edge_counts.items())),
        "reference_edge_counts": dict(sorted(reference_edge_counts.items())),
        "non_item_reference_edge_counts": dict(
            sorted(non_item_reference_edge_counts.items())
        ),
        "mixed_physical_file_count": len(mixed_files),
        "mixed_physical_files": mixed_files,
        "simulated_qic_source_file_count": len(simulation["selected_files"]["qic"]),
        "simulated_qic_source_files": simulation["selected_files"]["qic"],
        "simulated_tn_source_file_count": len(simulation["selected_files"]["tn"]),
        "simulated_tn_source_files": simulation["selected_files"]["tn"],
        "blueprint_file_count": len(blueprint_files),
        "tn_interface_label_count": len(interface_labels),
        "items": items,
        "uses_edges": edges,
        "reference_edges": reference_edges,
        "non_item_reference_edges": non_item_reference_edges,
        "qic_to_tn_uses_edges": [edge for edge in edges if edge["direction"] == "qic_to_tn"],
        "qic_to_tn_reference_edges": [
            edge
            for edge in [*reference_edges, *non_item_reference_edges]
            if edge["direction"] == "qic_to_tn"
        ],
        "tn_to_qic_interface_edges": [
            edge
            for edge in [*edges, *reference_edges, *non_item_reference_edges]
            if edge["direction"] == "tn_to_qic"
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
        if report["qic_to_tn_uses_edges"] or report["qic_to_tn_reference_edges"]:
            raise ValueError("QIC-to-TN blueprint dependencies remain")
        if (
            report["edge_counts"].get("unclassified", 0)
            or report["reference_edge_counts"].get("unclassified", 0)
            or report["non_item_reference_edge_counts"].get("unclassified", 0)
        ):
            raise ValueError("unclassified blueprint dependencies remain")
        if report["simulated_output_errors"]:
            raise ValueError("; ".join(report["simulated_output_errors"]))
    except (csv.Error, OSError, subprocess.CalledProcessError, ValueError) as error:
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
