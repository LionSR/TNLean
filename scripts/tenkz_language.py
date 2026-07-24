#!/usr/bin/env python3
"""Generate and verify the public tenkz language registry.

The TeX registry is executable by the package and parseable here.  This tool
is the common source for the manual reference, lint aliases, and API census.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "tex/tenkz/tenkz-language-registry.tex"
REFERENCE = ROOT / "docs/tenkz/chapters2/generated-language-reference.tex"
ALIASES = ROOT / "docs/tenkz/chapters2/generated-language-aliases.tex"


@dataclass(frozen=True)
class Entry:
    kind: str
    fields: tuple[str, ...]


ARITIES = {"environment": 4, "command": 5, "key": 6, "alias": 4, "example": 3}

BASELINE = ROOT / "tests/tenkz/census-baseline.json"

# The two-ledger vocabulary of the shrink gate (docs/tenkz/SHRINK.md).
# kernel: the load-bearing surface, hard one-in-one-out budget.
# sugar(<expansion>): expands mechanically into kernel spellings.
# alias(<replacement>; sunset=<milestone>): read-old-documents only.
# escape: sanctioned raw-geometry leak, metered by the escape census.
_LEDGERS = ("kernel", "sugar", "alias", "escape")
MILESTONES = ("0.8", "0.9", "1.0")
_PARSER_FAMILY_SCOPE = {
    "setup": "setup",
    "grid": "picture",
    "lattice": "picture",
    "cd": "picture",
    "cell": "object",
    "put": "object",
    "tree": "object",
    "site": "object",
    "join": "connection",
    "edge": "connection",
    "arrow": "connection",
    "region": "region",
    "free region": "region",
    "span": "annotation",
    "declare atom": "atom-declaration",
    # the 1.0 kernel trees (l3keys); scopes mirror LANGUAGE-1.0.md section 2
    "kernel-picture": "kernel-picture",
    "kernel-atom": "kernel-atom",
    "kernel-wire": "kernel-wire",
    "kernel-mark": "kernel-mark",
    "kernel-setup": "kernel-setup",
    "kernel-declare": "kernel-declare",
    "kernel-declare-atom": "atom-declaration",
}
_SETUP_FORWARDS = {
    "grid": {"pitch", "compact", "inline", "tensor style", "species"},
    "lattice": {"pitch", "compact", "inline", "tensor style", "species"},
    "cd": {"pitch", "compact", "inline", "tensor style", "species"},
    "tree": {"pitch", "compact", "inline"},
}


def parse_status(status: str) -> tuple[str, str]:
    """Return (ledger, payload); raise ValueError on unknown vocabulary."""
    if status in ("kernel", "escape"):
        return status, ""
    for ledger in ("sugar", "alias"):
        if status.startswith(ledger + "(") and status.endswith(")"):
            return ledger, status[len(ledger) + 1 : -1]
    raise ValueError(f"unknown ledger status {status!r}")


def parse_alias_payload(payload: str) -> tuple[str, str]:
    """Return an alias replacement and its supported sunset milestone."""
    match = re.fullmatch(r"(.+?)\s*;\s*sunset=([^;\s]+)", payload)
    if match is None:
        raise ValueError(
            "alias payload must be '<replacement>; sunset=<milestone>'"
        )
    replacement, sunset = match.groups()
    if sunset not in MILESTONES:
        raise ValueError(
            f"unsupported alias sunset {sunset!r}; expected one of "
            + ", ".join(MILESTONES)
        )
    return replacement.strip(), sunset


def parse_value_alias_sunset(meaning: str) -> str:
    """Return the milestone carried by a value-alias description."""
    match = re.search(r"(?:^|\s)Sunset\s+([^.\s]+(?:\.[^.\s]+)?)\.\s*$", meaning)
    if match is None:
        raise ValueError("value alias description carries no final 'Sunset M.'")
    sunset = match.group(1)
    if sunset not in MILESTONES:
        raise ValueError(
            f"unsupported value-alias sunset {sunset!r}; expected one of "
            + ", ".join(MILESTONES)
        )
    return sunset


def ledger_split(entries: list[Entry]) -> dict[str, list[tuple[str, ...]]]:
    split: dict[str, list[tuple[str, ...]]] = {ledger: [] for ledger in _LEDGERS}
    for entry in entries:
        if entry.kind != "key":
            continue
        ledger, _payload = parse_status(entry.fields[4])
        split[ledger].append(entry.fields)
    return split


def public_census(entries: list[Entry]) -> dict[str, int]:
    """Registry surface counted by M1, including commands and environments."""
    split = ledger_split(entries)
    return {
        **{ledger: len(split[ledger]) for ledger in _LEDGERS},
        "commands": sum(entry.kind == "command" for entry in entries),
        "environments": sum(entry.kind == "environment" for entry in entries),
    }


def _split_top_level_commas(text: str) -> list[str]:
    """Split a registry expression without cutting commas inside braces."""
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char in "{[(":
            depth += 1
        elif char in "}])":
            depth -= 1
            if depth < 0:
                raise ValueError(f"unbalanced registry expression {text!r}")
        elif char == "," and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
        index += 1
    if depth:
        raise ValueError(f"unbalanced registry expression {text!r}")
    parts.append(text[start:].strip())
    return parts


def parse_key_expression(expression: str) -> list[tuple[str, str | None]]:
    """Parse a complete comma-separated key or key=value expression."""
    parsed: list[tuple[str, str | None]] = []
    for fragment in _split_top_level_commas(expression):
        match = re.fullmatch(r"([a-z][a-z ~]*?)(?:\s*=(.*))?", fragment)
        if match is None:
            raise ValueError(f"invalid key-expression fragment {fragment!r}")
        name, value = match.groups()
        parsed.append((name.replace("~", " ").strip(), value))
    if not parsed:
        raise ValueError("empty key expression")
    return parsed


def _enum_value_error(
    target: str,
    value: str | None,
    target_record: tuple[str, str],
) -> str | None:
    """Describe an invalid explicit enum value in a registry rewrite."""
    if value is None:
        return None
    value_type = target_record[1]
    enum = re.fullmatch(r"enum\(([^)]*)\)", value_type)
    if enum is not None and value not in enum.group(1).split("|"):
        return f"replacement value {value!r} for {target!r} is not in {value_type}"
    return None


def _group(text: str, start: int) -> tuple[str, int]:
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] != "{":
        raise ValueError(f"expected '{{' at registry offset {start}")
    depth = 1
    out: list[str] = []
    i = start + 1
    while i < len(text) and depth:
        char = text[i]
        if char == "\\" and i + 1 < len(text):
            out.extend((char, text[i + 1]))
            i += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return "".join(out).strip(), i + 1
        out.append(char)
        i += 1
    raise ValueError(f"unclosed registry group at offset {start}")


def load_registry() -> list[Entry]:
    text = REGISTRY.read_text(encoding="utf-8")
    pattern = re.compile(
        r"\\__tenkz_language_registry_(environment|command|key|alias|example):[n]+"
    )
    entries: list[Entry] = []
    for match in pattern.finditer(text):
        kind = match.group(1)
        pos = match.end()
        fields: list[str] = []
        for _ in range(ARITIES[kind]):
            field, pos = _group(text, pos)
            fields.append(field)
        entries.append(Entry(kind, tuple(fields)))
    return entries


def _declared_api() -> tuple[set[str], set[str]]:
    commands: set[str] = {"tnset"}
    environments: set[str] = set()
    for path in (ROOT / "tex/tenkz").glob("*.code.tex"):
        text = path.read_text(encoding="utf-8")
        commands.update(re.findall(r"\\NewDocumentCommand\s+\\([A-Za-z]+)", text))
        environments.update(
            re.findall(r"\\NewDocumentEnvironment\s*\{\s*([A-Za-z]+)", text)
        )
    return commands, environments


def _parser_leaf_keys_from_texts(texts: Iterable[str]) -> set[tuple[str, str]]:
    """Collect public leaf-key spellings from TeX parser source texts."""
    leaves: set[tuple[str, str]] = set()
    leaf = re.compile(
        r"/tenkz/([^/,{]+?)/([^/,{]+?)/\.(?:code|store~in|is~choice)"
        r"(?=\s*[,=])"
    )
    root_leaf = re.compile(
        r"/tenkz/([^/,{]+?)/\.(?:code|store~in|is~choice)(?=\s*[,=])"
    )
    forwards = re.compile(
        r"(?m)^\\tenkz_install_core_forwards:nn\s*\{[^}]+\}\s*\{([^}]+)\}"
    )
    for text in texts:
        for match in leaf.finditer(text):
            family = match.group(1).replace("~", " ").strip()
            name = match.group(2).replace("~", " ").strip()
            if family not in {"#1", "tensor style"} and name != ".unknown":
                leaves.add((family, name))
        for match in forwards.finditer(text):
            family_match = re.search(r"\{([^}]+)\}", match.group(0))
            assert family_match is not None
            family = family_match.group(1).replace("~", " ").strip()
            leaves.update(
                (family, item.replace("~", " ").strip())
                for item in match.group(1).split(",")
            )
        for match in root_leaf.finditer(text):
            name = match.group(1).replace("~", " ").strip()
            if name not in {"", "declare atom"}:
                leaves.add(("setup", name))
    return leaves


# Extension-gate: #4687; Census-correction: #4753 includes hyphenated
# kernel families in the parser-path census.
_KERNEL_HELPER = re.compile(
    r"\\__tenkz_kernel_"
    r"(?:value:nnn|choice:nnnn|flag:nnn|positive_integer:nnn)\s*"
    r"\{\s*tenkz-kernel-([a-z]+(?:-[a-z]+)*)\s*\}\s*\{\s*([^}]+?)\s*\}"
)
_KERNEL_BLOCK = re.compile(
    r"\\keys_define:nn\s*\{\s*tenkz-kernel-([a-z]+(?:-[a-z]+)*)\s*\}"
)
_KERNEL_LINE = re.compile(
    r"^\s*([a-z][a-z ~-]*?)\s*\.(?:code:n|meta:n|choices:nn)\s*="
)


def _kernel_leaf_keys_from_texts(texts) -> set[tuple[str, str]]:
    """Collect l3keys leaves installed by the kernel language stage."""
    leaves: set[tuple[str, str]] = set()
    for text in texts:
        for match in _KERNEL_HELPER.finditer(text):
            leaves.add((f"kernel-{match.group(1)}",
                        match.group(2).replace("~", " ").strip()))
        family = None
        depth = 0
        for line in text.splitlines():
            if family is None:
                block = _KERNEL_BLOCK.search(line)
                if block:
                    family = f"kernel-{block.group(1)}"
                    depth = line.count("{") - line.count("}")
                continue
            depth += line.count("{") - line.count("}")
            key = _KERNEL_LINE.match(line)
            if key and key.group(1).strip() != "unknown":
                leaves.add((family, key.group(1).replace("~", " ").strip()))
            if depth <= 0:
                family = None
    return leaves


def _parser_leaf_keys() -> set[tuple[str, str]]:
    """Collect public leaf-key spellings installed by the TeX parsers.

    Choice values and family roots are deliberately excluded.  Shared
    forwards are expanded so the census fails if implementation and registry
    drift in either direction.
    """
    texts = [
        path.read_text(encoding="utf-8")
        for path in (ROOT / "tex/tenkz").glob("*.code.tex")
    ]
    return _parser_leaf_keys_from_texts(texts) | _kernel_leaf_keys_from_texts(texts)


def _parser_registry_keys() -> set[tuple[str, str]]:
    """Collapse parser families onto the public registry ownership scopes."""
    scoped: set[tuple[str, str]] = set()
    for family, name in _parser_leaf_keys():
        if family not in _PARSER_FAMILY_SCOPE:
            raise ValueError(f"parser family {family!r} has no registry scope")
        scope = (
            "setup"
            if name in _SETUP_FORWARDS.get(family, set())
            else _PARSER_FAMILY_SCOPE[family]
        )
        scoped.add((scope, name))
    return scoped


def check(entries: list[Entry]) -> list[str]:
    errors: list[str] = []
    by_kind = {
        kind: [entry.fields for entry in entries if entry.kind == kind]
        for kind in ARITIES
    }
    for kind, rows in by_kind.items():
        names = [row[0] if kind != "key" else f"{row[0]}:{row[1]}" for row in rows]
        duplicates = sorted(name for name in set(names) if names.count(name) > 1)
        if duplicates:
            errors.append(f"duplicate {kind} records: {', '.join(duplicates)}")
    registered_commands = {row[0] for row in by_kind["command"]}
    registered_environments = {row[0] for row in by_kind["environment"]}
    declared_commands, declared_environments = _declared_api()
    missing_commands = sorted(declared_commands - registered_commands)
    missing_environments = sorted(declared_environments - registered_environments)
    absent_commands = sorted(registered_commands - declared_commands - {"tndeclareatom"})
    if missing_commands:
        errors.append(f"accidental public commands: {', '.join(missing_commands)}")
    if missing_environments:
        errors.append(f"accidental public environments: {', '.join(missing_environments)}")
    if absent_commands:
        errors.append(f"registered commands without declarations: {', '.join(absent_commands)}")
    key_vocabulary: dict[tuple[str, str], tuple[str, str]] = {}
    for scope, name, value_type, default, status, meaning in by_kind["key"]:
        if not all((scope, name, value_type, default, status, meaning)):
            errors.append(f"incomplete key record: {scope}:{name}")
        try:
            ledger, _ = parse_status(status)
        except ValueError as exc:
            errors.append(f"{scope}:{name}: {exc}")
            continue
        key_vocabulary[(scope, name.replace("~", " "))] = (ledger, value_type)
    for scope, name, _vt, _default, status, _meaning in by_kind["key"]:
        try:
            ledger, payload = parse_status(status)
        except ValueError:
            continue
        if ledger == "sugar":
            # Expansion closure: a sugar row must spell its expansion in
            # kernel vocabulary.  Sugar that cannot expand is kernel in
            # disguise and fails here.
            try:
                expansion = parse_key_expression(payload)
            except ValueError as exc:
                errors.append(
                    f"sugar row {scope}:{name} has invalid expansion: {exc}"
                )
                continue
            unknown = [
                token
                for token, _value in expansion
                if key_vocabulary.get((scope, token), ("", ""))[0] != "kernel"
            ]
            if unknown:
                errors.append(
                    f"sugar row {scope}:{name} expansion names non-kernel "
                    f"token(s): {', '.join(unknown)}"
                )
                continue
            for target, value in expansion:
                value_error = _enum_value_error(
                    target,
                    value,
                    key_vocabulary[(scope, target)],
                )
                if value_error is not None:
                    errors.append(f"sugar row {scope}:{name} {value_error}")
        if ledger == "alias":
            try:
                replacement, _sunset = parse_alias_payload(payload)
                targets = parse_key_expression(replacement)
            except ValueError as exc:
                errors.append(f"alias row {scope}:{name}: {exc}")
                continue
            unknown = [
                token
                for token, _value in targets
                if key_vocabulary.get((scope, token), ("", ""))[0]
                not in {"kernel", "sugar"}
            ]
            if unknown:
                errors.append(
                    f"alias row {scope}:{name} replacement names unknown "
                    f"token(s): {', '.join(unknown)}"
                )
                continue
            for target, value in targets:
                value_error = _enum_value_error(
                    target,
                    value,
                    key_vocabulary[(scope, target)],
                )
                if value_error is not None:
                    errors.append(f"alias row {scope}:{name} {value_error}")
    for scope, spelling, replacement, meaning in by_kind["alias"]:
        try:
            parse_value_alias_sunset(meaning)
        except ValueError as exc:
            errors.append(f"value alias {scope}:{spelling}: {exc}")
        try:
            targets = parse_key_expression(replacement)
        except ValueError as exc:
            errors.append(f"value alias {scope}:{spelling}: {exc}")
            continue
        if len(targets) != 1 or targets[0][1] in (None, ""):
            errors.append(
                f"value alias {scope}:{spelling} replacement must be one key=value"
            )
            continue
        target, value = targets[0]
        target_record = key_vocabulary.get((scope, target))
        if target_record is None or target_record[0] not in {"kernel", "sugar"}:
            errors.append(
                f"value alias {scope}:{spelling} replacement key {target!r} "
                "is not registered vocabulary"
            )
            continue
        value_error = _enum_value_error(target, value, target_record)
        if value_error is not None:
            errors.append(
                f"value alias {scope}:{spelling} {value_error}"
            )
    if BASELINE.is_file():
        baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
        recorded = baseline["m1_census"]["value"]
        actual = public_census(entries)
        if actual != recorded:
            errors.append(
                f"ledger census {actual} != baseline {recorded}; a change is "
                "legal only as a shrink-session update or with an "
                "Extension-gate: #NNNN citation, and either way the baseline "
                "moves in the same commit"
            )
    registered_keys = {
        (row[0], row[1].replace("~", " ")) for row in by_kind["key"]
    }
    parser_keys = _parser_registry_keys()
    if registered_keys != parser_keys:
        missing = sorted(
            f"{scope}:{name}" for scope, name in parser_keys - registered_keys
        )
        extra = sorted(
            f"{scope}:{name}" for scope, name in registered_keys - parser_keys
        )
        errors.append(
            "parser/registry key census mismatch; missing=" + ",".join(missing)
            + "; extra=" + ",".join(extra)
        )
    expected_leaves = 145
    if BASELINE.is_file():
        expected_leaves = json.loads(BASELINE.read_text(encoding="utf-8"))[
            "m2_parser_paths"
        ]["value"]
    if len(_parser_leaf_keys()) != expected_leaves:
        errors.append(
            f"parser leaf-key census is {len(_parser_leaf_keys())}; expected "
            f"{expected_leaves} (raise only with an Extension-gate: #NNNN "
            "citation and the baseline bump in the same commit)"
        )
    examples = {row[0]: row for row in by_kind["example"]}
    registered_commands = {row[0] for row in by_kind["command"]}
    if set(examples) != registered_commands:
        missing = sorted(registered_commands - set(examples))
        extra = sorted(set(examples) - registered_commands)
        errors.append(
            "example census mismatch; missing=" + ",".join(missing)
            + "; extra=" + ",".join(extra)
        )
    for command, relative, failure in by_kind["example"]:
        example = ROOT / relative
        if not example.is_file():
            errors.append(f"missing example for {command}: {relative}")
            continue
        lines = example.read_text(encoding="utf-8").splitlines()
        if len(lines) > 15:
            errors.append(f"example for {command} has {len(lines)} lines; maximum is 15")
        if f"\\{command}" not in "\n".join(lines):
            errors.append(f"example for {command} does not use \\{command}")
        if not failure.strip():
            errors.append(f"example for {command} has no representative failure")
    contract_labels = ("% Input:", "% Output:", "% Owned state:", "% Invariants:", "% Next stage:")
    internal_files = [ROOT / "tex/tenkz/tenkz.sty", *sorted((ROOT / "tex/tenkz").glob("*.code.tex"))]
    for path in internal_files:
        first = path.read_text(encoding="utf-8").splitlines()[:5]
        if len(first) != 5 or any(
                not line.startswith(label) for line, label in zip(first, contract_labels)):
            errors.append(f"missing five-line stage contract: {path.relative_to(ROOT)}")
    return errors


def _tex(value: str) -> str:
    return (
        value.replace("_", r"\_")
        .replace("|", r"\textbar{}\allowbreak{}")
        .replace("(", r"(\allowbreak{}")
        .replace(",", r",\allowbreak{}")
        .replace("-", r"-\allowbreak{}")
        .replace(" ", r" \allowbreak{}")
    )


def generate_reference(entries: list[Entry]) -> None:
    commands = [e.fields for e in entries if e.kind == "command"]
    examples = {e.fields[0]: e.fields[1:] for e in entries if e.kind == "example"}
    keys = [
        e.fields
        for e in entries
        if e.kind == "key" and parse_status(e.fields[4])[0] != "alias"
    ]
    aliases = [
        e.fields
        for e in entries
        if e.kind == "key" and parse_status(e.fields[4])[0] == "alias"
    ]
    value_aliases = [e.fields for e in entries if e.kind == "alias"]
    lines = [
        "% Generated by scripts/tenkz_language.py; do not edit.",
        r"{\footnotesize",
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{30mm}"
        r">{\raggedright\arraybackslash}p{24mm}"
        r">{\raggedright\arraybackslash}p{48mm}@{}}",
        r"\toprule Command & Class & Why this is a command \\ \midrule",
    ]
    for name, category, _scope, signature, why in commands:
        lines.append(
            rf"\texttt{{\textbackslash {_tex(name)}}} & {_tex(category)} & {_tex(why)} \\"
        )
        lines.append(
            rf"\multicolumn{{3}}{{@{{}}p{{106mm}}@{{}}}}{{\footnotesize\texttt{{\detokenize{{{signature}}}}}}} \\[2pt]"
        )
        example, failure = examples[name]
        lines.append(
            rf"\multicolumn{{3}}{{@{{}}p{{106mm}}@{{}}}}{{Example: \texttt{{\detokenize{{{example}}}}}. "
            rf"Representative failure: {_tex(failure)}}} \\[3pt]"
        )
    lines.extend(
        [
            r"\bottomrule\end{longtable}",
            r"\scriptsize",
            r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{20mm}"
            r">{\raggedright\arraybackslash}p{25mm}"
            r">{\raggedright\arraybackslash}p{20mm}"
            r">{\raggedright\arraybackslash}p{20mm}"
            r">{\raggedright\arraybackslash}p{18mm}@{}}",
            r"\toprule Scope & Key & Type & Default & Meaning \\ \midrule",
        ]
    )
    for scope, name, value_type, default, _status, meaning in keys:
        lines.append(
            rf"{_tex(scope)} & \texttt{{{_tex(name)}}} & {_tex(value_type)} & "
            rf"{_tex(default)} & {_tex(meaning)} \\"
        )
    lines.append(r"\bottomrule\end{longtable}")
    lines.append("}")
    alias_lines = [
        "% Generated by scripts/tenkz_language.py; do not edit.",
        r"{\footnotesize",
        r"\begin{tabularx}{\linewidth}{@{}l l X@{}}\toprule Scope & Alias & Replacement \\ \midrule",
    ]
    for scope, name, _type, _default, status, meaning in aliases:
        alias_lines.append(
            rf"{_tex(scope)} & \texttt{{{_tex(name)}}} & {_tex(status)}; {_tex(meaning)} \\"
        )
    for scope, spelling, replacement, meaning in value_aliases:
        alias_lines.append(
            rf"{_tex(scope)} & \texttt{{{_tex(spelling)}}} & "
            rf"use \texttt{{{_tex(replacement)}}}; {_tex(meaning)} \\"
        )
    alias_lines.extend((r"\bottomrule\end{tabularx}", "}"))
    REFERENCE.parent.mkdir(parents=True, exist_ok=True)
    REFERENCE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    ALIASES.write_text("\n".join(alias_lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("check", "generate-reference", "census"))
    args = parser.parse_args()
    entries = load_registry()
    if args.action == "generate-reference":
        generate_reference(entries)
    errors = check(entries)
    if args.action == "census":
        census = {kind: sum(e.kind == kind for e in entries) for kind in ARITIES}
        census["parser_leaf_keys"] = len(_parser_leaf_keys())
        census["ledgers"] = {
            ledger: len(rows) for ledger, rows in ledger_split(entries).items()
        }
        print(json.dumps(census, sort_keys=True))
    if errors:
        for error in errors:
            print(f"tenkz-language: {error}", file=sys.stderr)
        return 1
    if args.action != "census":
        print(f"PASS: tenkz language registry ({len(entries)} records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
