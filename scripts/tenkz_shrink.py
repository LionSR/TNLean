#!/usr/bin/env python3
"""Shrink-gate meters and detectors for the tenkz language registry.

One vocabulary source: the executable registry, parsed by tenkz_language.
This tool computes the six census meters, raises the mechanical shrink
flags, and gates a milestone session: the session passes only when the
census strictly decreased or every raised flag carries a written verdict
in the latest section of docs/tenkz/SHRINK.md.

Consumer counting uses the demand corpus only -- the RMP benchmark cases
and the blueprint chapters.  Package examples and regression fixtures are
manufactured consumers and never count.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import statistics
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from tenkz_language import (  # noqa: E402
    Entry,
    MILESTONES,
    ledger_split,
    load_registry,
    parse_alias_payload,
    parse_status,
    parse_value_alias_sunset,
    public_census,
    _kernel_leaf_keys_from_texts,
    _parser_leaf_keys,
    _parser_leaf_keys_from_texts,
)
from tenkzlib.texcase import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "tests/tenkz/census-baseline.json"
SHRINK_LEDGER = ROOT / "docs/tenkz/SHRINK.md"
RMP_MANIFEST = ROOT / "tests/tenkz/rmp/manifest.toml"
BLUEPRINT = sorted(ROOT.glob("blueprint/src/chapter/*.tex"))

# Alias sunsets execute at their milestone; milestones this project uses.
CURRENT_MILESTONE = "0.8"

_SCOPE_COMMANDS = {
    "picture": ("tnpic",),
    "group": ("tngroup",),
    "object": ("tn", "tnX", "tnfuse", "tndots", "tnsite", "tnput", "tntree"),
    "connection": ("tncut", "tnedge", "tnjoin"),
    "region": ("tnregion",),
    "annotation": ("tnspan",),
}
_SETUP_COMMAND_FORWARDS = {
    "tntree": {"pitch", "compact", "inline"},
}


def manifest_case_paths() -> list[Path]:
    """Return the frozen RMP denominator after checking it against the manifest."""
    data = tomllib.loads(RMP_MANIFEST.read_text(encoding="utf-8"))
    expected = data.get("corpus", {}).get("total_targets")
    if expected != 130:
        raise ValueError(f"RMP manifest total_targets is {expected!r}; expected 130")
    raw_targets = data.get("target")
    if not isinstance(raw_targets, list):
        raise ValueError("RMP manifest has no [[target]] records")
    cases: list[Path] = []
    for index, target in enumerate(raw_targets, 1):
        case = target.get("case") if isinstance(target, dict) else None
        if not isinstance(case, str):
            raise ValueError(f"RMP manifest target {index} has no case path")
        path = ROOT / case
        if not path.is_file():
            raise ValueError(f"RMP manifest case does not exist: {case}")
        cases.append(path)
    if len(cases) != expected or len(set(cases)) != expected:
        raise ValueError("RMP manifest case paths are not 130 distinct files")
    discovered = set(ROOT.glob("tests/tenkz/rmp/*/cases/*.tex"))
    if set(cases) != discovered:
        missing = sorted(str(path.relative_to(ROOT)) for path in set(cases) - discovered)
        extra = sorted(str(path.relative_to(ROOT)) for path in discovered - set(cases))
        raise ValueError(
            "RMP case set differs from manifest; missing="
            + ",".join(missing)
            + "; extra="
            + ",".join(extra)
        )
    return cases


def consumer_files() -> dict[Path, str]:
    files: dict[Path, str] = {}
    for path in manifest_case_paths():
        files[path] = strip_comments(path.read_text(encoding="utf-8"))
    for path in BLUEPRINT:
        text = path.read_text(encoding="utf-8")
        if "begin{tenkz" in text or "\\tnpic" in text:
            files[path] = strip_comments(text)
    return files


def _command_pattern(name: str) -> re.Pattern[str]:
    return re.compile(rf"\\{re.escape(name)}(?![a-zA-Z])")


def _group_payload(text: str, start: int, opener: str, closer: str) -> tuple[str, int] | None:
    """Read one balanced TeX group, preserving nested braces in options."""
    if start >= len(text) or text[start] != opener:
        return None
    depth = 1
    brace_depth = 0
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if opener == "[":
            if char == "{":
                brace_depth += 1
            elif char == "}":
                brace_depth -= 1
            elif char == "[" and brace_depth == 0:
                depth += 1
            elif char == "]" and brace_depth == 0:
                depth -= 1
        elif char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
        if depth == 0:
            return text[start + 1 : index], index + 1
        index += 1
    return None


def _skip_space_and_star(text: str, start: int) -> int:
    while start < len(text) and text[start].isspace():
        start += 1
    if start < len(text) and text[start] == "*":
        start += 1
        while start < len(text) and text[start].isspace():
            start += 1
    return start


def _command_invocations(text: str, name: str) -> list[str | None]:
    """Return one optional-argument payload per command invocation."""
    payloads: list[str | None] = []
    for match in _command_pattern(name).finditer(text):
        start = _skip_space_and_star(text, match.end())
        group = _group_payload(text, start, "[", "]")
        payloads.append(group[0] if group is not None else None)
    return payloads


def _command_options(text: str, name: str) -> list[str]:
    return [
        payload
        for payload in _command_invocations(text, name)
        if payload is not None
    ]


def _top_level_option_parts(payload: str) -> list[str]:
    """Split an option payload on commas outside balanced groups."""
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(payload):
        char = payload[index]
        if char == "\\":
            index += 2
            continue
        if char in "{[(":
            depth += 1
        elif char in "}])":
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(payload[start:index].strip())
            start = index + 1
        index += 1
    parts.append(payload[start:].strip())
    return [part for part in parts if part]


def _option_key_names(payload: str) -> list[str]:
    """Return exact top-level key names, preserving repeated occurrences."""
    return [
        part.partition("=")[0].strip().replace("~", " ")
        for part in _top_level_option_parts(payload)
    ]


def _forwarded_options(payload: str, keys: set[str]) -> str:
    """Keep only option parts whose keys are forwarded to another scope."""
    return ",".join(
        part
        for part in _top_level_option_parts(payload)
        if part.partition("=")[0].strip().replace("~", " ") in keys
    )


def _environment_options(text: str) -> list[str]:
    payloads: list[str] = []
    pattern = re.compile(r"\\begin\{tenkz(?:cd|lattice|free|planes)?\}")
    for match in pattern.finditer(text):
        start = _skip_space_and_star(text, match.end())
        group = _group_payload(text, start, "[", "]")
        if group is not None:
            payloads.append(group[0])
    return payloads


def _brace_argument(text: str, name: str, argument: int) -> list[str]:
    payloads: list[str] = []
    for match in _command_pattern(name).finditer(text):
        start = _skip_space_and_star(text, match.end())
        groups: list[str] = []
        while len(groups) < argument:
            group = _group_payload(text, start, "{", "}")
            if group is None:
                break
            groups.append(group[0])
            start = _skip_space_and_star(text, group[1])
        if len(groups) == argument:
            payloads.append(groups[-1])
    return payloads


def scoped_consumer_text(corpus: dict[Path, str]) -> dict[str, dict[Path, str]]:
    """Option text grouped by the registry scope that owns each key."""
    return {
        scope: {
            path: "\n,\n".join(payloads)
            for path, payloads in by_path.items()
        }
        for scope, by_path in scoped_option_groups(corpus).items()
    }


def scoped_option_groups(
    corpus: dict[Path, str],
) -> dict[str, dict[Path, list[str]]]:
    """Individual option payloads grouped by their registry scope."""
    scoped = {
        scope: {} for scope in (
            "setup",
            "picture",
            "group",
            "object",
            "connection",
            "region",
            "annotation",
            "atom-declaration",
        )
    }
    for path, text in corpus.items():
        picture_options = [
            *_environment_options(text),
            *_command_options(text, "tnpic"),
        ]
        scoped["picture"][path] = picture_options
        for scope, commands in _SCOPE_COMMANDS.items():
            if scope == "picture":
                continue
            scoped[scope][path] = [
                option
                for command in commands
                for option in _command_options(text, command)
            ]
        # Setup keys are legal both in \tnset and in each picture family's
        # option list through the shared forwarders.
        scoped["setup"][path] = [
            *_brace_argument(text, "tnset", 1),
            *picture_options,
            *(
                _forwarded_options(payload, keys)
                for command, keys in _SETUP_COMMAND_FORWARDS.items()
                for payload in _command_options(text, command)
            ),
        ]
        scoped["atom-declaration"][path] = _brace_argument(
            text, "tndeclareatom", 2
        )
    return scoped


def _scope_groups(
    groups: dict[str, dict[Path, list[str]]], scope: str
) -> dict[Path, list[str]]:
    if scope in groups:
        return groups[scope]
    if scope.startswith("kernel-"):
        return {}
    raise KeyError(f"unknown registry scope: {scope}")


def row_consumers(entries: list[Entry], corpus: dict[Path, str]) -> dict[str, set[str]]:
    """Distinct consumer files per registry row, keyed by a stable row id."""
    consumers: dict[str, set[str]] = {}
    scoped = scoped_option_groups(corpus)
    for entry in entries:
        if entry.kind == "key":
            scope, name = entry.fields[0], entry.fields[1].replace("~", " ")
            row_id = f"key:{scope}:{name}"
            # kernel-* scopes have no demand-corpus constructs until the
            # S4 surface swap; their rows count zero consumers here and the
            # tenure flags they raise carry session verdicts instead.
            hits = {
                str(path.relative_to(ROOT))
                for path, payloads in _scope_groups(scoped, scope).items()
                if any(
                    name in _option_key_names(payload)
                    for payload in payloads
                )
            }
        elif entry.kind == "command":
            row_id = f"command:{entry.fields[0]}"
            pattern = _command_pattern(entry.fields[0])
            sources = corpus
            hits = {
                str(path.relative_to(ROOT))
                for path, text in sources.items()
                if pattern.search(text)
            }
        elif entry.kind == "environment":
            row_id = f"environment:{entry.fields[0]}"
            pattern = re.compile(rf"\\begin\{{{re.escape(entry.fields[0])}\}}")
            sources = corpus
            hits = {
                str(path.relative_to(ROOT))
                for path, text in sources.items()
                if pattern.search(text)
            }
        else:
            continue
        consumers[row_id] = hits
    return consumers


def escape_rows(entries: list[Entry]) -> list[tuple[str, str]]:
    return [
        (fields[0], fields[1].replace("~", " "))
        for fields in (e.fields for e in entries if e.kind == "key")
        if parse_status(fields[4])[0] == "escape"
    ]


def alias_records(entries: list[Entry]) -> list[tuple[str, str, str | None]]:
    """Return key and value aliases with normalized IDs and parsed sunsets."""
    records: list[tuple[str, str, str | None]] = []
    for entry in entries:
        if entry.kind == "key":
            ledger, payload = parse_status(entry.fields[4])
            if ledger != "alias":
                continue
            try:
                _replacement, sunset = parse_alias_payload(payload)
            except ValueError:
                sunset = None
            records.append(
                (entry.fields[0], entry.fields[1].replace("~", " "), sunset)
            )
        elif entry.kind == "alias":
            try:
                sunset = parse_value_alias_sunset(entry.fields[3])
            except ValueError:
                sunset = None
            records.append(
                (entry.fields[0], entry.fields[1].replace("~", " "), sunset)
            )
    return records


def meters(entries: list[Entry], corpus: dict[Path, str]) -> dict[str, dict]:
    parser_leaf_keys = _parser_leaf_keys()
    escape_usage = 0
    scoped = scoped_option_groups(corpus)
    for scope, name in escape_rows(entries):
        escape_usage += sum(
            _option_key_names(payload).count(name)
            for payloads in scoped[scope].values()
            for payload in payloads
        )

    cases = manifest_case_paths()
    case_lengths = [
        len(
            [
                line
                for line in strip_comments(path.read_text(encoding="utf-8")).splitlines()
                if line.strip()
            ]
        )
        for path in cases
    ]

    aliases = alias_records(entries)
    sunsets_missing = sum(sunset is None for _scope, _spelling, sunset in aliases)

    # M6: the overload co-meter.  (a) one name, several scopes, different
    # value types; (b) union value types; (c) one enum word shared by
    # several enum definitions.
    by_name: dict[str, set[str]] = {}
    enum_words: dict[str, set[str]] = {}
    union_types = 0
    for entry in entries:
        if entry.kind != "key":
            continue
        scope, name, value_type = entry.fields[0], entry.fields[1], entry.fields[2]
        by_name.setdefault(name, set()).add(value_type)
        if "|" in value_type and not value_type.startswith("enum("):
            union_types += 1
        match = re.fullmatch(r"enum\(([^)]*)\)", value_type)
        if match:
            for word in match.group(1).split("|"):
                enum_words.setdefault(word, set()).add(f"{scope}:{name}")
    multi_typed = sum(1 for types in by_name.values() if len(types) > 1)
    shared_enum_words = sum(1 for owners in enum_words.values() if len(owners) > 1)

    return {
        "m1_census": {
            "definition": "registry key rows per ledger plus public commands and"
            " environments; kernel is one-in-one-out and the total never rises"
            " between shrink sessions",
            "value": public_census(entries),
        },
        "m2_parser_paths": {
            "definition": "public leaf keys installed by the TeX parsers;"
            " identity changes require an Extension-gate citation",
            "identity_sha256": parser_leaf_fingerprint(parser_leaf_keys),
            "value": len(parser_leaf_keys),
        },
        "m3_escape_usage": {
            "definition": "occurrences of escape-ledger spellings in the demand"
            " corpus; every occurrence names a core-grammar gap",
            "value": escape_usage,
        },
        "m4_lines_per_case": {
            "definition": "mean non-comment non-blank lines over the frozen 130"
            " benchmark cases; the fidelity meter against fake shrink",
            "value": round(statistics.mean(case_lengths), 2),
        },
        "m5_aliases": {
            "definition": "key and value alias rows plus sunset compliance; near"
            " zero at the 1.0 freeze",
            "value": {"count": len(aliases), "missing_sunset": sunsets_missing},
        },
        "m6_overloads": {
            "definition": "names with several value types + union types + enum"
            " words shared across enums; must never rise",
            "value": {
                "multi_typed_names": multi_typed,
                "union_types": union_types,
                "shared_enum_words": shared_enum_words,
            },
        },
    }


def flags(entries: list[Entry], corpus: dict[Path, str]) -> list[dict[str, str]]:
    raised: list[dict[str, str]] = []
    consumers = row_consumers(entries, corpus)
    split = ledger_split(entries)

    kernel_and_sugar = {
        f"key:{fields[0]}:{fields[1].replace('~', ' ')}"
        for ledger in ("kernel", "sugar")
        for fields in split[ledger]
    }
    for row_id, hits in sorted(consumers.items()):
        if row_id.startswith("key:") and row_id not in kernel_and_sugar:
            continue
        if len(hits) < 3:
            raised.append(
                {
                    "id": f"flag:consumers:{row_id}",
                    "detail": f"{row_id} has {len(hits)} demand-corpus consumer(s)",
                }
            )

    # 100% co-occurring same-scope key pairs across at least five invocations.
    key_rows = [
        (fields[0], fields[1].replace("~", " "))
        for fields in (e.fields for e in entries if e.kind == "key")
    ]
    by_scope: dict[str, list[str]] = {}
    for scope, name in key_rows:
        by_scope.setdefault(scope, []).append(name)
    groups = scoped_option_groups(corpus)
    for scope, names in sorted(by_scope.items()):
        invocations: dict[str, set[tuple[Path, int]]] = {}
        for name in names:
            invocations[name] = {
                (path, index)
                for path, payloads in _scope_groups(groups, scope).items()
                for index, payload in enumerate(payloads)
                if name in _option_key_names(payload)
            }
        for i, first in enumerate(sorted(names)):
            hits_first = invocations[first]
            if len(hits_first) < 5:
                continue
            for second in sorted(names)[i + 1 :]:
                hits_second = invocations[second]
                if hits_first and hits_first == hits_second:
                    raised.append(
                        {
                            "id": f"flag:cooccur:{scope}:{first}+{second}",
                            "detail": f"{scope} keys '{first}' and '{second}' share"
                            f" all {len(hits_first)} invocations",
                        }
                    )

    # Value types consumed by exactly one key, excluding closed enums.
    type_owners: dict[str, list[str]] = {}
    for entry in entries:
        if entry.kind != "key":
            continue
        value_type = entry.fields[2]
        if value_type.startswith("enum("):
            continue
        type_owners.setdefault(value_type, []).append(
            f"{entry.fields[0]}:{entry.fields[1]}"
        )
    for value_type, owners in sorted(type_owners.items()):
        if len(owners) == 1:
            raised.append(
                {
                    "id": f"flag:lonely-type:{value_type}",
                    "detail": f"value type '{value_type}' has one consumer: {owners[0]}",
                }
            )

    # Commands whose corpus invocations normalize to at most two signatures.
    for entry in entries:
        if entry.kind != "command":
            continue
        name = entry.fields[0]
        signatures: set[str] = set()
        uses = 0
        for text in corpus.values():
            for options in _command_invocations(text, name):
                uses += 1
                if options is None:
                    signatures.add("")
                    continue
                keys = sorted(
                    part.split("=")[0].strip()
                    for part in _top_level_option_parts(options)
                    if part.strip()
                )
                signatures.add(",".join(keys))
        if uses >= 3 and 0 < len(signatures) <= 2:
            raised.append(
                {
                    "id": f"flag:sugar-shaped:command:{name}",
                    "detail": f"\\{name} appears {uses} times under"
                    f" {len(signatures)} option signature(s)",
                }
            )

    # Key and value alias sunsets due at or before the current milestone.
    for scope, spelling, sunset in alias_records(entries):
        if (
            sunset is not None
            and MILESTONES.index(sunset) <= MILESTONES.index(CURRENT_MILESTONE)
        ):
            raised.append(
                {
                    "id": f"flag:sunset:{scope}:{spelling}",
                    "detail": f"alias {scope}:{spelling} sunset {sunset} is due",
                }
            )
    return raised


def latest_session_section(text: str) -> str:
    sections = re.split(r"(?m)^## ", text)
    return sections[-1] if len(sections) > 1 else ""


def session_verdict_ids(
    section: str,
    *,
    current_milestone: str = CURRENT_MILESTONE,
) -> set[str]:
    """Parse unexpired flag verdicts from two-column table rows."""
    if current_milestone not in MILESTONES:
        raise ValueError(f"unsupported current milestone {current_milestone!r}")
    current_index = MILESTONES.index(current_milestone)
    verdicts: set[str] = set()
    placeholder = "\0PIPE\0"
    decision = re.compile(
        r"^(?:keep-because|keep|dies|demoted|folds|respelled|becomes|moves|"
        r"confirmed(?:\s+merge)?|tombstoned|sugar preset|executes)\b"
    )
    expiry = re.compile(
        r"\bexpiry\s+("
        + "|".join(re.escape(item) for item in MILESTONES)
        + r")\b"
    )
    executes = re.compile(
        r"^executes at the ("
        + "|".join(re.escape(item) for item in MILESTONES)
        + r") freeze\b"
    )
    for line in section.splitlines():
        if not line.startswith("|"):
            continue
        cells = [
            cell.replace(placeholder, "|").strip()
            for cell in line.replace("\\|", placeholder).strip("|").split("|")
        ]
        if len(cells) < 2 or not cells[0].startswith("flag:"):
            continue
        body = cells[1]
        if not decision.search(body):
            continue
        expiry_match = expiry.search(body)
        executes_match = executes.search(body)
        expiry_valid = (
            expiry_match is not None
            and MILESTONES.index(expiry_match.group(1)) >= current_index
        )
        executes_valid = (
            executes_match is not None
            and MILESTONES.index(executes_match.group(1)) >= current_index
        )
        has_lifetime = (
            expiry_valid
            or re.search(r"\bpermanent\b", body) is not None
            or executes_valid
        )
        if has_lifetime:
            verdicts.add(cells[0])
    return verdicts


def baseline_at_ref(ref: str) -> dict | None:
    """Read the baseline committed at a Git ref, or None before Session 0."""
    result = subprocess.run(
        ["git", "show", f"{ref}:tests/tenkz/census-baseline.json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        exists = subprocess.run(
            ["git", "cat-file", "-e", f"{ref}^{{commit}}"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if exists.returncode:
            raise ValueError(f"base ref does not resolve: {ref}")
        return None
    return json.loads(result.stdout)


def ledger_at_ref(ref: str) -> str | None:
    """Read the shrink ledger at a Git ref, or None before Session 0."""
    result = subprocess.run(
        ["git", "show", f"{ref}:docs/tenkz/SHRINK.md"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        exists = subprocess.run(
            ["git", "cat-file", "-e", f"{ref}^{{commit}}"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if exists.returncode:
            raise ValueError(f"base ref does not resolve: {ref}")
        return None
    return result.stdout


def ledger_history_errors(current: str, previous: str | None) -> list[str]:
    """Require every pre-change ledger byte to remain an exact prefix."""
    if previous is not None and not current.startswith(previous):
        return [
            "docs/tenkz/SHRINK.md rewrites pre-change history; "
            "shrink sessions are append-only"
        ]
    return []


def added_diff_text(patch: str) -> str:
    """Return only added content lines from a unified Git patch."""
    return "\n".join(
        line[1:]
        for line in patch.splitlines()
        if line.startswith("+") and not line.startswith("+++")
    )


def extension_cited(ref: str) -> bool:
    """Whether the PR diff carries the numeric extension-gate citation."""
    result = subprocess.run(
        ["git", "diff", "--merge-base", ref, "HEAD", "--"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        raise ValueError(f"cannot diff against base ref {ref}: {result.stderr.strip()}")
    return (
        re.search(
            r"Extension-gate:\s*#[0-9]+",
            added_diff_text(result.stdout),
        )
        is not None
    )


def census_correction_cited(ref: str) -> bool:
    """Whether added diff lines cite a reviewed census correction."""
    result = subprocess.run(
        ["git", "diff", "--merge-base", ref, "HEAD", "--"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode:
        raise ValueError(f"cannot diff against base ref {ref}: {result.stderr.strip()}")
    return (
        re.search(
            r"Census-correction:\s*#[0-9]+",
            added_diff_text(result.stdout),
        )
        is not None
    )


def _m1_total(snapshot: dict) -> int:
    return sum(snapshot["m1_census"]["value"].values())


def parser_leaf_fingerprint(keys: set[tuple[str, str]]) -> str:
    """Return a stable digest of the exact parser family/key identities."""
    payload = "\n".join(f"{family}\0{name}" for family, name in sorted(keys))
    return hashlib.sha256(payload.encode()).hexdigest()


def parser_leaf_fingerprint_from_texts(texts: list[str]) -> str:
    """Fingerprint every legacy and kernel parser leaf in source texts."""
    keys = (
        _parser_leaf_keys_from_texts(texts)
        | _kernel_leaf_keys_from_texts(texts)
    )
    return parser_leaf_fingerprint(keys)


def parser_leaf_fingerprint_at_ref(ref: str) -> str:
    """Return the exact parser-leaf fingerprint from a Git tree."""
    listed = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, "--", "tex/tenkz"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if listed.returncode:
        raise ValueError(
            f"cannot list parser sources at {ref}: {listed.stderr.strip()}"
        )
    paths = [
        path
        for path in listed.stdout.splitlines()
        if path.endswith(".code.tex")
    ]
    texts: list[str] = []
    for path in paths:
        shown = subprocess.run(
            ["git", "show", f"{ref}:{path}"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if shown.returncode:
            raise ValueError(
                f"cannot read parser source {path} at {ref}: "
                f"{shown.stderr.strip()}"
            )
        texts.append(shown.stdout)
    return parser_leaf_fingerprint_from_texts(texts)


def ratchet_errors(
    current: dict,
    previous: dict,
    *,
    has_extension: bool,
    has_census_correction: bool = False,
    previous_parser_fingerprint: str | None = None,
) -> list[str]:
    """Compare the checked-in baseline with its pre-change counterpart."""
    errors: list[str] = []
    current_m1 = current["m1_census"]["value"]
    previous_m1 = previous["m1_census"]["value"]
    current_parser_fingerprint = current["m2_parser_paths"].get(
        "identity_sha256"
    )
    if previous_parser_fingerprint is None:
        previous_parser_fingerprint = previous["m2_parser_paths"].get(
            "identity_sha256"
        )
    parser_paths_unchanged = (
        current_parser_fingerprint is not None
        and previous_parser_fingerprint is not None
        and current_parser_fingerprint == previous_parser_fingerprint
    )
    correction_allowed = has_census_correction and parser_paths_unchanged

    def extension_guard(
        grew: bool,
        meter: str,
        *,
        allow_correction: bool = False,
    ) -> None:
        if (
            grew
            and not has_extension
            and not (allow_correction and correction_allowed)
        ):
            errors.append(f"{meter} increased without an Extension-gate: #NNNN citation")

    extension_guard(
        _m1_total(current) > _m1_total(previous),
        "M1 total",
        allow_correction=True,
    )
    extension_guard(
        current_m1.get("kernel", 0) > previous_m1.get("kernel", 0),
        "M1 kernel",
        allow_correction=True,
    )
    for surface in ("commands", "environments"):
        extension_guard(
            current_m1.get(surface, 0) > previous_m1.get(surface, 0),
            f"M1 {surface}",
        )
    extension_guard(
        current["m2_parser_paths"]["value"] > previous["m2_parser_paths"]["value"],
        "M2 parser paths",
    )
    if (
        current_parser_fingerprint != previous_parser_fingerprint
        and not has_extension
    ):
        errors.append(
            "M2 parser identities changed without an Extension-gate: "
            "#NNNN citation"
        )
    # M3 and M4 measure demand and fidelity, not size, and both can rise for
    # the right reason: a figure hand-routed through an escape hatch names a
    # gap in the grammar, and a figure that gains the indices its source
    # asserts gains lines.  Refusing every rise makes the meters argue against
    # correctness, so a rise is admitted on the same terms M1 already uses --
    # a dated verdict in the ledger citing the correction.  A rise carrying no
    # verdict is still refused, which is the case the meters exist to catch.
    if (
        current["m3_escape_usage"]["value"]
        > previous["m3_escape_usage"]["value"]
        and not has_census_correction
    ):
        errors.append(
            "M3 escape usage increased without a Census-correction: #NNNN "
            "verdict naming the grammar gap the new occurrences stand in for"
        )
    if (
        current["m4_lines_per_case"]["value"]
        > previous["m4_lines_per_case"]["value"]
        and not has_census_correction
    ):
        errors.append(
            "M4 mean lines per frozen case increased without a "
            "Census-correction: #NNNN verdict"
        )
    current_m5 = current["m5_aliases"]["value"]
    previous_m5 = previous["m5_aliases"]["value"]
    if current_m5["count"] > previous_m5["count"]:
        errors.append("M5 alias count increased")
    if current_m5["missing_sunset"]:
        errors.append("M5 contains aliases without a valid sunset")
    for name, value in current["m6_overloads"]["value"].items():
        if (
            value > previous["m6_overloads"]["value"][name]
            and not correction_allowed
        ):
            errors.append(f"M6 overload component {name} increased")
    return errors


def evaluate_gate(
    entries: list[Entry],
    corpus: dict[Path, str],
    baseline: dict,
    previous: dict | None,
    verdicts: set[str],
    *,
    has_extension: bool,
    has_census_correction: bool = False,
    previous_parser_fingerprint: str | None = None,
) -> tuple[str, list[str]]:
    """Return the gate branch and any failures."""
    actual = meters(entries, corpus)
    if actual != baseline:
        return "baseline-mismatch", [
            "computed meters differ from tests/tenkz/census-baseline.json"
        ]
    if previous is not None:
        errors = ratchet_errors(
            baseline,
            previous,
            has_extension=has_extension,
            has_census_correction=has_census_correction,
            previous_parser_fingerprint=previous_parser_fingerprint,
        )
        if errors:
            return "ratchet", errors
        if _m1_total(baseline) < _m1_total(previous):
            return "decreased", []
    raised = flags(entries, corpus)
    unanswered = [flag for flag in raised if flag["id"] not in verdicts]
    return "verdicts", [
        f"no verdict for {flag['id']} ({flag['detail']})" for flag in unanswered
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("meters", "flags", "gate"))
    parser.add_argument(
        "--base-ref",
        help="pre-change Git ref whose baseline supplies the per-PR ratchet",
    )
    args = parser.parse_args()
    entries = load_registry()
    corpus = consumer_files()
    if args.action == "meters":
        print(json.dumps(meters(entries, corpus), indent=2, sort_keys=True))
        return 0
    raised = flags(entries, corpus)
    if args.action == "flags":
        for flag in raised:
            print(f"{flag['id']}  --  {flag['detail']}")
        print(f"{len(raised)} flag(s)")
        return 0
    # gate: enforce the per-PR ratchet, then accept a census decrease or
    # structured verdict rows for every current flag.
    if not BASELINE.is_file():
        print("tenkz-shrink: FAIL: no census baseline; run Session 0 first", file=sys.stderr)
        return 1
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    section = (
        latest_session_section(SHRINK_LEDGER.read_text(encoding="utf-8"))
        if SHRINK_LEDGER.is_file()
        else ""
    )
    try:
        previous = baseline_at_ref(args.base_ref) if args.base_ref else None
        previous_parser_fingerprint = (
            parser_leaf_fingerprint_at_ref(args.base_ref)
            if previous is not None
            else None
        )
        has_extension = extension_cited(args.base_ref) if previous is not None else False
        has_census_correction = (
            census_correction_cited(args.base_ref)
            if previous is not None
            else False
        )
        previous_ledger = ledger_at_ref(args.base_ref) if args.base_ref else None
    except ValueError as exc:
        print(f"tenkz-shrink: FAIL: {exc}", file=sys.stderr)
        return 1
    ledger_failures = ledger_history_errors(
        SHRINK_LEDGER.read_text(encoding="utf-8"),
        previous_ledger,
    )
    if ledger_failures:
        for failure in ledger_failures:
            print(f"tenkz-shrink: FAIL: {failure}", file=sys.stderr)
        return 1
    branch, failures = evaluate_gate(
        entries,
        corpus,
        baseline,
        previous,
        session_verdict_ids(section),
        has_extension=has_extension,
        has_census_correction=has_census_correction,
        previous_parser_fingerprint=previous_parser_fingerprint,
    )
    if failures:
        for failure in failures:
            print(f"tenkz-shrink: FAIL: {failure}", file=sys.stderr)
        return 1
    if branch == "decreased":
        assert previous is not None
        print(
            f"tenkz-shrink: PASS: census decreased "
            f"{_m1_total(previous)} -> {_m1_total(baseline)}"
        )
    else:
        print(
            f"tenkz-shrink: PASS: census stable at {_m1_total(baseline)} and all"
            f" {len(raised)} flag(s) carry verdicts"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
