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
    _parser_leaf_keys,
)

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "tests/tenkz/census-baseline.json"
SHRINK_LEDGER = ROOT / "docs/tenkz/SHRINK.md"
RMP_MANIFEST = ROOT / "tests/tenkz/rmp/manifest.toml"
BLUEPRINT = sorted(ROOT.glob("blueprint/src/chapter/*.tex"))

# Alias sunsets execute at their milestone; milestones this project uses.
CURRENT_MILESTONE = "0.8"

_SCOPE_COMMANDS = {
    "picture": ("tnpic",),
    "object": ("tn", "tnX", "tnfuse", "tndots", "tnsite", "tnput", "tntree"),
    "connection": ("tncut", "tnedge", "tnjoin", "tnarrow"),
    "region": ("tnregion",),
    "annotation": ("tnspan",),
}


def strip_comments(text: str) -> str:
    out = []
    for line in text.splitlines():
        cut = len(line)
        for index, char in enumerate(line):
            if char == "%" and (index == 0 or line[index - 1] != "\\"):
                cut = index
                break
        out.append(line[:cut])
    return "\n".join(out)


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


def _key_pattern(name: str) -> re.Pattern[str]:
    escaped = re.escape(name)
    # A key appears as `name=` or as a bare flag word inside an option list;
    # word boundaries keep `in=` from matching `\tnjoin=` style noise.
    return re.compile(
        rf"(?<![\\a-zA-Z@]){escaped}\s*=|"
        rf"(?<![\\a-zA-Z@]){escaped}(?=\s*(?:,|$))"
    )


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
    scoped = {
        scope: {} for scope in (
            "setup",
            "picture",
            "object",
            "connection",
            "region",
            "annotation",
            "atom-declaration",
        )
    }
    for path, text in corpus.items():
        scoped["picture"][path] = "\n".join(
            [*_environment_options(text), *_command_options(text, "tnpic")]
        )
        for scope, commands in _SCOPE_COMMANDS.items():
            if scope == "picture":
                continue
            scoped[scope][path] = "\n".join(
                option
                for command in commands
                for option in _command_options(text, command)
            )
        scoped["setup"][path] = "\n".join(_brace_argument(text, "tnset", 1))
        scoped["atom-declaration"][path] = "\n".join(
            _brace_argument(text, "tndeclareatom", 2)
        )
    return scoped


def row_consumers(entries: list[Entry], corpus: dict[Path, str]) -> dict[str, set[str]]:
    """Distinct consumer files per registry row, keyed by a stable row id."""
    consumers: dict[str, set[str]] = {}
    scoped = scoped_consumer_text(corpus)
    for entry in entries:
        if entry.kind == "key":
            scope, name = entry.fields[0], entry.fields[1].replace("~", " ")
            row_id = f"key:{scope}:{name}"
            pattern = _key_pattern(name)
            sources = scoped[scope]
        elif entry.kind == "command":
            row_id = f"command:{entry.fields[0]}"
            pattern = _command_pattern(entry.fields[0])
            sources = corpus
        elif entry.kind == "environment":
            row_id = f"environment:{entry.fields[0]}"
            pattern = re.compile(rf"\\begin\{{{re.escape(entry.fields[0])}\}}")
            sources = corpus
        else:
            continue
        hits = {
            str(path.relative_to(ROOT))
            for path, text in sources.items()
            if pattern.search(text)
        }
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
    escape_usage = 0
    scoped = scoped_consumer_text(corpus)
    for scope, name in escape_rows(entries):
        pattern = _key_pattern(name)
        escape_usage += sum(
            len(pattern.findall(text)) for text in scoped[scope].values()
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
            " an increase requires an Extension-gate citation",
            "value": len(_parser_leaf_keys()),
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

    # 100% co-occurring same-scope key pairs across at least five consumers.
    key_rows = [
        (fields[0], fields[1].replace("~", " "))
        for fields in (e.fields for e in entries if e.kind == "key")
    ]
    by_scope: dict[str, list[str]] = {}
    for scope, name in key_rows:
        by_scope.setdefault(scope, []).append(name)
    for scope, names in sorted(by_scope.items()):
        for i, first in enumerate(sorted(names)):
            hits_first = consumers.get(f"key:{scope}:{first}", set())
            if len(hits_first) < 5:
                continue
            for second in sorted(names)[i + 1 :]:
                hits_second = consumers.get(f"key:{scope}:{second}", set())
                if hits_first and hits_first == hits_second:
                    raised.append(
                        {
                            "id": f"flag:cooccur:{scope}:{first}+{second}",
                            "detail": f"{scope} keys '{first}' and '{second}' share"
                            f" all {len(hits_first)} consumers",
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


def session_verdict_ids(section: str) -> set[str]:
    """Parse exact flag IDs from two-column verdict table rows."""
    verdicts: set[str] = set()
    placeholder = "\0PIPE\0"
    decision = re.compile(
        r"^(?:keep-because|keep|dies|demoted|folds|respelled|becomes|moves|"
        r"confirmed(?:\s+merge)?|tombstoned|sugar preset|executes)\b"
    )
    expiry = re.compile(
        r"\bexpiry\s+(?:" + "|".join(re.escape(item) for item in MILESTONES) + r")\b"
    )
    executes = re.compile(
        r"^executes at the (?:"
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
        has_lifetime = (
            expiry.search(body) is not None
            or re.search(r"\bpermanent\b", body) is not None
            or executes.search(body) is not None
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


def _m1_total(snapshot: dict) -> int:
    return sum(snapshot["m1_census"]["value"].values())


def ratchet_errors(current: dict, previous: dict, *, has_extension: bool) -> list[str]:
    """Compare the checked-in baseline with its pre-change counterpart."""
    errors: list[str] = []
    current_m1 = current["m1_census"]["value"]
    previous_m1 = previous["m1_census"]["value"]

    def extension_guard(grew: bool, meter: str) -> None:
        if grew and not has_extension:
            errors.append(f"{meter} increased without an Extension-gate: #NNNN citation")

    extension_guard(_m1_total(current) > _m1_total(previous), "M1 total")
    extension_guard(
        current_m1.get("kernel", 0) > previous_m1.get("kernel", 0),
        "M1 kernel",
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
    if current["m3_escape_usage"]["value"] > previous["m3_escape_usage"]["value"]:
        errors.append("M3 escape usage increased")
    if current["m4_lines_per_case"]["value"] > previous["m4_lines_per_case"]["value"]:
        errors.append("M4 mean lines per frozen case increased")
    current_m5 = current["m5_aliases"]["value"]
    previous_m5 = previous["m5_aliases"]["value"]
    if current_m5["count"] > previous_m5["count"]:
        errors.append("M5 alias count increased")
    if current_m5["missing_sunset"]:
        errors.append("M5 contains aliases without a valid sunset")
    for name, value in current["m6_overloads"]["value"].items():
        if value > previous["m6_overloads"]["value"][name]:
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
) -> tuple[str, list[str]]:
    """Return the gate branch and any failures."""
    actual = meters(entries, corpus)
    if actual != baseline:
        return "baseline-mismatch", [
            "computed meters differ from tests/tenkz/census-baseline.json"
        ]
    if previous is not None:
        errors = ratchet_errors(baseline, previous, has_extension=has_extension)
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
        has_extension = extension_cited(args.base_ref) if previous is not None else False
    except ValueError as exc:
        print(f"tenkz-shrink: FAIL: {exc}", file=sys.stderr)
        return 1
    branch, failures = evaluate_gate(
        entries,
        corpus,
        baseline,
        previous,
        session_verdict_ids(section),
        has_extension=has_extension,
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
