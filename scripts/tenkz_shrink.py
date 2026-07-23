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
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from tenkz_language import (  # noqa: E402
    Entry,
    ledger_split,
    load_registry,
    parse_status,
    _parser_leaf_keys,
)

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "tests/tenkz/census-baseline.json"
SHRINK_LEDGER = ROOT / "docs/tenkz/SHRINK.md"
RMP_CASES = sorted(ROOT.glob("tests/tenkz/rmp/*/cases/*.tex"))
BLUEPRINT = sorted(ROOT.glob("blueprint/src/chapter/*.tex"))

# Alias sunsets execute at their milestone; milestones this project uses.
MILESTONES = ("0.8", "0.9", "1.0")
CURRENT_MILESTONE = "0.8"


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


def consumer_files() -> dict[Path, str]:
    files: dict[Path, str] = {}
    for path in RMP_CASES:
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
    return re.compile(rf"(?<![\\a-zA-Z@]){escaped}\s*=|(?<![\\a-zA-Z@]){escaped}(?=[,\]])")


def _command_pattern(name: str) -> re.Pattern[str]:
    return re.compile(rf"\\{re.escape(name)}(?![a-zA-Z])")


def row_consumers(entries: list[Entry], corpus: dict[Path, str]) -> dict[str, set[str]]:
    """Distinct consumer files per registry row, keyed by a stable row id."""
    consumers: dict[str, set[str]] = {}
    for entry in entries:
        if entry.kind == "key":
            scope, name = entry.fields[0], entry.fields[1].replace("~", " ")
            row_id = f"key:{scope}:{name}"
            pattern = _key_pattern(name)
        elif entry.kind == "command":
            row_id = f"command:{entry.fields[0]}"
            pattern = _command_pattern(entry.fields[0])
        elif entry.kind == "environment":
            row_id = f"environment:{entry.fields[0]}"
            pattern = re.compile(rf"\\begin\{{{re.escape(entry.fields[0])}\}}")
        else:
            continue
        hits = {
            str(path.relative_to(ROOT))
            for path, text in corpus.items()
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


def meters(entries: list[Entry], corpus: dict[Path, str]) -> dict[str, dict]:
    split = ledger_split(entries)
    consumers = row_consumers(entries, corpus)

    escape_usage = 0
    for scope, name in escape_rows(entries):
        pattern = _key_pattern(name)
        escape_usage += sum(len(pattern.findall(text)) for text in corpus.values())

    case_lengths = [
        len([line for line in strip_comments(p.read_text(encoding="utf-8")).splitlines() if line.strip()])
        for p in RMP_CASES
    ]

    aliases = split["alias"]
    sunsets_missing = sum(
        1 for fields in aliases if "sunset=" not in parse_status(fields[4])[1]
    )

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
            "definition": "registry key rows per ledger; kernel is one-in-one-out,"
            " the total never rises between shrink sessions",
            "value": {ledger: len(rows) for ledger, rows in split.items()},
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
            "definition": "alias rows and sunset compliance; near zero at the"
            " 1.0 freeze",
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
        pattern = re.compile(rf"\\{re.escape(name)}\s*\[([^\]]*)\]")
        for text in corpus.values():
            for options in pattern.findall(text):
                uses += 1
                keys = sorted(
                    part.split("=")[0].strip()
                    for part in options.split(",")
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

    # Alias sunsets due at or before the current milestone.
    for fields in split["alias"]:
        payload = parse_status(fields[4])[1]
        match = re.search(r"sunset=([0-9.]+)", payload)
        if match and MILESTONES.index(match.group(1)) <= MILESTONES.index(
            CURRENT_MILESTONE
        ):
            raised.append(
                {
                    "id": f"flag:sunset:{fields[0]}:{fields[1]}",
                    "detail": f"alias {fields[0]}:{fields[1]} sunset {match.group(1)}"
                    " is due",
                }
            )
    return raised


def latest_session_section(text: str) -> str:
    sections = re.split(r"(?m)^## ", text)
    # Markdown tables escape the pipe; verdict matching sees the raw id.
    return sections[-1].replace("\\|", "|") if len(sections) > 1 else ""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("meters", "flags", "gate"))
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
    # gate: census strictly decreased, or every flag has a session verdict.
    if not BASELINE.is_file():
        print("tenkz-shrink: FAIL: no census baseline; run Session 0 first", file=sys.stderr)
        return 1
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    recorded_total = sum(baseline["m1_census"]["value"].values())
    actual_total = sum(len(rows) for rows in ledger_split(entries).values())
    if actual_total < recorded_total:
        print(
            f"tenkz-shrink: PASS: census decreased {recorded_total} -> {actual_total}"
        )
        return 0
    section = (
        latest_session_section(SHRINK_LEDGER.read_text(encoding="utf-8"))
        if SHRINK_LEDGER.is_file()
        else ""
    )
    unanswered = [flag for flag in raised if flag["id"] not in section]
    if unanswered:
        for flag in unanswered:
            print(
                f"tenkz-shrink: FAIL: no verdict for {flag['id']} ({flag['detail']})",
                file=sys.stderr,
            )
        return 1
    print(
        f"tenkz-shrink: PASS: census stable at {actual_total} and all"
        f" {len(raised)} flag(s) carry verdicts"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
