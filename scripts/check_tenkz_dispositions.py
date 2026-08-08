#!/usr/bin/env python3
"""Verify that the tenkz migration ledger matches the tracked TeX sources."""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from tenkzlib.texcase import (
    Construct,
    following_group,
    following_group_span,
    match_group,
    scan_constructs,
    strip_comments,
    top_level_options,
)
from tenkz_language import load_registry


DOCUMENT = ROOT / "docs/tenkz/DISPOSITIONS.md"
BLUEPRINT_ROOT = ROOT / "blueprint/src/chapter"
FIXTURE_ROOT = ROOT / "tests/tenkz"
ENVIRONMENT = re.compile(
    r"\\begin\s*\{\s*(tenkz(?:eq|free|cd|lattice|planes)?)\s*\}"
)
COMMAND = re.compile(r"\\(tnpic|tntree)\b")
TENKZEQ_TOKEN = re.compile(r"\\(begin|end)\{tenkzeq\}")
SETUP_COMMAND = re.compile(r"\\(?:tnset|tndeclare(?:atom)?|tenkzkernel)\b")
DISPOSITIONS = ("preserve", "codemod", "redraw")
DEAD_COMMANDS = (
    "tnput",
    "tnjoin",
    "tnedge",
    "tnarrow",
    "tnsite",
    "tnghost",
    "tncut",
    "tnregion",
    "tnprose",
)
DEAD_KEYS = (
    "out",
    "in",
    "label shift",
    "col vector",
    "row vector",
    "sheet vector",
    "maps",
    "polygon",
    "radius",
    "tensor style",
    "wiring",
    "trace style",
    "via",
    "bend",
    "weight",
    "nudge",
    "inset",
    "slot",
    "check",
    "chain axis",
    "legs at",
    "boundary legs",
    "label at",
    "poly",
    "bond dir",
    "up",
    "down",
)
SUGAR_COMMANDS = (
    "tnX",
    "tnbond",
    "tnstring",
    "tnfuse",
    "tnspan",
    "tndots",
    "tnskip",
)
# Sugar commands the kernel tier binds to their signed expansions.  Under
# `\tenkzkernel` these owe no migration work, exactly as a key with a signed
# `kernel-` registry row owes none: the surface switch reads them as their
# ledger expansions where they stand.
KERNEL_SUGAR_COMMANDS = frozenset({"tnbond", "tnfuse"})
BARE_DEAD_FLAGS = ("boundary legs", "maps")
SIGNED_KEYS_BY_SCOPE = {
    scope: {
        entry.fields[1].replace("~", " ")
        for entry in load_registry()
        if entry.kind == "key" and entry.fields[0] == f"kernel-{scope}"
    }
    for scope in ("picture", "atom", "wire", "mark", "setup", "declare")
}
COMPATIBILITY_KEYS = {
    "picture": {
        "inline",
        "compact",
        "fused",
        "periodic",
        "west label",
        "east label",
        "north label",
        "south label",
        "bond label",
        "planes",
        *BARE_DEAD_FLAGS,
    },
    "atom": {
        "box",
        "dot",
        "pill",
        "mpo",
        "ring",
        "no legs",
        "circle",
        "boundary",
        "removed",
        "enclosure",
        "tri",
        "combined",
        "span",
        "up at",
        "down at",
        "west at",
        "east at",
        *DEAD_KEYS,
    },
    "wire": {"none", "bond dir", *DEAD_KEYS},
    "mark": {"brace above", "brace below", *DEAD_KEYS},
    "setup": {"species"},
    "declare": set(),
}
OPTION_SCOPES = {
    "tn": "atom",
    "tnX": "atom",
    "tnfuse": "atom",
    "tntree": "atom",
    "tnwire": "wire",
    "tnbond": "wire",
    "tnstring": "wire",
    "tnmark": "mark",
    "tngroup": "picture",
    "tnspan": "mark",
    "tnpic": "picture",
    "tnput": "atom",
    "tnsite": "atom",
    "tnghost": "atom",
    "tnjoin": "wire",
    "tnedge": "wire",
    "tnarrow": "wire",
    "tncut": "mark",
    "tnregion": "mark",
    "tnprose": "mark",
}


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


def normalized_environment_spacing(source: str) -> str:
    """Normalize tenkz tokens without changing source length or line count."""
    pattern = re.compile(
        r"\\(begin|end)(\s*)\{(\s*)"
        r"(tenkz(?:eq|free|cd|lattice|planes)?)(\s*)\}"
    )

    def replace(match: re.Match[str]) -> str:
        whitespace = match.group(2) + match.group(3) + match.group(5)
        return rf"\{match.group(1)}{{{match.group(4)}}}" + whitespace

    return pattern.sub(replace, source)


def encountered_option_groups(source: str) -> list[tuple[str, str]]:
    """Return every public option group with its signed registry scope."""
    groups: list[tuple[str, str]] = []
    for match in ENVIRONMENT.finditer(source):
        options = following_group(source, match.end(), "[", "]")
        if options is not None:
            groups.append(("picture", options))
    commands = "|".join(sorted(OPTION_SCOPES, key=len, reverse=True))
    for match in re.finditer(rf"\\({commands})\*?(?![A-Za-z])", source):
        options = following_group(source, match.end(), "[", "]")
        if options is not None:
            groups.append((OPTION_SCOPES[match.group(1)], options))
    for match in re.finditer(r"\\tnset\b", source):
        options = following_group(source, match.end(), "{", "}")
        if options is not None:
            groups.append(("setup", options))
    for match in re.finditer(r"\\tndeclare\b", source):
        position = match.end()
        arguments: list[str] = []
        for _ in range(3):
            group = following_group_span(source, position, "{", "}")
            if group is None:
                break
            argument, position = group
            arguments.append(argument)
        if len(arguments) == 3:
            groups.append(("declare", arguments[2]))
    for match in re.finditer(r"\\tndeclareatom\b", source):
        position = match.end()
        arguments: list[str] = []
        for _ in range(2):
            group = following_group_span(source, position, "{", "}")
            if group is None:
                break
            argument, position = group
            arguments.append(argument)
        if len(arguments) == 2:
            groups.append(("atom", arguments[1]))
    return groups


def encountered_options(source: str) -> list[tuple[str, str, str | None]]:
    """Return parsed public options as scope, key, and optional value."""
    return [
        (scope, key, value)
        for scope, group in encountered_option_groups(source)
        for key, value in top_level_options(group)
    ]


def unrecognized_option_keys(source: str) -> set[str]:
    """Find option keys outside the signed 1.0 grammar and classified sugar."""
    unknown: set[str] = set()

    def check(options: str, scope: str) -> None:
        allowed = SIGNED_KEYS_BY_SCOPE[scope] | COMPATIBILITY_KEYS[scope]
        unknown.update(
            key for key, _value in top_level_options(options) if key not in allowed
        )

    for scope, options in encountered_option_groups(source):
        check(options, scope)
    return unknown


def scan_inventory_constructs(source: str) -> list[Construct]:
    """Scan picture constructs plus the non-picture `tenkzeq` wrapper."""
    constructs = scan_constructs(source)
    for match in re.finditer(r"\\begin\{tenkzeq\}", source):
        depth = 1
        end_match: re.Match[str] | None = None
        for token in TENKZEQ_TOKEN.finditer(source, match.end()):
            depth += 1 if token.group(1) == "begin" else -1
            if depth == 0:
                end_match = token
                break
        end = end_match.end() if end_match else len(source)
        body_start = match.end()
        if source[body_start : body_start + 1] == "[":
            closed = match_group(source, body_start, "[", "]")
            if closed != -1:
                body_start = closed
        body_end = end_match.start() if end_match else len(source)
        constructs.append(
            Construct(
                "tenkzeq",
                match.start(),
                end,
                source[body_start:body_end],
                source.count("\n", 0, match.start()) + 1,
                body_start,
            )
        )
    constructs.sort(key=lambda construct: construct.start)
    return constructs


def construct_sources(
    path: Path,
) -> dict[tuple[str, int, str], list[tuple[str, bool]]]:
    """Return each construct's source slice and whether the kernel reaches it.

    Since the S4 surface swap the package binds the kernel surface at load,
    so the kernel reaches every construct; a document's own `\\tenkzkernel`
    call rebinds the same meanings and is inert.
    """
    source = normalized_environment_spacing(
        strip_comments(path.read_text(errors="replace"))
    )
    result: dict[tuple[str, int, str], list[tuple[str, bool]]] = defaultdict(list)
    for construct in scan_inventory_constructs(source):
        key = (path.name, construct.line, construct.name)
        result[key].append(
            (source[construct.start : construct.end], True)
        )
    return result


def expanded_source(path: Path, stack: tuple[Path, ...] = ()) -> str:
    """Expand local input files so fixture disposition includes dependencies."""
    path = path.resolve()
    if path in stack:
        fail(f"recursive fixture input: {' -> '.join(map(str, stack + (path,)))}")
    source = strip_comments(path.read_text(errors="replace"))

    def replace(match: re.Match[str]) -> str:
        dependency = (path.parent / (match.group(1) or match.group(2))).resolve()
        if not dependency.suffix:
            dependency = dependency.with_suffix(".tex")
        if not dependency.is_file():
            return match.group(0)
        return expanded_source(dependency, stack + (path,))

    return re.sub(
        r"\\(?:input|include)\s*(?:\{\s*([^}]+?)\s*\}|([^\s%{}]+))",
        replace,
        source,
    )


def fragment_target_codes(source: str, kernel: bool = False) -> frozenset[str]:
    r"""Classify one construct or construct-free source fragment.

    `kernel` says the `\tenkzkernel` switch reaches this fragment, so its keys
    already carry their 1.0 meaning. A key with a signed `kernel-` registry
    row then owes no migration work, whether the row is kernel or sugar: the
    surface switch leaves it spelled exactly as it stands. The same key on a
    0.7 picture still owes one, because the two tiers read several of these
    keys differently — 0.7 `boundary=` sets all four sides where the kernel
    sets west and east, and 0.7 `physical=` is a row topology where the
    kernel's is a per-cell port policy.
    """
    public_commands = (
        "tn",
        "tnwire",
        "tnmark",
        "tngroup",
        "tnset",
        "tndeclare",
        "tndeclareatom",
        "tenkzkernel",
        *DEAD_COMMANDS,
        *SUGAR_COMMANDS,
    )
    public = bool(
        ENVIRONMENT.search(source)
        or COMMAND.search(source)
        or any(re.search(rf"\\{name}\b", source) for name in public_commands)
    )
    if not public:
        return frozenset({"P-none"})

    codes: set[str] = set()
    environments = set(ENVIRONMENT.findall(source))
    environment_codes = {
        "tenkzfree": "R-free",
        "tenkzcd": "R-cd",
        "tenkzlattice": "R-lattice",
        "tenkzplanes": "R-plane",
    }
    codes.update(
        environment_codes[name] for name in environments if name in environment_codes
    )

    options = encountered_options(source)
    keys = {key for _scope, key, _value in options}
    keys_by_scope = {
        scope: {key for option_scope, key, _value in options if option_scope == scope}
        for scope in SIGNED_KEYS_BY_SCOPE
    }
    migrating_by_scope = {
        scope: scope_keys - SIGNED_KEYS_BY_SCOPE[scope] if kernel else scope_keys
        for scope, scope_keys in keys_by_scope.items()
    }
    migrating = set().union(*migrating_by_scope.values())
    tn_options: list[tuple[str, str | None]] = []
    for match in re.finditer(r"\\tn\*?(?![A-Za-z])", source):
        group = following_group(source, match.end(), "[", "]")
        if group is not None:
            tn_options.extend(top_level_options(group))
    tn_keys = {key for key, _value in tn_options}
    bare_tn_keys = {key for key, value in tn_options if value is None}

    def values(key: str) -> list[str]:
        return [
            value.lstrip("{").strip()
            for _scope, option_key, value in options
            if option_key == key and value is not None
        ]

    dead_record = any(re.search(rf"\\{name}\b", source) for name in DEAD_COMMANDS)
    dead_record |= bool(keys & set(DEAD_KEYS))
    dead_record |= bool(
        keys
        & {
            "inline",
            "compact",
            "fused",
            "none",
            "brace above",
            "brace below",
            *BARE_DEAD_FLAGS,
        }
    )
    dead_record |= any(
        re.match(r"(?:hv|vh|curve|drop|hug)\b", value)
        for value in values("route")
    )
    dead_record |= any(
        re.match(r"vertical\b|(?:rotate|matrix)\s*=", value)
        for value in values("frame")
    )
    dead_record |= any(":" in value for value in values("rows"))
    dead_record |= any(
        re.match(r"(?:brace-(?:below|above)|cut|band|prose)\b", value)
        for value in values("form")
    )
    dead_record |= any(
        re.match(r"(?:cluster|enclosure)\b", value) for value in values("skin")
    )
    dead_record |= any(
        re.match(r"string\b", value) for value in values("weight")
    )
    dead_record |= any(
        re.search(
            r"\bleg\s+(?:north|south|east|west)\s+of\b"
            r"|\b(?:north|south|east|west)\s+outside\b",
            value,
        )
        for _scope, _key, value in options
        if value is not None
    )
    # A subtracted selector term is kernel grammar (#5565): a mark states a
    # staircase or a complement in the language itself, so the spelling is
    # preserved rather than redrawn.
    unknown_keys = unrecognized_option_keys(source)
    dead_record |= bool(unknown_keys) and not any(
        code.startswith("R-") for code in codes
    )
    dead_record |= bool(
        bare_tn_keys & {"circle", "boundary", "removed", "cluster", "enclosure"}
    )
    dead_record |= "tri" in tn_keys
    if tn_keys & {"box", "dot", "pill", "mpo", "ring", "no legs"}:
        codes.add("C-record")
    if "cluster" in migrating_by_scope["atom"] and any(
        key == "cluster" and value is not None for key, value in tn_options
    ):
        codes.add("C-record")
    if dead_record:
        codes.add("R-record")

    if COMMAND.search(source) and re.search(r"\\tnpic\b", source):
        codes.add("C-picture")
    if re.search(r"\\tntree\b", source):
        codes.add("C-tree")
    # The kernel side grammar takes `cup={m}` itself; `tail=` has no kernel row.
    labelled_side = r"tail" if kernel else r"(?:cup|tail)"
    if "physical" in migrating or migrating_by_scope["picture"] & {
        "boundary",
        "west label",
        "east label",
        "north label",
        "south label",
        "bond label",
        "sandwich",
        "periodic",
    } or any(
        re.match(labelled_side + r"\s*=", value.lstrip("{").strip())
        for scope, key, value in options
        if scope == "picture"
        and key in {"west", "east", "north", "south"}
        and value is not None
    ):
        codes.add("C-policy")
    if migrating_by_scope["picture"] & {
        "lattice",
        "ring",
        "surface",
        "cluster",
        "planes",
    }:
        codes.add("C-frame")
    if any(
        re.search(rf"\\{name}\b", source)
        for name in SUGAR_COMMANDS
        if not (kernel and name in KERNEL_SUGAR_COMMANDS)
    ):
        codes.add("C-record")
    if re.search(r"\\tn\*", source):
        codes.add("C-record")
    if migrating_by_scope["atom"] & {
        "combined",
        "span",
        "up at",
        "down at",
        "west at",
        "east at",
        "up",
        "down",
    }:
        codes.add("C-record")
    if "role" in migrating:
        codes.add("C-species")
    if "species" in migrating_by_scope["setup"]:
        codes.add("C-declare")
    if re.search(r"\\tndeclareatom\b", source):
        codes.add("C-declare")
    if re.search(r"\\tenkzkernel\b", source):
        codes.add("C-switch")

    redraw = {code for code in codes if code.startswith("R-")}
    if redraw:
        return frozenset(codes)
    if codes:
        return frozenset(codes)
    return frozenset({"P-grid"})


def source_target_codes(source: str) -> frozenset[str]:
    """Derive exact migration targets, preserving mixed-construct workloads.

    The kernel is passed as reaching every construct: since the S4 surface
    swap the package binds the kernel surface at load.
    """
    source = normalized_environment_spacing(source)
    constructs = scan_inventory_constructs(source)
    codes: set[str] = set()
    masked = list(source)
    for construct in constructs:
        codes.update(
            fragment_target_codes(
                source[construct.start : construct.end],
                True,
            )
        )
        for index in range(construct.start, construct.end):
            if masked[index] != "\n":
                masked[index] = " "
    codes.update(fragment_target_codes("".join(masked), True))
    if any(not code.startswith("P-") for code in codes):
        codes = {code for code in codes if not code.startswith("P-")}
    elif "P-grid" in codes:
        codes.discard("P-none")
    return frozenset(codes)


def uses_tombstone(source: str) -> bool:
    """Return whether source uses a spelling tombstoned by LANGUAGE-1.0 §10."""
    return any(code.startswith("R-") for code in source_target_codes(source))


def target_disposition(codes: frozenset[str]) -> str:
    """Return the workload disposition implied by a target-code set."""
    if any(code.startswith("R-") for code in codes):
        return "redraw"
    if any(code.startswith("C-") for code in codes):
        return "codemod"
    return "preserve"


def section(text: str, heading: str, next_heading: str | None = None) -> str:
    try:
        result = text.split(heading, 1)[1]
    except IndexError:
        fail(f"missing document heading: {heading}")
    if next_heading is not None:
        result = result.split(next_heading, 1)[0]
    return result


def parse_counter_table(text: str, heading: str) -> tuple[Counter[str], int]:
    result: Counter[str] = Counter()
    total: int | None = None
    started = False
    for row in section(text, heading).splitlines():
        if started and not row.strip():
            break
        match = re.match(r"\| `?([^|`]+?)`? \| \**([0-9]+)\** \|$", row)
        started |= bool(match)
        label = match.group(1).strip().strip("*") if match else ""
        if match and label.lower() == "total":
            total = int(match.group(2))
        elif match:
            result[label] = int(match.group(2))
    if not result:
        fail(f"could not parse counter table below {heading}")
    if total is None or total != sum(result.values()):
        fail(f"invalid total below {heading}: {total} != {sum(result.values())}")
    return result, total


def parse_fixture_table(text: str) -> tuple[Counter[str], int]:
    body = section(text, "| Disposition | Fixtures |")
    body = body.split("\n\n", 1)[0]
    files: Counter[str] = Counter()
    total: int | None = None
    for row in body.splitlines():
        match = re.match(r"\| ([a-z]+) \| ([0-9]+) \|$", row)
        if match and match.group(1) in DISPOSITIONS:
            files[match.group(1)] = int(match.group(2))
        total_match = re.match(r"\| \*\*Total\*\* \| \*\*([0-9]+)\*\* \|$", row)
        if total_match:
            total = int(total_match.group(1))
    # Since the S4 surface swap every codemod and redraw fixture has left the
    # corpus, so the table may carry the preserve row alone.
    if not files or set(files) - set(DISPOSITIONS):
        fail("could not parse standalone fixture reconciliation table")
    if total is None or total != sum(files.values()):
        fail(f"invalid standalone fixture total: {total} != {sum(files.values())}")
    return files, total


def documented_blueprint(
    text: str,
) -> tuple[
    Counter[tuple[str, int, str]],
    Counter[str],
    dict[tuple[str, int, str], str],
    dict[tuple[str, int, str], frozenset[str]],
]:
    body = section(text, "## Blueprint inventory", "### Blueprint reconciliation")
    listed: Counter[tuple[str, int, str]] = Counter()
    dispositions: Counter[str] = Counter()
    disposition_by_occurrence: dict[tuple[str, int, str], str] = {}
    targets_by_occurrence: dict[tuple[str, int, str], frozenset[str]] = {}
    for row in body.splitlines():
        cells = [cell.strip() for cell in row.split("|")[1:-1]]
        if len(cells) != 4 or not re.fullmatch(r"`[^`]+\.tex`", cells[0]):
            continue
        filename = cells[0].strip("`")
        for disposition, cell in zip(DISPOSITIONS, cells[1:]):
            for use in re.finditer(
                r"L([0-9]+(?:, [0-9]+)*) `([^`]+)` → `([^`]+)`",
                cell,
            ):
                for line in map(int, use.group(1).split(", ")):
                    key = (filename, line, use.group(2))
                    listed[key] += 1
                    dispositions[disposition] += 1
                    disposition_by_occurrence[key] = disposition
                    targets_by_occurrence[key] = frozenset(
                        use.group(3).split("+")
                    )
    return (
        listed,
        dispositions,
        disposition_by_occurrence,
        targets_by_occurrence,
    )


def documented_fixtures(text: str) -> dict[str, tuple[str, frozenset[str]]]:
    result: dict[str, tuple[str, frozenset[str]]] = {}
    target_codes = set(re.findall(r"^\| `([PCR]-[^`]+)` \|", text, re.MULTILINE))
    for disposition in DISPOSITIONS:
        heading = rf"### {disposition.capitalize()} fixtures \(([0-9]+)\)\n"
        ending = r"(?=\n### |\nThe preserved list|\n\nThree corrections)"
        match = re.search(
            heading + r"(.*?)" + ending,
            text,
            flags=re.DOTALL,
        )
        if not match:
            # Since the S4 surface swap the codemod and redraw groups are
            # empty and their lists have left the document.
            if disposition in ("codemod", "redraw"):
                continue
            fail(f"missing {disposition} fixture list")
        names: list[str] = []
        for row in match.group(2).splitlines():
            item = re.match(r"- `([^`]+)`: (.+)", row)
            if not item:
                continue
            codes = frozenset(item.group(1).split("+"))
            unknown = codes - target_codes
            if unknown:
                fail(f"unknown target codes for {disposition}: {sorted(unknown)}")
            if disposition == "preserve" and any(not code.startswith("P-") for code in codes):
                fail(f"non-preserve target in preserve fixture group: {sorted(codes)}")
            if disposition == "codemod" and (
                not any(code.startswith("C-") for code in codes)
                or any(code.startswith("R-") for code in codes)
            ):
                fail(f"invalid codemod target set: {sorted(codes)}")
            if disposition == "redraw" and not any(
                code.startswith("R-") for code in codes
            ):
                fail(f"redraw target set lacks a redraw code: {sorted(codes)}")
            row_names = re.findall(r"`([^`]+\.tex)`", item.group(2))
            names.extend(row_names)
            for name in row_names:
                if name in result:
                    fail(f"fixture is listed more than once: {name}")
                result[name] = (disposition, codes)
        if len(names) != int(match.group(1)):
            fail(
                f"{disposition} heading says {match.group(1)} fixtures, "
                f"but lists {len(names)}"
            )
    return result


def main() -> int:
    text = DOCUMENT.read_text()

    blueprint_occurrences: Counter[tuple[str, int, str]] = Counter()
    blueprint_raw: Counter[str] = Counter()
    blueprint_sources: dict[tuple[str, int, str], list[tuple[str, bool]]] = {}
    for path in sorted(BLUEPRINT_ROOT.glob("*.tex")):
        blueprint_sources.update(construct_sources(path))
        for line, name in occurrences(path):
            blueprint_occurrences[(path.name, line, name)] += 1
            blueprint_raw[name] += 1

    (
        listed_blueprint,
        blueprint_dispositions,
        blueprint_occurrence_dispositions,
        blueprint_occurrence_targets,
    ) = documented_blueprint(text)
    if blueprint_occurrences != listed_blueprint:
        fail(
            "blueprint inventory mismatch: "
            f"missing={blueprint_occurrences - listed_blueprint}, "
            f"extra={listed_blueprint - blueprint_occurrences}"
        )
    documented_blueprint_raw, blueprint_total = parse_counter_table(
        text, "| Raw construct | Occurrences |"
    )
    if blueprint_raw != documented_blueprint_raw:
        fail("blueprint raw-count table does not match the source inventory")
    documented_blueprint_dispositions, disposition_total = parse_counter_table(
        text, "| Disposition | Occurrences |"
    )
    if blueprint_dispositions != documented_blueprint_dispositions:
        fail("blueprint disposition totals do not match the line inventory")
    if blueprint_total != disposition_total:
        fail("blueprint reconciliation tables have different totals")
    for key, documented_disposition in blueprint_occurrence_dispositions.items():
        actual_targets = frozenset().union(
            *(
                fragment_target_codes(source, kernel)
                for source, kernel in blueprint_sources[key]
            )
        )
        if actual_targets != blueprint_occurrence_targets[key]:
            fail(
                f"{key[0]}:{key[1]} {key[2]} target mismatch: "
                f"documented={sorted(blueprint_occurrence_targets[key])}, "
                f"actual={sorted(actual_targets)}"
            )
        actual_disposition = target_disposition(actual_targets)
        if actual_disposition != documented_disposition:
            fail(
                f"{key[0]}:{key[1]} {key[2]} disposition mismatch: "
                f"documented={documented_disposition}, actual={actual_disposition}"
            )

    fixtures = documented_fixtures(text)
    expected_fixtures = {path.name for path in FIXTURE_ROOT.glob("*.tex")}
    if set(fixtures) != expected_fixtures:
        fail(
            "fixture inventory mismatch: "
            f"missing={sorted(expected_fixtures - set(fixtures))}, "
            f"extra={sorted(set(fixtures) - expected_fixtures)}"
        )

    fixture_raw: Counter[str] = Counter()
    fixture_files: Counter[str] = Counter(
        disposition for disposition, _ in fixtures.values()
    )
    environment_files = 0
    command_only_files = 0
    setup_only_files = 0
    no_surface_files = 0
    for path in sorted(FIXTURE_ROOT.glob("*.tex")):
        uses = occurrences(path)
        names = Counter(name for _, name in uses)
        fixture_raw.update(names)
        expanded = expanded_source(path)
        expanded_names = [
            match.group(1)
            for pattern in (ENVIRONMENT, COMMAND)
            for match in pattern.finditer(expanded)
        ]
        has_environment = any(name.startswith("tenkz") for name in expanded_names)
        has_command = any(name in {"tnpic", "tntree"} for name in expanded_names)
        has_setup = SETUP_COMMAND.search(expanded) is not None
        environment_files += has_environment
        command_only_files += has_command and not has_environment
        setup_only_files += has_setup and not has_environment and not has_command
        no_surface_files += not has_environment and not has_command and not has_setup
        disposition, _ = fixtures[path.name]
        _, documented_targets = fixtures[path.name]
        actual_targets = source_target_codes(expanded)
        if actual_targets != documented_targets:
            fail(
                f"{path.name} target mismatch: "
                f"documented={sorted(documented_targets)}, "
                f"actual={sorted(actual_targets)}"
            )
        actual_disposition = target_disposition(actual_targets)
        if actual_disposition != disposition:
            fail(
                f"{path.name} disposition mismatch: "
                f"documented={disposition}, actual={actual_disposition}"
            )

    documented_files, _fixture_total = parse_fixture_table(text)
    if fixture_files != documented_files:
        fail("fixture disposition totals do not match the fixture lists")
    fixture_heading = "### Fixture raw-count reconciliation"
    documented_fixture_raw, _fixture_raw_total = parse_counter_table(
        text, fixture_heading
    )
    if fixture_raw != documented_fixture_raw:
        fail("fixture raw-count table does not match the source inventory")

    census = re.search(
        r"Of the ([0-9]+) top-level fixtures, ([0-9]+) open the \(kernel\) "
        r"tenkz environment and ([0-9]+)\n"
        r"contain no tenkz public-surface construct\.",
        text,
    )
    actual_census = (
        len(expected_fixtures),
        environment_files,
        no_surface_files,
    )
    if command_only_files or setup_only_files:
        fail(
            "fixture consumer census has command-only or setup-only "
            f"consumers the document does not state: {command_only_files}, "
            f"{setup_only_files}"
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
