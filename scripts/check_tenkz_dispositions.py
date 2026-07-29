#!/usr/bin/env python3
"""Verify that the tenkz migration ledger matches the tracked TeX sources."""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from tenkzlib.texcase import scan_constructs, strip_comments


DOCUMENT = ROOT / "docs/tenkz/DISPOSITIONS.md"
BLUEPRINT_ROOT = ROOT / "blueprint/src/chapter"
FIXTURE_ROOT = ROOT / "tests/tenkz"
ENVIRONMENT = re.compile(
    r"\\begin\s*\{\s*(tenkz(?:eq|free|cd|lattice|planes)?)\s*\}"
)
COMMAND = re.compile(r"\\(tnpic|tntree)\b")
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
)
SUGAR_COMMANDS = (
    "tnX",
    "tnbond",
    "tnstring",
    "tnfuse",
    "tnspan",
    "tndots",
    "tnskip",
    "tndeclareatom",
)


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
    """Normalize TeX whitespace that the shared construct scanner omits."""
    source = re.sub(r"\\begin\s+\{", r"\\begin{", source)
    return re.sub(r"\\end\s+\{", r"\\end{", source)


def construct_sources(path: Path) -> dict[tuple[str, int, str], list[str]]:
    """Return source slices for each picture construct in a TeX file."""
    source = normalized_environment_spacing(
        strip_comments(path.read_text(errors="replace"))
    )
    result: dict[tuple[str, int, str], list[str]] = defaultdict(list)
    for construct in scan_constructs(source):
        key = (path.name, construct.line, construct.name)
        result[key].append(source[construct.start : construct.end])
    for match in re.finditer(r"\\tntree\b[^\n]*", source):
        line = source.count("\n", 0, match.start()) + 1
        result[(path.name, line, "tntree")].append(match.group(0))
    return result


def expanded_source(path: Path, stack: tuple[Path, ...] = ()) -> str:
    """Expand local input files so fixture disposition includes dependencies."""
    if path in stack:
        fail(f"recursive fixture input: {' -> '.join(map(str, stack + (path,)))}")
    source = strip_comments(path.read_text(errors="replace"))

    def replace(match: re.Match[str]) -> str:
        dependency = path.parent / (match.group(1) or match.group(2))
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


def fragment_target_codes(source: str) -> frozenset[str]:
    """Classify one construct or construct-free source fragment."""
    public_commands = (
        "tn",
        "tnwire",
        "tnmark",
        "tngroup",
        "tnset",
        "tndeclare",
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

    dead_record = any(re.search(rf"\\{name}\b", source) for name in DEAD_COMMANDS)
    dead_record |= any(
        re.search(r"(?<![A-Za-z])" + re.escape(key) + r"\s*=", source)
        for key in DEAD_KEYS
    )
    dead_patterns = (
        r"(?<![A-Za-z])(?:inline|compact|fused)(?=\s*[,}\]])",
        r"route\s*=\s*(?:\{\s*)?(?:hv|vh|curve|drop|hug)\b",
        r"frame\s*=\s*(?:\{\s*)?(?:vertical\b|rotate\s*=)",
        r"frame\s*=\s*(?:\{\s*)?matrix\s*=",
        r"rows\s*=\s*\{[^}\n]*:[^}\n]*\}",
        r"\\tnfuse\s*\[[^\]]*\brows\s*=",
        r"form\s*=\s*(?:brace-(?:below|above)|cut|band|prose)\b",
        r"\\tnspan\s*\[[^\]]*\bbrace\s+(?:below|above)\b",
        r"skin\s*=\s*(?:cluster|enclosure)\b",
        r"weight\s*=\s*string\b",
        r"\([^)]+\)\s*-\s*\([^)]+\)",
        r"\bleg\s+(?:north|south|east|west)\s+of\b",
        r"\b(?:north|south|east|west)\s+outside\b",
        r"(?:^|,)\s*none(?=\s*(?:,|\]))",
    )
    dead_record |= any(re.search(pattern, source) for pattern in dead_patterns)

    for match in ENVIRONMENT.finditer(source):
        options = re.match(r"\s*\[([^\]]*)\]", source[match.end() :])
        if options and re.search(
            r"(?:^|,)\s*boundary\s+legs(?=\s*(?:,|$))",
            options.group(1),
        ):
            dead_record = True

    for match in re.finditer(r"\\tn\*?\s*\[([^\]]*)\]", source):
        if re.search(
            r"(?:^|,)\s*(?:pill|circle|boundary|removed|cluster|enclosure)"
            r"(?=\s*(?:,|$))"
            r"|(?:^|,)\s*tri\s*=",
            match.group(1),
        ):
            dead_record = True
        if re.search(
            r"(?:^|,)\s*(?:box|dot|mpo|ring|no legs)(?=\s*(?:,|$))",
            match.group(1),
        ):
            codes.add("C-record")
    if dead_record:
        codes.add("R-record")

    if COMMAND.search(source) and re.search(r"\\tnpic\b", source):
        codes.add("C-picture")
    if re.search(r"\\tntree\b", source):
        codes.add("C-tree")
    policy_patterns = (
        r"(?<![A-Za-z])(?:physical|boundary|west label|east label|"
        r"north label|south label|bond label)\s*=",
        r"(?<![A-Za-z])(?:sandwich|periodic)(?=\s*[,}\]])",
        r"(?:west|east|north|south)\s*=\s*\{?\s*(?:cup|tail)\s*=",
    )
    if any(re.search(pattern, source) for pattern in policy_patterns):
        codes.add("C-policy")
    if re.search(
        r"(?<![A-Za-z])(?:lattice|ring|surface|cluster)\s*=|"
        r"(?<![A-Za-z])planes(?=\s*[,}\]])",
        source,
    ):
        codes.add("C-frame")
    if any(re.search(rf"\\{name}\b", source) for name in SUGAR_COMMANDS):
        codes.add("C-record")
    if re.search(r"\\tn\*", source):
        codes.add("C-record")
    if re.search(
        r"(?<![A-Za-z])(?:combined|span|up at|down at|west at|east at|"
        r"up|down)\s*=",
        source,
    ):
        codes.add("C-record")
    if re.search(r"(?<![A-Za-z])role\s*=", source):
        codes.add("C-species")
    if re.search(r"\\tnset\s*\{[^}]*\bspecies\s*=", source):
        codes.add("C-declare")

    redraw = {code for code in codes if code.startswith("R-")}
    if redraw:
        return frozenset(codes)
    if codes:
        return frozenset(codes)
    return frozenset({"P-grid"})


def source_target_codes(source: str) -> frozenset[str]:
    """Derive exact migration targets, preserving mixed-construct workloads."""
    source = normalized_environment_spacing(source)
    constructs = scan_constructs(source)
    codes: set[str] = set()
    masked = list(source)
    for construct in constructs:
        codes.update(fragment_target_codes(source[construct.start : construct.end]))
        for index in range(construct.start, construct.end):
            if masked[index] != "\n":
                masked[index] = " "
    for match in re.finditer(r"\\tntree\b[^\n]*", source):
        codes.update(fragment_target_codes(match.group(0)))
        for index in range(match.start(), match.end()):
            masked[index] = " "
    codes.update(fragment_target_codes("".join(masked)))
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
    if set(files) != set(DISPOSITIONS):
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
        ending = r"(?=\n### |\nThe preserved list)"
        match = re.search(
            heading + r"(.*?)" + ending,
            text,
            flags=re.DOTALL,
        )
        if not match:
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
    blueprint_sources: dict[tuple[str, int, str], list[str]] = {}
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
            *(fragment_target_codes(source) for source in blueprint_sources[key])
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
        has_setup = re.search(r"\\(?:tnset|tndeclare)\b", expanded) is not None
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
        r"Of the ([0-9]+) top-level fixtures, ([0-9]+) directly or indirectly "
        r"open a tenkz\n"
        r"environment, ([0-9]+) are picture-command-only consumers, ([0-9]+) "
        r"are setup-only\n"
        r"consumers, and ([0-9]+) contain no tenkz public-surface construct\.",
        text,
    )
    actual_census = (
        len(expected_fixtures),
        environment_files,
        command_only_files,
        setup_only_files,
        no_surface_files,
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
