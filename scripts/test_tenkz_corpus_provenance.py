#!/usr/bin/env python3
"""Regression checks for independent tenkz corpus metadata invariants."""

from __future__ import annotations

import csv
import dataclasses
import os
import re
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

import tenkz_rmp
from tenkz_audit import Audit
from tenkz_rmp import (
    AUTHOR_SOURCE_HASHES,
    DEFAULT_MANIFEST,
    DEFAULT_VERDICT,
    RMPError,
    event_signatures,
    ink_environment_problems,
    load_author_source_hashes,
    load_manifest,
    rendered_ink_environment_families,
    sha256,
    structural_capability_problems,
    verify_author_source_tree,
)
from tenkzlib.dimensions import (
    BOOK_LAYOUT_ALLOWLIST,
    DimensionOccurrence,
    DimensionOwner,
    DimensionOwnershipError,
    DimensionReport,
    _COMMAND_GRAMMARS,
    _PUBLIC_ENVIRONMENTS,
    _environment_spans,
    collect_dimension_report,
    scan_book_dimensions,
    scan_case_dimensions,
    validate_dimension_report,
)
from tenkzlib.texcase import strip_comments
from tenkzlib.tnlog import parse_log


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts" / "tenkz_corpus.sh"
PROVENANCE = ROOT / "tests" / "tenkz" / "PROVENANCE.tsv"


def write_rows(path: Path, rows: list[list[str]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as stream:
        csv.writer(stream, dialect="excel-tab", lineterminator="\n").writerows(rows)


def validate(path: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["TENKZ_CORPUS_PROVENANCE"] = str(path)
    env["TENKZ_CORPUS_VALIDATE_ONLY"] = "1"
    return subprocess.run(
        ["bash", str(DRIVER)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )


def test_kernel_capability_owner() -> None:
    kernel_body = r"\tenkzkernel{\begin{tenkz} A \end{tenkz}}"
    if structural_capability_problems("good", ("kernel",), kernel_body):
        raise AssertionError("exclusive kernel owner tag was rejected")

    missing = structural_capability_problems("missing", ("grid",), kernel_body)
    if not any("capability 'kernel' is missing" in problem for problem in missing):
        raise AssertionError("nested grid tag hid a missing kernel owner tag")
    if not any("exclusive owner tag 'kernel'" in problem for problem in missing):
        raise AssertionError("kernel picture retained the nested grid tag")

    mixed = structural_capability_problems(
        "mixed", ("kernel", "grid"), kernel_body
    )
    if not any("exclusive owner tag 'kernel'" in problem for problem in mixed):
        raise AssertionError("kernel picture accepted both structural owner tags")

    bare_grid = r"\begin{tenkz} A \end{tenkz}"
    if structural_capability_problems("grid", ("grid",), bare_grid):
        raise AssertionError("bare grid owner tag was rejected")


def test_ink_environment_owner() -> None:
    log = "\n".join(
        (
            "picture|id=1|lang=grid",
            "picture|id=2|lang=cd",
            "picture|id=3|lang=free",
            "picture|id=4|lang=lattice",
            "picture|id=5|lang=lattice",
            "surface|picture=5|name=tenkzplanes",
            "picture|id=k1|lang=kernel",
            "tree|picture=0|id=1|style=wire|leaves=2|vertices=1|"
            "topology=(1,2)|role=none|species=none",
            "",
        )
    )
    parsed = parse_log(log, source_name="ink-owner-test.tnlog")
    used = rendered_ink_environment_families(parsed)
    expected = {
        "tenkz",
        "tenkzcd",
        "tenkzfree",
        "tenkzlattice",
        "tenkzplanes",
        "kernel",
    }
    if used != expected:
        raise AssertionError(f"compiled Ink owners disagree: {used!r}")
    malformed: list[tuple[str, str, str]] = []
    rejected = parse_log(
        "picture|id=1|id=2|lang=grid\n"
        "kernel-boundary|picture=1|signature=a|signature=b\n",
        source_name="invalid-owner-test.tnlog",
        hard=lambda *finding: malformed.append(finding),
    )
    if not malformed or rejected.valid_events:
        raise AssertionError("invalid records escaped canonical quarantine")
    if rendered_ink_environment_families(rejected):
        raise AssertionError("invalid picture changed compiled Ink ownership")
    if event_signatures(rejected) != ("model-events|none",):
        raise AssertionError("invalid boundary changed compiled event signatures")
    with tempfile.TemporaryDirectory(prefix="tenkz-ink-owner-") as tmp:
        log_path = Path(tmp) / "ink-owner-test.tnlog"
        log_path.write_text(log, encoding="utf-8")
        audit = Audit(log_path, None)
        audit.parse_log()
        audit.check_dialects()
        mismatches = [
            finding for finding in audit.findings
            if finding.rule == "dialect-mismatch"
        ]
        if mismatches:
            raise AssertionError(
                "compiled Ink owner metadata was foreign to its picture dialect: "
                + "; ".join(finding.msg for finding in mismatches)
            )
    ink = (
        "Canonical tenkz, tenkzcd, tenkzfree, tenkzlattice, tenkzplanes, "
        "and kernel."
    )
    if ink_environment_problems("good", ink, used):
        raise AssertionError("accurate compiled Ink owners were rejected")
    cd_only = parse_log(
        "picture|id=1|lang=cd\n", source_name="ink-cd-owner-test.tnlog"
    )
    cd_used = rendered_ink_environment_families(cd_only)
    if cd_used != {"tenkzcd"}:
        raise AssertionError(f"tenkzcd was collapsed into another owner: {cd_used!r}")
    cd_mismatch = ink_environment_problems(
        "cd-as-tenkz", "Canonical public tenkz environment.", cd_used
    )
    if not (
        any("Ink names tenkz" in problem for problem in cd_mismatch)
        and any("uses tenkzcd" in problem for problem in cd_mismatch)
    ):
        raise AssertionError("plain tenkz Ink was accepted for a tenkzcd picture")
    tree_only = parse_log(
        "tree|picture=0|id=1|style=wire|leaves=2|vertices=1|"
        "topology=(1,2)|role=none|species=none\n",
        source_name="ink-tree-owner-test.tnlog",
    )
    tree_used = rendered_ink_environment_families(tree_only)
    if tree_used != {"tenkz"}:
        raise AssertionError(f"standalone tree lost its tenkz owner: {tree_used!r}")
    cd_tree = parse_log(
        "picture|id=1|lang=cd\n"
        "tree|picture=1|id=1|style=wire|leaves=2|vertices=1|"
        "topology=(1,2)|role=none|species=none\n",
        source_name="ink-cd-tree-owner-test.tnlog",
    )
    cd_tree_used = rendered_ink_environment_families(cd_tree)
    if cd_tree_used != {"tenkzcd"}:
        raise AssertionError(
            f"tree inside tenkzcd gained a second owner: {cd_tree_used!r}"
        )
    mismatch = ink_environment_problems(
        "wrong", "Canonical tenkzfree environment.", {"kernel"}
    )
    if not any("Ink names tenkzfree" in problem for problem in mismatch):
        raise AssertionError("stale Ink family was accepted")
    if not any("uses kernel but Ink does not name" in problem for problem in mismatch):
        raise AssertionError("compiled kernel owner was omitted")


def _expect_dimension_failure(report: DimensionReport, phrase: str) -> None:
    try:
        validate_dimension_report(report)
    except DimensionOwnershipError as exc:
        if phrase not in str(exc):
            raise AssertionError(
                f"dimension mutation produced the wrong failure: {exc}"
            ) from exc
    else:
        raise AssertionError(f"dimension mutation escaped the {phrase!r} ratchet")


def test_rmp_dimension_ownership() -> None:
    registry_source = (
        ROOT / "tex" / "tenkz" / "tenkz-language-registry.tex"
    ).read_text(encoding="utf-8")
    registry = strip_comments(
        registry_source
        + "\n% \\__tenkz_language_registry_command:nnnnn "
        "{commentedcommand}\n"
        + "% \\__tenkz_language_registry_environment:nnnn "
        "{commentedenvironment}\n"
    )
    registered_commands = set(
        re.findall(
            r"__tenkz_language_registry_command:nnnnn \{([^}]+)\}",
            registry,
        )
    )
    if registered_commands != set(_COMMAND_GRAMMARS):
        raise AssertionError(
            "dimension barriers disagree with the public command registry: "
            f"registry-only={sorted(registered_commands - set(_COMMAND_GRAMMARS))!r}, "
            f"scanner-only={sorted(set(_COMMAND_GRAMMARS) - registered_commands)!r}"
        )
    registered_environments = set(
        re.findall(
            r"__tenkz_language_registry_environment:nnnn \{([^}]+)\}",
            registry,
        )
    )
    if registered_environments != set(_PUBLIC_ENVIRONMENTS):
        raise AssertionError(
            "dimension barriers disagree with the public environment registry: "
            f"registry-only="
            f"{sorted(registered_environments - set(_PUBLIC_ENVIRONMENTS))!r}, "
            f"scanner-only="
            f"{sorted(set(_PUBLIC_ENVIRONMENTS) - registered_environments)!r}"
        )
    targets = load_manifest(DEFAULT_MANIFEST)
    report = collect_dimension_report(ROOT, (target.case for target in targets))
    expected = Counter(
        {
            DimensionOwner.METRIC: 0,
            DimensionOwner.FRAME: 0,
            DimensionOwner.ROUTE: 396,
            DimensionOwner.LAYOUT: 530,
        }
    )
    if report.case_count != 926 or report.case_counts != expected:
        raise AssertionError(
            "RMP dimension ownership baseline drifted: "
            f"total={report.case_count}, owners={report.case_counts!r}"
        )
    if report.comment_count:
        raise AssertionError("RMP case comments regained physical dimensions")
    if report.book_counts != Counter(BOOK_LAYOUT_ALLOWLIST):
        raise AssertionError(
            f"benchmark-book dimension allowlist drifted: {report.book_counts!r}"
        )
    validate_dimension_report(report)

    synthetic = r"""% pitch=14mm remains visible to the comment audit
\begin{tenkz}[pitch=11mm]
  \tnput{a}{(1mm,2mm)}{}
  \tnjoin[via={(3mm,4mm)}]{a}{5mm,6mm}
\end{tenkz}
\begin{tenkzlattice}[sheet vector={0mm,2.5mm}]\end{tenkzlattice}
"""
    occurrences = scan_case_dimensions(Path("synthetic.tex"), synthetic)
    synthetic_counts = Counter(
        occurrence.owner for occurrence in occurrences if not occurrence.in_comment
    )
    if synthetic_counts != Counter(
        {
            DimensionOwner.METRIC: 1,
            DimensionOwner.FRAME: 2,
            DimensionOwner.ROUTE: 4,
            DimensionOwner.LAYOUT: 2,
        }
    ):
        raise AssertionError(
            f"balanced dimension classification failed: {synthetic_counts!r}"
        )
    if sum(occurrence.in_comment for occurrence in occurrences) != 1:
        raise AssertionError("comment dimensions were not counted orthogonally")

    absolute_units = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnput{x}{(1 in, 1truept, 1 true pt, 1 true in)}{}",
    )
    if len(absolute_units) != 4 or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in absolute_units
    ):
        raise AssertionError(
            f"spaced/true absolute dimensions escaped: {absolute_units!r}"
        )
    command_adjacent_units = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnput{x}{(\kern1mm,1MM,1Mm,\kern1mmfoo)}{}",
    )
    if [occurrence.literal for occurrence in command_adjacent_units] != [
        "1mm",
        "1MM",
        "1Mm",
        "1mm",
    ] or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in command_adjacent_units
    ):
        raise AssertionError(
            "command-adjacent/mixed-case dimensions escaped: "
            f"{command_adjacent_units!r}"
        )
    starred_command_units = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow*[from=1,to=2]{\rule{1mm}{2pt}}",
    )
    if [occurrence.literal for occurrence in starred_command_units] != [
        "1mm",
        "2pt",
    ] or any(
        occurrence.owner is not DimensionOwner.ROUTE
        for occurrence in starred_command_units
    ):
        raise AssertionError(
            f"starred command dimensions escaped: {starred_command_units!r}"
        )
    command_arity_cases = (
        (
            r"\tnput{a}{(3mm,0)}{\rule{4pt}{5pt}}{\hspace{6mm}}",
            DimensionOwner.LAYOUT,
            ("3mm", "4pt", "5pt"),
            "6mm",
        ),
        (
            r"\tnjoin[label={\rule{11pt}{12pt}}]{0mm,0}{13mm,0}"
            r"{\hspace{14mm}}",
            DimensionOwner.ROUTE,
            ("11pt", "12pt", "0mm", "13mm"),
            "14mm",
        ),
        (
            r"\tnwire{A.e}{B.w}{\hspace{22mm}}",
            DimensionOwner.ROUTE,
            (),
            "22mm",
        ),
        (
            r"\tnedge[label={\rule{31pt}{32pt}}]{(1,1)-(1,2)}"
            r"{\hspace{33mm}}",
            DimensionOwner.ROUTE,
            ("31pt", "32pt"),
            "33mm",
        ),
        (
            r"\tnarrow[from=1,to=2]{\rule{41pt}{42pt}}{\hspace{43mm}}",
            DimensionOwner.ROUTE,
            ("41pt", "42pt"),
            "43mm",
        ),
        (
            r"\tnarrow*[from=1,to=2]{\rule{51pt}{52pt}}{\hspace{53mm}}",
            DimensionOwner.ROUTE,
            ("51pt", "52pt"),
            "53mm",
        ),
        (
            r"\tnpic{\rule{61pt}{62pt}}{\hspace{63mm}}",
            None,
            ("61pt", "62pt"),
            "63mm",
        ),
        (
            r"\tntree{{\rule{71pt}{72pt}}}{\hspace{73mm}}",
            None,
            ("71pt", "72pt"),
            "73mm",
        ),
    )
    for source, owner, owned_literals, independent_literal in command_arity_cases:
        occurrences = scan_case_dimensions(Path("synthetic.tex"), source)
        actual = tuple(
            (occurrence.literal, occurrence.owner) for occurrence in occurrences
        )
        expected = (
            *((literal, owner) for literal in owned_literals),
            (independent_literal, None),
        )
        if actual != expected:
            raise AssertionError(
                "a command swallowed an independent following TeX group: "
                f"source={source!r}, occurrences={occurrences!r}"
            )
    escaped_command_units = scan_case_dimensions(
        Path("synthetic.tex"), r"\\tnput{x}{(1mm,0)}{}"
    )
    if (
        len(escaped_command_units) != 1
        or escaped_command_units[0].owner is not None
    ):
        raise AssertionError(
            "an escaped command spelling gained dimension ownership: "
            f"{escaped_command_units!r}"
        )
    active_after_escape_units = scan_case_dimensions(
        Path("synthetic.tex"), r"\\\tnput{x}{(2mm,0)}{}"
    )
    if (
        len(active_after_escape_units) != 1
        or active_after_escape_units[0].owner is not DimensionOwner.LAYOUT
    ):
        raise AssertionError(
            "an active command after an escaped backslash lost ownership: "
            f"{active_after_escape_units!r}"
        )
    label_option_text = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnput{x}{(0,0)}{pitch=1mm, row vector={2mm,3mm}}",
    )
    if len(label_option_text) != 3 or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in label_option_text
    ):
        raise AssertionError(
            "option-like text inside a command label overrode its owner: "
            f"{label_option_text!r}"
        )
    setting_option = scan_case_dimensions(
        Path("synthetic.tex"), r"\tnset{physical=up, pitch=4mm}"
    )
    if (
        len(setting_option) != 1
        or setting_option[0].owner is not DimensionOwner.METRIC
    ):
        raise AssertionError(
            f"a tnset metric option lost ownership: {setting_option!r}"
        )
    nested_picture_option = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow[from=1,to=2]{\tnpic[pitch=5mm]{x}}",
    )
    if (
        len(nested_picture_option) != 1
        or nested_picture_option[0].owner is not DimensionOwner.METRIC
    ):
        raise AssertionError(
            "a nested tnpic metric option inherited command ownership: "
            f"{nested_picture_option!r}"
        )
    tree_option = scan_case_dimensions(
        Path("synthetic.tex"), r"\tntree[pitch=6mm]{a(b,c)}"
    )
    if len(tree_option) != 1 or tree_option[0].owner is not DimensionOwner.METRIC:
        raise AssertionError(f"a tntree metric option lost ownership: {tree_option!r}")
    public_example = ROOT / "tex" / "tenkz" / "examples" / "api" / "tnarrow.tex"
    public_example_dimensions = scan_case_dimensions(
        public_example.relative_to(ROOT), public_example.read_text(encoding="utf-8")
    )
    if (
        len(public_example_dimensions) != 1
        or public_example_dimensions[0].literal != "18mm"
        or public_example_dimensions[0].owner is not DimensionOwner.METRIC
    ):
        raise AssertionError(
            "the public tenkzcd polygon radius lost metric ownership: "
            f"{public_example_dimensions!r}"
        )
    physical_picture_options = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\begin{tenkzcd}[column sep=7mm,row sep=8mm]\end{tenkzcd}"
        r"\begin{tenkzlattice}[col vector={9mm,10mm},"
        r"row vector={11mm,12mm},sheet vector={13mm,14mm}]"
        r"\end{tenkzlattice}",
    )
    expected_picture_owners = (
        *((literal, DimensionOwner.METRIC) for literal in ("7mm", "8mm")),
        *((literal, DimensionOwner.FRAME) for literal in (
            "9mm", "10mm", "11mm", "12mm", "13mm", "14mm"
        )),
    )
    if tuple(
        (occurrence.literal, occurrence.owner)
        for occurrence in physical_picture_options
    ) != expected_picture_owners:
        raise AssertionError(
            "public physical picture keys lost their semantic owners: "
            f"{physical_picture_options!r}"
        )
    ratio_keys = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\begin{tenkzlattice}[plane rise=15mm,plane slant=16mm]"
        r"\end{tenkzlattice}",
    )
    if len(ratio_keys) != 2 or any(
        occurrence.owner is not None for occurrence in ratio_keys
    ):
        raise AssertionError(
            "dimensionless plane-ratio keys gained physical ownership: "
            f"{ratio_keys!r}"
        )
    direct_label_shift = scan_case_dimensions(
        Path("synthetic.tex"), r"\tn*[label shift={17mm,18mm}]{A}"
    )
    if len(direct_label_shift) != 2 or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in direct_label_shift
    ):
        raise AssertionError(
            "a public object label shift lost layout ownership: "
            f"{direct_label_shift!r}"
        )
    for command in ("tnX", "tnfuse"):
        object_label_shift = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\{command}[label shift={{17mm,18mm}}]{{A}}",
        )
        if len(object_label_shift) != 2 or any(
            occurrence.owner is not DimensionOwner.LAYOUT
            for occurrence in object_label_shift
        ):
            raise AssertionError(
                f"{command} label shift lost layout ownership: "
                f"{object_label_shift!r}"
            )
    for malformed_source, expected_count in (
        (r"\tnsite[label shift={23mm,24mm}]{(1,1)}", 2),
        (r"\tndots[label shift={25mm,26mm}]", 2),
        (r"\tnarrow[from=1,to=2]{\tn[pitch=27mm]{A}}", 1),
        (r"\tnpic[label shift={28mm,29mm}]{\tn{A}}", 2),
        (r"\tnset{radius=30mm}", 1),
        (r"\begin{tenkz}[radius=31mm]\end{tenkz}", 1),
        (r"\begin{tenkzcd}[col vector={32mm,33mm}]\end{tenkzcd}", 2),
    ):
        malformed_options = scan_case_dimensions(
            Path("synthetic.tex"), malformed_source
        )
        if len(malformed_options) != expected_count or any(
            occurrence.owner is not None for occurrence in malformed_options
        ):
            raise AssertionError(
                "a non-public physical option gained ownership: "
                f"source={malformed_source!r}, occurrences={malformed_options!r}"
            )
    unclosed_public_argument = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{x \tnpic[pitch=41mm \tnput{x}{(42mm,0)}{} "
        r"\rule{43mm}{44mm}}",
    )
    if len(unclosed_public_argument) != 4 or any(
        occurrence.owner is not None for occurrence in unclosed_public_argument
    ):
        raise AssertionError(
            "an unclosed public argument exposed dimensions to an enclosing owner: "
            f"{unclosed_public_argument!r}"
        )
    for malformed_nested_source in (
        r"\tnpic{51mm \tnput{x}{(52mm,0)}{}",
        r"\tndeclareatom{\tnmalformed}{skin=dot}"
        r"\tnmalformed[label shift=53mm \tnput{x}{(54mm,0)}{}",
    ):
        malformed_nested = scan_case_dimensions(
            Path("synthetic.tex"), malformed_nested_source
        )
        if len(malformed_nested) != 2 or any(
            occurrence.owner is not None for occurrence in malformed_nested
        ):
            raise AssertionError(
                "a malformed static or dynamic argument exposed nested ownership: "
                f"source={malformed_nested_source!r}, "
                f"occurrences={malformed_nested!r}"
            )
    environment_names = (
        ("static", "{tenkz}", "{tenkz}", "{tenkz ", ""),
        (
            "unresolved",
            r"{\tenname}",
            r"{\tenname}",
            r"{\tenname ",
            r"\def\tenname{tenkz}",
        ),
        ("parameterized", "{#1}", "{#1}", "{#1 ", ""),
        (
            "unresolved unbraced",
            r"\tenname",
            r"\tenname",
            None,
            r"\def\tenname{tenkz}",
        ),
        ("parameterized unbraced", "#1", "#1", None, ""),
    )
    owner_contexts = (
        (
            "route",
            r"\tnarrow{",
            "}",
            r"\tnput{x}{(DIM,0)}{}",
        ),
        (
            "layout",
            r"\tnput{x}{(0,0)}{",
            "}",
            r"\tnarrow{DIM}",
        ),
    )
    malformed_kinds = ("unclosed name", "unclosed option", "missing end")
    literal_index = 61
    for (
        name_kind,
        begin_argument,
        end_argument,
        unclosed_argument,
        prelude,
    ) in environment_names:
        for malformed_kind in malformed_kinds:
            if malformed_kind == "unclosed name" and unclosed_argument is None:
                continue
            for owner_kind, outer_open, outer_close, inner_template in owner_contexts:
                literal = f"{literal_index}mm"
                literal_index += 1
                inner_command = inner_template.replace("DIM", literal)
                if malformed_kind == "unclosed name":
                    environment = r"\begin" + unclosed_argument + inner_command
                    # Keep the name group genuinely unclosed; the outer owner
                    # is intentionally opened but cannot close across it.
                    suffix = ""
                elif malformed_kind == "unclosed option":
                    environment = (
                        r"\begin"
                        + begin_argument
                        + "[malformed "
                        + inner_command
                        + r"\end"
                        + end_argument
                    )
                    suffix = outer_close
                else:
                    environment = r"\begin" + begin_argument + inner_command
                    suffix = outer_close
                source = prelude + outer_open + environment + suffix
                owner_source = strip_comments(source)
                literal_offset = source.index(literal)
                environment_barriers = _environment_spans(source, owner_source)
                if not any(
                    span.is_quarantine
                    and span.start <= literal_offset < span.end
                    for span in environment_barriers
                ):
                    raise AssertionError(
                        "a malformed environment remainder lacked a quarantine: "
                        f"name={name_kind}, malformed={malformed_kind}, "
                        f"outer={owner_kind}, source={source!r}, "
                        f"spans={environment_barriers!r}"
                    )
                occurrences = scan_case_dimensions(Path("synthetic.tex"), source)
                if len(occurrences) != 1 or occurrences[0].owner is not None:
                    raise AssertionError(
                        "a malformed environment remainder exposed an owner: "
                        f"name={name_kind}, malformed={malformed_kind}, "
                        f"outer={owner_kind}, source={source!r}, "
                        f"occurrences={occurrences!r}"
                    )
    replacement_templates = (
        ("primitive", r"\def\x{TOKEN}"),
        ("latex", r"\newcommand{\x}{TOKEN}"),
        ("xparse", r"\NewDocumentCommand{\x}{}{TOKEN}"),
    )
    for definition_kind, definition_template in replacement_templates:
        inert_end = definition_template.replace("TOKEN", r"\end{tenkz}")
        for owner_kind, outer_open, outer_close, _ in owner_contexts:
            source = (
                outer_open
                + r"\begin{tenkz}"
                + inert_end
                + r"\rule{81mm}{82mm}\end{tenkz}"
                + outer_close
            )
            occurrences = scan_case_dimensions(Path("synthetic.tex"), source)
            if len(occurrences) != 2 or any(
                occurrence.owner is not None for occurrence in occurrences
            ):
                raise AssertionError(
                    "an inert replacement end token closed an environment: "
                    f"definition={definition_kind}, outer={owner_kind}, "
                    f"occurrences={occurrences!r}"
                )
        inert_begin = definition_template.replace("TOKEN", r"\begin{tenkz}")
        source = (
            r"\tnarrow{\begin{tenkz}\end{tenkz}"
            + inert_begin
            + r"\rule{83mm}{84mm}}"
        )
        occurrences = scan_case_dimensions(Path("synthetic.tex"), source)
        if len(occurrences) != 2 or any(
            occurrence.owner is not DimensionOwner.ROUTE
            for occurrence in occurrences
        ):
            raise AssertionError(
                "an inert replacement begin token opened an environment: "
                f"definition={definition_kind}, occurrences={occurrences!r}"
            )
    unclosed_environment_end = scan_case_dimensions(
        Path("synthetic.tex"), r"\end{tenkz \tnput{x}{(79mm,0)}{}"
    )
    if len(unclosed_environment_end) != 1 or unclosed_environment_end[0].owner is not None:
        raise AssertionError(
            "an unclosed environment end name exposed nested ownership: "
            f"{unclosed_environment_end!r}"
        )
    for case_variant in (
        r"\tnarrow{x \tnpic[PITCH=34mm]{y}}",
        r"\tnarrow{x \tn[Label Shift={35mm,36mm}]{A}}",
        r"\tnarrow{x \begin{tenkzlattice}[COL VECTOR={37mm,38mm}]"
        r"\end{tenkzlattice}}",
    ):
        case_sensitive_options = scan_case_dimensions(
            Path("synthetic.tex"), case_variant
        )
        if not case_sensitive_options or any(
            occurrence.owner is not None
            for occurrence in case_sensitive_options
        ):
            raise AssertionError(
                "a case-mismatched PGF key gained ownership: "
                f"source={case_variant!r}, "
                f"occurrences={case_sensitive_options!r}"
            )
    nested_setup = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{x \tnset{pitch=39mm,radius=40mm}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in nested_setup
    ] != [
        ("39mm", DimensionOwner.METRIC),
        ("40mm", None),
    ]:
        raise AssertionError(
            "a nested setup command leaked its enclosing owner: "
            f"{nested_setup!r}"
        )
    neutral_command_containers = (
        ("tn", r"\tn{\rule{41mm}{42mm}}"),
        ("tnX", r"\tnX{\rule{41mm}{42mm}}"),
        ("tnfuse", r"\tnfuse{\rule{41mm}{42mm}}"),
        ("tndots", r"\tndots[label shift={41mm,42mm}]"),
        ("tnghost", r"\tnghost{41mm}"),
        ("tnspan", r"\tnspan{2}{\rule{41mm}{42mm}}"),
        ("tncut", r"\tncut{\rule{41mm}{42mm}}"),
        ("tnregion", r"\tnregion[label={\rule{41mm}{42mm}}]{x}"),
        ("tnsite", r"\tnsite[label={\rule{41mm}{42mm}}]{(1,1)}"),
        ("tntree", r"\tntree{{\rule{41mm}{42mm}}}"),
        ("tnpic", r"\tnpic{\rule{41mm}{42mm}}"),
        ("tnset", r"\tnset{radius=41mm}"),
        ("tndeclareatom", r"\tndeclareatom{\foo}{bogus=41mm}"),
        ("tnmark", r"\tnmark[form=label]{x}{\rule{41mm}{42mm}}"),
        ("tngroup", r"\tngroup{\rule{41mm}{42mm}}"),
        ("tndeclare", r"\tndeclare{skin}{x}{bogus=41mm}"),
        ("tnbond", r"\tnbond{41mm}{x}"),
        ("tnprose", r"\tnprose{\rule{41mm}{42mm}}"),
    )
    for command, container in neutral_command_containers:
        nested_container = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tnarrow[from=1,to=2]{{{container}}}",
        )
        if not nested_container or any(
            occurrence.owner is not None for occurrence in nested_container
        ):
            raise AssertionError(
                f"a nested {command} container inherited route ownership: "
                f"{nested_container!r}"
            )
    declared_compatibility_atom = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnmyatom}{skin=dot}"
        r"\tnarrow{\tnmyatom[label shift={52mm,53mm}]"
        r"{\rule{54mm}{55mm}}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in declared_compatibility_atom
    ] != [
        ("52mm", None),
        ("53mm", None),
        ("54mm", None),
        ("55mm", None),
    ]:
        raise AssertionError(
            "a source-only compatibility declaration granted ownership: "
            f"{declared_compatibility_atom!r}"
        )
    unbraced_compatibility_atom = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\tndeclareatom\tnbareatom{skin=dot}"
        r"\tnbareatom[label shift={86mm,87mm}]{A}}",
    )
    if len(unbraced_compatibility_atom) != 2 or any(
        occurrence.owner is not None
        for occurrence in unbraced_compatibility_atom
    ):
        raise AssertionError(
            "an unbraced xparse declaration escaped quarantine: "
            f"{unbraced_compatibility_atom!r}"
        )
    unbraced_dynamic_label = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnfoo}{skin=dot}"
        r"\tnarrow{\tnfoo\tnput{x}{(121mm,0)}{}}",
    )
    if len(unbraced_dynamic_label) != 1 or any(
        occurrence.owner is not None for occurrence in unbraced_dynamic_label
    ):
        raise AssertionError(
            "an unbraced dynamic label reactivated a public command: "
            f"{unbraced_dynamic_label!r}"
        )
    later_dynamic_sibling = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnfoo}{skin=dot}"
        r"\tnarrow{\tnfoo A\tnput{x}{(122mm,0)}{}}",
    )
    if len(later_dynamic_sibling) != 1 or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in later_dynamic_sibling
    ):
        raise AssertionError(
            "a dynamic one-token label consumed a later sibling command: "
            f"{later_dynamic_sibling!r}"
        )
    grouped_dynamic_label = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnfoo}{skin=dot}"
        r"\tnarrow{\tnfoo{\tnput{x}{(123mm,0)}{}}}",
    )
    if len(grouped_dynamic_label) != 1 or any(
        occurrence.owner is not None for occurrence in grouped_dynamic_label
    ):
        raise AssertionError(
            "a grouped dynamic label reactivated a public command: "
            f"{grouped_dynamic_label!r}"
        )
    for catcode_prelude, atom_name in (
        (r"\makeatletter", "tn@atom"),
        (r"\ExplSyntaxOn", "tn:atom"),
        (r"\ExplSyntaxOn", "tn_atom"),
        ("", "tnλatom"),
        ("", "?"),
    ):
        catcode_atom = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"{catcode_prelude}\tndeclareatom{{\{atom_name}}}{{skin=dot}}"
            rf"\tnarrow{{\{atom_name}[label shift={{99mm,100mm}}]"
            r"{101mm}{102mm}}",
        )
        if len(catcode_atom) != 4 or any(
            occurrence.owner is not None for occurrence in catcode_atom
        ):
            raise AssertionError(
                "a control-sequence atom name escaped dynamic quarantine: "
                f"name={atom_name!r}, occurrences={catcode_atom!r}"
            )
    declared_kernel_atom = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclare{atom}{tnkernelatom}{skin=dot}"
        r"\tnarrow{\tnkernelatom[label shift={56mm,57mm}]"
        r"{\rule{58mm}{59mm}}}",
    )
    if len(declared_kernel_atom) != 4 or any(
        occurrence.owner is not None for occurrence in declared_kernel_atom
    ):
        raise AssertionError(
            "a declared kernel atom inherited route or compatibility keys: "
            f"{declared_kernel_atom!r}"
        )
    for invalid_descriptor in (
        "bogus=x",
        "skin=triangle",
        "ports={west:physical}",
        "skin=dot,ports={up:virtual}",
    ):
        rejected_compatibility_atom = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tnarrow{{\tndeclareatom{{\tninvalidatom}}"
            rf"{{{invalid_descriptor}}}"
            r"\tninvalidatom[label shift={80mm,81mm}]{A}}",
        )
        if len(rejected_compatibility_atom) != 2 or any(
            occurrence.owner is not None
            for occurrence in rejected_compatibility_atom
        ):
            raise AssertionError(
                "an invalid compatibility descriptor activated an atom: "
                f"descriptor={invalid_descriptor!r}, "
                f"occurrences={rejected_compatibility_atom!r}"
            )
    for opener, closer in (
        ("begingroup", "endgroup"),
        ("bgroup", "egroup"),
    ):
        digit_delimited_group = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\{opener}1\tndeclareatom{{\tngroupatom}}{{skin=dot}}"
            rf"\tngroupatom[label shift={{82mm,83mm}}]{{A}}\{closer}2"
            r"\tnarrow{\tngroupatom[label shift={84mm,85mm}]{B}}",
        )
        if [
            (occurrence.literal, occurrence.owner)
            for occurrence in digit_delimited_group
        ] != [
            ("82mm", None),
            ("83mm", None),
            ("84mm", None),
            ("85mm", None),
        ]:
            raise AssertionError(
                "a grouped dynamic declaration escaped quarantine: "
                f"opener={opener!r}, occurrences={digit_delimited_group!r}"
            )
    atom_before_declaration = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\tnlateatom[label shift={60mm,61mm}]{A}}"
        r"\tndeclareatom{\tnlateatom}{skin=dot}",
    )
    if len(atom_before_declaration) != 2 or any(
        occurrence.owner is not None for occurrence in atom_before_declaration
    ):
        raise AssertionError(
            "a dynamic atom gained ownership before its declaration: "
            f"{atom_before_declaration!r}"
        )
    colliding_atom_declaration = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnjoin}{skin=dot}"
        r"\tnjoin[label shift={62mm,63mm}]{a}{b}",
    )
    if len(colliding_atom_declaration) != 2 or any(
        occurrence.owner is not DimensionOwner.ROUTE
        for occurrence in colliding_atom_declaration
    ):
        raise AssertionError(
            "a rejected declaration changed a fixed public command owner: "
            f"{colliding_atom_declaration!r}"
        )
    colliding_latex_declaration = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\tndeclareatom\rule{skin=dot}"
        r"\rule[label shift={88mm,89mm}]{95mm}{96mm}}",
    )
    if len(colliding_latex_declaration) != 4 or any(
        occurrence.owner is not None
        for occurrence in colliding_latex_declaration
    ):
        raise AssertionError(
            "a format command collision activated dynamic ownership: "
            f"{colliding_latex_declaration!r}"
        )
    source_local_collision = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\newcommand{\tnoccupied}[2][]{A}"
        r"\tnarrow{\tndeclareatom{\tnoccupied}{skin=dot}"
        r"\tnoccupied[label shift={93mm,94mm}]{97mm}{98mm}}",
    )
    if len(source_local_collision) != 4 or any(
        occurrence.owner is not None for occurrence in source_local_collision
    ):
        raise AssertionError(
            "a source-local command collision activated dynamic ownership: "
            f"{source_local_collision!r}"
        )
    repeated_optional_collision = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\NewDocumentCommand{\tnoccupied}{O{} O{} m}{}"
        r"\tnarrow{\tndeclareatom{\tnoccupied}{skin=dot}"
        r"\tnoccupied[][103mm]{104mm}}",
    )
    if len(repeated_optional_collision) != 2 or any(
        occurrence.owner is not None
        for occurrence in repeated_optional_collision
    ):
        raise AssertionError(
            "a repeated optional argument escaped unknown-arity quarantine: "
            f"{repeated_optional_collision!r}"
        )
    colliding_parbox = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\tndeclareatom{\parbox}{skin=dot}"
        r"\parbox[c][105mm][c]{106mm}{x}}",
    )
    if len(colliding_parbox) != 2 or any(
        occurrence.owner is not None for occurrence in colliding_parbox
    ):
        raise AssertionError(
            "a real multi-option command escaped unknown-arity quarantine: "
            f"{colliding_parbox!r}"
        )
    scoped_atom_declaration = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{{\tndeclareatom{\tnlocalatom}{skin=dot}"
        r"\tnlocalatom[label shift={64mm,65mm}]{A}}"
        r"\tnlocalatom[label shift={66mm,67mm}]{B}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in scoped_atom_declaration
    ] != [
        ("64mm", None),
        ("65mm", None),
        ("66mm", None),
        ("67mm", None),
    ]:
        raise AssertionError(
            "a local dynamic atom escaped source-wide quarantine: "
            f"{scoped_atom_declaration!r}"
        )
    compatibility_then_duplicate = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclareatom{\tnduplicateatom}{skin=dot}"
        r"\tndeclare{atom}{tnduplicateatom}{skin=dot}"
        r"\tnduplicateatom[label shift={68mm,69mm}]{A}",
    )
    if len(compatibility_then_duplicate) != 2 or any(
        occurrence.owner is not None
        for occurrence in compatibility_then_duplicate
    ):
        raise AssertionError(
            "duplicate declarations escaped dynamic quarantine: "
            f"{compatibility_then_duplicate!r}"
        )
    kernel_then_duplicate = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tndeclare{atom}{tnotherduplicate}{skin=dot}"
        r"\tndeclareatom{\tnotherduplicate}{skin=dot}"
        r"\tnotherduplicate[label shift={70mm,71mm}]{A}",
    )
    if len(kernel_then_duplicate) != 2 or any(
        occurrence.owner is not None for occurrence in kernel_then_duplicate
    ):
        raise AssertionError(
            "a rejected duplicate replaced an active kernel atom: "
            f"{kernel_then_duplicate!r}"
        )
    reused_atom_declaration = scan_case_dimensions(
        Path("synthetic.tex"),
        r"{\tndeclareatom{\tnreusedatom}{skin=dot}"
        r"\tnreusedatom[label shift={72mm,73mm}]{A}}"
        r"{\tndeclare{atom}{tnreusedatom}{skin=dot}"
        r"\tnreusedatom[label shift={74mm,75mm}]{B}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in reused_atom_declaration
    ] != [
        ("72mm", None),
        ("73mm", None),
        ("74mm", None),
        ("75mm", None),
    ]:
        raise AssertionError(
            "a reused dynamic name escaped source-wide quarantine: "
            f"{reused_atom_declaration!r}"
        )
    environment_scoped_atom = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\begin{tenkzeq}\tndeclareatom{\tnenvatom}{skin=dot}"
        r"\tnenvatom[label shift={76mm,77mm}]{A}\end{tenkzeq}"
        r"\tnarrow{\tnenvatom[label shift={78mm,79mm}]{B}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in environment_scoped_atom
    ] != [
        ("76mm", None),
        ("77mm", None),
        ("78mm", None),
        ("79mm", None),
    ]:
        raise AssertionError(
            "an environment-local atom escaped source-wide quarantine: "
            f"{environment_scoped_atom!r}"
        )
    for kernel_name in ("tn spaced", "tn\nspaced"):
        csname_declared_atom = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tndeclare{{atom}}{{{kernel_name}}}{{skin=dot}}"
            r"\tnarrow{\tnspaced[label shift={107mm,108mm}]{A}}",
        )
        if len(csname_declared_atom) != 2 or any(
            occurrence.owner is not None for occurrence in csname_declared_atom
        ):
            raise AssertionError(
                "a csname-normalized kernel atom escaped quarantine: "
                f"name={kernel_name!r}, occurrences={csname_declared_atom!r}"
            )
    for environment in (
        "tenkz",
        "tenkzcd",
        "tenkzfree",
        "tenkzlattice",
        "tenkzplanes",
        "tenkzeq",
    ):
        nested_environment = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tnarrow{{\begin{{{environment}}}"
            rf"\rule{{43mm}}{{44mm}}\end{{{environment}}}}}",
        )
        if len(nested_environment) != 2 or any(
            occurrence.owner is not None for occurrence in nested_environment
        ):
            raise AssertionError(
                f"a nested {environment} environment inherited route ownership: "
                f"{nested_environment!r}"
            )
    unbraced_pgf_pair = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\begin{tenkzlattice}[col vector=(45mm,46mm)]"
        r"\end{tenkzlattice}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in unbraced_pgf_pair
    ] != [
        ("45mm", DimensionOwner.FRAME),
        ("46mm", None),
    ]:
        raise AssertionError(
            "parentheses incorrectly protected a PGF option comma: "
            f"{unbraced_pgf_pair!r}"
        )
    unbraced_pgf_brackets = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow{\tn[label shift=[47mm,48mm]]{A}}",
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in unbraced_pgf_brackets
    ] != [
        ("47mm", DimensionOwner.LAYOUT),
        ("48mm", None),
    ]:
        raise AssertionError(
            "brackets incorrectly protected a PGF option comma: "
            f"{unbraced_pgf_brackets!r}"
        )
    spliced_environment_source = r"""\tnarrow{
  \begin{ten% splice an environment name
kz}[pitch=49mm]\rule{50mm}{51mm}\end{ten% splice the closing name
kz}}
"""
    spliced_environment = scan_case_dimensions(
        Path("synthetic.tex"), spliced_environment_source
    )
    if [
        (occurrence.literal, occurrence.owner)
        for occurrence in spliced_environment
    ] != [
        ("49mm", DimensionOwner.METRIC),
        ("50mm", None),
        ("51mm", None),
    ]:
        raise AssertionError(
            "a comment-spliced environment lost its neutral boundary: "
            f"{spliced_environment!r}"
        )
    for spaced_name in ("ten kz", "tenkz cd", " tenkz", "ten\nkz"):
        spaced_environment = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tnarrow{{\begin{{{spaced_name}}}[pitch=90mm]"
            rf"\rule{{91mm}}{{92mm}}\end{{{spaced_name}}}}}",
        )
        if [
            (occurrence.literal, occurrence.owner)
            for occurrence in spaced_environment
        ] != [
            ("90mm", DimensionOwner.METRIC),
            ("91mm", None),
            ("92mm", None),
        ]:
            raise AssertionError(
                "a csname-spaced environment lost its public boundary: "
                f"name={spaced_name!r}, occurrences={spaced_environment!r}"
            )
    for expanded_space_name in (
        r"ten\space kz",
        r"ten\space\space kz",
        "ten\\space% preserve the control-word boundary\nkz",
    ):
        expanded_space_environment = scan_case_dimensions(
            Path("synthetic.tex"),
            rf"\tnarrow{{\begin{{{expanded_space_name}}}[pitch=109mm]"
            rf"\rule{{110mm}}{{111mm}}\end{{{expanded_space_name}}}}}",
        )
        if [
            (occurrence.literal, occurrence.owner)
            for occurrence in expanded_space_environment
        ] != [
            ("109mm", DimensionOwner.METRIC),
            ("110mm", None),
            ("111mm", None),
        ]:
            raise AssertionError(
                "an expanded-space environment lost its public boundary: "
                f"name={expanded_space_name!r}, "
                f"occurrences={expanded_space_environment!r}"
            )
    macro_environment = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\def\tenname{tenkz}"
        r"\tnarrow{\begin{\tenname}[pitch=112mm]"
        r"\rule{113mm}{114mm}\end{\tenname}}",
    )
    if len(macro_environment) != 3 or any(
        occurrence.owner is not None for occurrence in macro_environment
    ):
        raise AssertionError(
            "an unresolved expandable environment escaped neutral quarantine: "
            f"{macro_environment!r}"
        )
    nested_label_shift = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\tnarrow[from=1,to=2]{\tnpic[inline]{"
        r"\tn*[label shift={19mm,20mm}]{A}}}",
    )
    if len(nested_label_shift) != 2 or any(
        occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in nested_label_shift
    ):
        raise AssertionError(
            "a nested object label shift inherited route ownership: "
            f"{nested_label_shift!r}"
        )
    spliced_picture_key_source = """\\tnarrow[from=1,to=2]{
  \\tnpic[pit% splice the public option key
ch=21mm,inline]{\\tn{A}}}
"""
    spliced_picture_key = scan_case_dimensions(
        Path("synthetic.tex"), spliced_picture_key_source
    )
    if (
        len(spliced_picture_key) != 1
        or spliced_picture_key[0].owner is not DimensionOwner.METRIC
        or spliced_picture_key[0].line != 3
        or spliced_picture_key[0].offset
        != spliced_picture_key_source.index("21mm")
    ):
        raise AssertionError(
            "a comment-spliced picture key inherited route ownership: "
            f"{spliced_picture_key!r}"
        )
    split_picture_source = "\\tn% terminate the control word\npic[pitch=22mm]{x}\n"
    split_picture = scan_case_dimensions(
        Path("synthetic.tex"), split_picture_source
    )
    if (
        len(split_picture) != 1
        or split_picture[0].owner is not None
        or split_picture[0].line != 2
    ):
        raise AssertionError(
            "a comment-split picture control word gained option ownership: "
            f"{split_picture!r}"
        )
    comment_spliced_source = """\\tnput{x}{(1% join the number and unit
 mm,2m% join the unit letters
 m,3tr% join the true prefix
 ue pt)}{}
"""
    comment_spliced_units = scan_case_dimensions(
        Path("synthetic.tex"), comment_spliced_source
    )
    expected_spliced = [
        ("1mm", 1, comment_spliced_source.index("1%")),
        ("2mm", 2, comment_spliced_source.index("2m%")),
        ("3true pt", 3, comment_spliced_source.index("3tr%")),
    ]
    if [
        (occurrence.literal, occurrence.line, occurrence.offset)
        for occurrence in comment_spliced_units
    ] != expected_spliced or any(
        occurrence.in_comment
        or occurrence.owner is not DimensionOwner.LAYOUT
        for occurrence in comment_spliced_units
    ):
        raise AssertionError(
            "comment-spliced active dimensions lost their source locations: "
            f"{comment_spliced_units!r}"
        )
    split_owner_source = "\\tn% terminate the control word\nput{x}{1mm}{}\n"
    split_owner = scan_case_dimensions(Path("synthetic.tex"), split_owner_source)
    if (
        len(split_owner) != 1
        or split_owner[0].owner is not None
        or split_owner[0].line != 2
        or split_owner[0].offset != split_owner_source.index("1mm")
    ):
        raise AssertionError(
            f"a comment-split control word gained dimension ownership: {split_owner!r}"
        )
    for extended_comment_command in (
        "% \\tnput_extra 47mm\n",
        "% \\tnjoin@extra 48mm\n",
        "% \\tnwire:extra 49mm\n",
        "% \\tnedgeλ 50mm\n",
    ):
        comment_dimensions = scan_case_dimensions(
            Path("synthetic.tex"), extended_comment_command
        )
        if (
            len(comment_dimensions) != 1
            or comment_dimensions[0].owner is not None
            or not comment_dimensions[0].in_comment
        ):
            raise AssertionError(
                "an extended comment control word matched a public-command prefix: "
                f"source={extended_comment_command!r}, "
                f"occurrences={comment_dimensions!r}"
            )
    book_spliced_source = "\\setlength\\textwidth{1m% join the unit\n m}\n"
    book_spliced = scan_book_dimensions(Path("book.tex"), book_spliced_source)
    if (
        len(book_spliced) != 1
        or book_spliced[0].literal != "1mm"
        or book_spliced[0].line != 1
        or book_spliced[0].offset != book_spliced_source.index("1m%")
    ):
        raise AssertionError(
            f"book comment-spliced dimension escaped: {book_spliced!r}"
        )
    suffix_key = scan_case_dimensions(
        Path("synthetic.tex"),
        r"\begin{tenkz}[narrow vector=1mm]\end{tenkz}",
    )
    if len(suffix_key) != 1 or suffix_key[0].owner is not None:
        raise AssertionError(f"option key suffix gained an owner: {suffix_key!r}")
    if scan_case_dimensions(
        Path("synthetic.tex"), "% at y=-0.75 in the author source\n"
    ):
        raise AssertionError("the English preposition 'in' became an inch unit")
    for prose in (
        "% site 3 in Section III\n",
        "% each of 4 in total\n",
        "% label 2 in figure 3\n",
        "% Figure 3 in the layout shows the path\n",
        "% use site 2 in the frame\n",
        "% There are 3 inputs in the panel.\n",
        "% The panel has 3 insets in total.\n",
        "% 2 points, 1 piece, and 3 special cases remain.\n",
        "% 2 pts and 1 pcs remain.\n",
        "% version 3 in the layout uses the old syntax\n",
        "% equation 2 in the figure shows the route\n",
        "% width of Figure 3 in the layout is fixed\n",
    ):
        if scan_case_dimensions(Path("synthetic.tex"), prose):
            raise AssertionError(f"English prose became an inch unit: {prose!r}")
    quantified_comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% each of 4 in wide sheets is retained\n"
    )
    if (
        len(quantified_comment_inch) != 1
        or quantified_comment_inch[0].owner is not DimensionOwner.LAYOUT
        or not quantified_comment_inch[0].in_comment
    ):
        raise AssertionError(
            "a dimension adjective did not disambiguate a quantified inch: "
            f"{quantified_comment_inch!r}"
        )
    compact_comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% retained clearance 1in\n"
    )
    if len(compact_comment_inch) != 1 or not compact_comment_inch[0].in_comment:
        raise AssertionError(
            f"compact comment inch escaped: {compact_comment_inch!r}"
        )
    governed_comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% clearance is 1 in.\n"
    )
    if (
        len(governed_comment_inch) != 1
        or not governed_comment_inch[0].in_comment
    ):
        raise AssertionError(
            "a local measurement phrase did not govern a spaced inch: "
            f"{governed_comment_inch!r}"
        )
    for source, owner in (
        ("% clearance = 1 in.\n", None),
        ("% width: 1 in.\n", DimensionOwner.LAYOUT),
        ("% spacing of 1 in.\n", DimensionOwner.METRIC),
    ):
        governed_comment_inch = scan_case_dimensions(Path("synthetic.tex"), source)
        if (
            len(governed_comment_inch) != 1
            or governed_comment_inch[0].owner is not owner
            or not governed_comment_inch[0].in_comment
        ):
            raise AssertionError(
                "measurement punctuation did not govern a spaced inch: "
                f"{governed_comment_inch!r}"
            )
    for source in (
        r"% \tnjoin path is 1 in from the origin" "\n",
        "% routes 2 in long\n",
        "% the distances 5 in apart\n",
    ):
        local_measurement = scan_case_dimensions(Path("synthetic.tex"), source)
        if len(local_measurement) != 1 or not local_measurement[0].in_comment:
            raise AssertionError(
                f"local comment measurement escaped: {local_measurement!r}"
            )
    ownerless_comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% shifted 1 in leftward\n"
    )
    if len(ownerless_comment_inch) != 1 or not ownerless_comment_inch[0].in_comment:
        raise AssertionError(
            f"ownerless comment inch escaped: {ownerless_comment_inch!r}"
        )
    active_inch = scan_case_dimensions(
        Path("synthetic.tex"), r"\tnput{x}{(1 in plus 2pt,0)}{}"
    )
    if [occurrence.literal for occurrence in active_inch] != ["1 in", "2pt"]:
        raise AssertionError(f"active spaced inch escaped: {active_inch!r}")
    comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% layout width is 1 in wide\n"
    )
    if len(comment_inch) != 1 or not comment_inch[0].in_comment:
        raise AssertionError(f"comment inch escaped: {comment_inch!r}")
    owned_comment_inch = scan_case_dimensions(
        Path("synthetic.tex"), "% pitch is 1 in the final figure\n"
    )
    if (
        len(owned_comment_inch) != 1
        or owned_comment_inch[0].owner is not DimensionOwner.METRIC
        or not owned_comment_inch[0].in_comment
    ):
        raise AssertionError(
            f"owned comment inch escaped: {owned_comment_inch!r}"
        )
    for source, owner in (
        ("% width is 1 in wide\n", DimensionOwner.LAYOUT),
        ("% offset 1 in north\n", DimensionOwner.FRAME),
    ):
        semantic_comment_inch = scan_case_dimensions(Path("synthetic.tex"), source)
        if (
            len(semantic_comment_inch) != 1
            or semantic_comment_inch[0].owner is not owner
            or not semantic_comment_inch[0].in_comment
        ):
            raise AssertionError(
                f"semantic comment inch escaped: {semantic_comment_inch!r}"
            )

    extra_layout = DimensionOccurrence(
        Path("synthetic.tex"),
        1,
        "1mm",
        DimensionOwner.LAYOUT,
        False,
        0,
    )
    _expect_dimension_failure(
        dataclasses.replace(report, cases=(*report.cases, extra_layout)),
        "case dimensions increased to 927",
    )
    _expect_dimension_failure(
        dataclasses.replace(report, cases=(*report.cases, extra_layout)),
        "composition/layout dimensions increased to 531",
    )
    for source, phrase in (
        (r"\begin{tenkz}[pitch=1mm]\end{tenkz}", "metric dimensions increased"),
        (
            r"\begin{tenkzlattice}[sheet vector={0mm,1mm}]"
            r"\end{tenkzlattice}",
            "projection/frame dimensions increased",
        ),
        (r"\tnjoin{a}{1mm}", "route/string dimensions increased to 397"),
    ):
        mutation = scan_case_dimensions(Path("synthetic.tex"), source)
        _expect_dimension_failure(
            dataclasses.replace(report, cases=(*report.cases, *mutation)),
            phrase,
        )
    unknown = scan_case_dimensions(Path("synthetic.tex"), r"\foo{1 in}")
    _expect_dimension_failure(
        dataclasses.replace(report, cases=(*report.cases, *unknown)),
        "unowned case dimension",
    )
    comment = scan_case_dimensions(Path("synthetic.tex"), "% pitch=1mm\n")
    _expect_dimension_failure(
        dataclasses.replace(report, cases=(*report.cases, *comment)),
        "comment dimensions increased",
    )
    book_path = next(iter(BOOK_LAYOUT_ALLOWLIST))
    extra_book = DimensionOccurrence(
        book_path,
        1,
        "1pt",
        DimensionOwner.BOOK_LAYOUT,
        False,
        0,
    )
    _expect_dimension_failure(
        dataclasses.replace(report, book=(*report.book, extra_book)),
        "allowlist requires exactly",
    )

    first_route = next(
        index
        for index, occurrence in enumerate(report.cases)
        if occurrence.owner is DimensionOwner.ROUTE
    )
    reduced = dataclasses.replace(
        report,
        cases=report.cases[:first_route] + report.cases[first_route + 1 :],
    )
    validate_dimension_report(reduced)


def test_rmp_author_source_identity() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    cited = sorted(
        {
            target.author_source
            for target in targets
            if target.author_source is not None
        },
        key=lambda path: path.as_posix(),
    )
    committed = sorted(
        load_author_source_hashes(AUTHOR_SOURCE_HASHES),
        key=lambda path: path.as_posix(),
    )
    if committed != cited:
        raise AssertionError(
            "committed author-source hashes disagree with manifest.toml"
        )
    with tempfile.TemporaryDirectory(prefix="tenkz-rmp-author-source-") as tmp:
        work = Path(tmp)
        source_root = work / "RMP_TIKZ_SOURCE_CODE"
        for index, source in enumerate(cited, 1):
            candidate = source_root / source
            candidate.parent.mkdir(parents=True, exist_ok=True)
            candidate.write_text(f"author source {index}\n", encoding="utf-8")
        hashes = work / "author-source.sha256"
        hashes.write_text(
            "".join(
                f"{sha256(source_root / source)}  {source.as_posix()}\n"
                for source in cited
            ),
            encoding="utf-8",
        )
        snapshot_root = work / "verified-snapshot"
        verified = verify_author_source_tree(
            targets,
            source_root,
            hashes_path=hashes,
            snapshot_root=snapshot_root,
        )
        if verified != len(cited):
            raise AssertionError("author-source verifier lost a cited source")

        changed = source_root / cited[0]
        original = changed.read_text(encoding="utf-8")
        snapshotted = snapshot_root / cited[0]
        if snapshotted.read_text(encoding="utf-8") != original:
            raise AssertionError("author-source snapshot changed the verified bytes")
        changed.write_text("different authority\n", encoding="utf-8")
        if snapshotted.read_text(encoding="utf-8") != original:
            raise AssertionError("author-source snapshot followed the live tree")
        try:
            verify_author_source_tree(targets, source_root, hashes_path=hashes)
        except RMPError as exc:
            if "author source hash mismatch" not in str(exc):
                raise AssertionError(
                    f"changed author source produced the wrong failure: {exc}"
                ) from exc
        else:
            raise AssertionError("changed author source passed identity verification")

        changed.write_text(original, encoding="utf-8")
        hashes.write_text(
            hashes.read_text(encoding="utf-8")
            + f"{'0' * 64}  uncited.tex\n",
            encoding="utf-8",
        )
        try:
            verify_author_source_tree(targets, source_root, hashes_path=hashes)
        except RMPError as exc:
            if "uncited: uncited.tex" not in str(exc):
                raise AssertionError(
                    f"uncited hash entry produced the wrong failure: {exc}"
                ) from exc
        else:
            raise AssertionError("uncited author-source hash entry was accepted")


def test_rmp_pairing_identity() -> None:
    targets = load_manifest(DEFAULT_MANIFEST)
    with tempfile.TemporaryDirectory(prefix="tenkz-rmp-pairing-") as tmp:
        stale = Path(tmp) / "verdicts.toml"
        text = DEFAULT_VERDICT.read_text(encoding="utf-8")
        stale.write_text(
            re.sub(
                r'(?m)^pairing_sha256 = "[0-9a-f]{64}"$',
                f'pairing_sha256 = "{"0" * 64}"',
                text,
                count=1,
            ),
            encoding="utf-8",
        )
        original = tenkz_rmp.DEFAULT_VERDICT
        tenkz_rmp.DEFAULT_VERDICT = stale
        try:
            tenkz_rmp.load_verdicts(targets)
        except RMPError as exc:
            if "stale pairing verdicts" not in str(exc):
                raise AssertionError(
                    f"stale pairing digest produced the wrong failure: {exc}"
                ) from exc
        else:
            raise AssertionError("stale pairing digest was accepted")
        finally:
            tenkz_rmp.DEFAULT_VERDICT = original


def main() -> int:
    test_kernel_capability_owner()
    test_ink_environment_owner()
    test_rmp_dimension_ownership()
    test_rmp_author_source_identity()
    test_rmp_pairing_identity()
    with PROVENANCE.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.reader(stream, dialect="excel-tab"))

    with tempfile.TemporaryDirectory(prefix="tenkz-provenance-") as tmp:
        work = Path(tmp)

        reordered = work / "reordered.tsv"
        write_rows(reordered, [rows[0], *reversed(rows[1:])])
        reordered_run = validate(reordered)
        if reordered_run.returncode:
            raise AssertionError(
                "canonical source-name digest depended on TSV row order:\n"
                + reordered_run.stdout
                + reordered_run.stderr
            )

        mutated_rows = [row.copy() for row in rows]
        excluded = next(row for row in mutated_rows[1:] if row[1] == "excluded")
        excluded[0] = "mutated-excluded-source.tex"
        mutated = work / "mutated.tsv"
        write_rows(mutated, mutated_rows)
        mutated_run = validate(mutated)
        if (mutated_run.returncode == 0
                or "source-file census SHA-256" not in mutated_run.stderr):
            raise AssertionError(
                "source-name invariant accepted an excluded-name swap:\n"
                + mutated_run.stdout
                + mutated_run.stderr
            )

        missing = work / "missing.tsv"
        missing_run = validate(missing)
        if (missing_run.returncode == 0
                or f"cannot read {missing}:" not in missing_run.stderr):
            raise AssertionError(
                "read failure did not identify the overridden provenance path:\n"
                + missing_run.stdout
                + missing_run.stderr
            )

    print("PASS: tenkz provenance source-name invariant")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
