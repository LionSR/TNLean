#!/usr/bin/env python3
"""Contract tests for the shrink-gate meters, detectors, and gate rule."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/tenkz_shrink.py"

sys.path.insert(0, str(ROOT / "scripts"))
from tenkz_language import (  # noqa: E402
    Entry,
    _kernel_leaf_keys_from_texts,
    check,
    parse_alias_payload,
    parse_status,
)
from tenkz_lint import registry_alias_patterns  # noqa: E402
import tenkz_shrink  # noqa: E402


def test_parse_status_ledgers() -> None:
    assert parse_status("kernel") == ("kernel", "")
    assert parse_status("escape") == ("escape", "")
    assert parse_status("sugar(rows={ket,op,bra})")[0] == "sugar"
    assert parse_status("alias(span; sunset=1.0)") == ("alias", "span; sunset=1.0")
    try:
        parse_status("canonical")
    except ValueError:
        pass
    else:
        raise AssertionError("legacy status word accepted")


def test_alias_sunset_validation() -> None:
    assert parse_alias_payload("frame; sunset=1.0") == ("frame", "1.0")
    for payload in ("frame; sunset=", "frame; sunset=1", "frame; sunset=1.1"):
        try:
            parse_alias_payload(payload)
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid alias sunset accepted: {payload}")


def test_alias_records_include_values_and_normalize_ids() -> None:
    records = tenkz_shrink.alias_records(
        [
            Entry(
                "key",
                (
                    "picture",
                    "chain~axis",
                    "enum(east|south)",
                    "east",
                    "alias(frame; sunset=1.0)",
                    "Legacy frame spelling.",
                ),
            ),
            Entry(
                "alias",
                (
                    "connection",
                    "route=curve",
                    "route=arc",
                    "Legacy curved route. Sunset 1.0.",
                ),
            ),
        ]
    )
    assert records == [
        ("picture", "chain axis", "1.0"),
        ("connection", "route=curve", "1.0"),
    ]


def test_sugar_expansion_checks_every_token() -> None:
    entries = tenkz_shrink.load_registry()
    for fragment in ("completely bogus", "bogus2", "Bogus", "completely-bogus"):
        changed = [
            Entry(
                entry.kind,
                (*entry.fields[:4], f"sugar(rows=, {fragment}=)", entry.fields[5]),
            )
            if entry.kind == "key"
            and entry.fields[0] == "picture"
            and entry.fields[1] == "physical"
            else entry
            for entry in entries
        ]
        errors = check(changed)
        assert any("sugar row picture:physical" in error for error in errors), (
            fragment,
            errors,
        )
    changed_enum = [
        Entry(
            entry.kind,
            (
                *entry.fields[:4],
                "sugar(trace style=bogus)",
                entry.fields[5],
            ),
        )
        if entry.kind == "key"
        and entry.fields[0] == "picture"
        and entry.fields[1] == "physical"
        else entry
        for entry in entries
    ]
    errors = check(changed_enum)
    assert any(
        "sugar row picture:physical replacement value 'bogus'"
        in error
        for error in errors
    ), errors


def test_parser_registry_census_preserves_scopes() -> None:
    entries = tenkz_shrink.load_registry()
    moved = [
        Entry(
            entry.kind,
            ("picture", *entry.fields[1:]),
        )
        if entry.kind == "key"
        and entry.fields[0] == "annotation"
        and entry.fields[1] == "brace above"
        else entry
        for entry in entries
    ]
    errors = check(moved)
    assert any(
        "missing=annotation:brace above" in error
        and "extra=picture:brace above" in error
        for error in errors
    ), errors


def test_kernel_parser_census_includes_hyphenated_families() -> None:
    source = r"""
\__tenkz_kernel_value:nnn
  { tenkz-kernel-declare-atom } { skin } { skin }
\keys_define:nn { tenkz-kernel-declare-atom }
  {
    ports .code:n = { }
  }
"""
    assert _kernel_leaf_keys_from_texts([source]) == {
        ("kernel-declare-atom", "skin"),
        ("kernel-declare-atom", "ports"),
    }


def test_alias_replacements_are_registered_vocabulary() -> None:
    entries = tenkz_shrink.load_registry()
    for replacement in ("does not exist", " "):
        changed = [
            Entry(
                entry.kind,
                (
                    *entry.fields[:4],
                    f"alias({replacement}; sunset=1.0)",
                    entry.fields[5],
                ),
            )
            if entry.kind == "key"
            and entry.fields[0] == "picture"
            and entry.fields[1] == "chain axis"
            else entry
            for entry in entries
        ]
        errors = check(changed)
        assert any("alias row picture:chain axis" in error for error in errors), (
            replacement,
            errors,
        )
    changed_value = [
        Entry(
            entry.kind,
            (entry.fields[0], entry.fields[1], "route=bogus", entry.fields[3]),
        )
        if entry.kind == "alias" and entry.fields[1] == "route=curve"
        else entry
        for entry in entries
    ]
    errors = check(changed_value)
    assert any(
        "value alias connection:route=curve replacement value 'bogus'"
        in error
        for error in errors
    ), errors
    changed_key_alias = [
        Entry(
            entry.kind,
            (
                *entry.fields[:4],
                "alias(boundary=bogus; sunset=1.0)",
                entry.fields[5],
            ),
        )
        if entry.kind == "key"
        and entry.fields[0] == "picture"
        and entry.fields[1] == "periodic"
        else entry
        for entry in entries
    ]
    errors = check(changed_key_alias)
    assert any(
        "alias row picture:periodic replacement value 'bogus'"
        in error
        for error in errors
    ), errors


def test_option_key_names_distinguish_bare_keys_from_values() -> None:
    assert tenkz_shrink._option_key_names("rows=wire, open") == ["rows", "open"]
    assert tenkz_shrink._option_key_names("open, rows=wire") == ["open", "rows"]
    assert tenkz_shrink._option_key_names("boundary=open") == ["boundary"]
    assert tenkz_shrink._option_key_names("rows={ket,op,bra}") == ["rows"]


def test_escape_usage_is_scoped_to_picture_options() -> None:
    path = ROOT / "synthetic.tex"
    corpus = {
        path: "The spectral radius, then "
        r"\begin{tenkz}[rows=wire, radius=2]\tn{A}\end{tenkz}"
    }
    scoped = tenkz_shrink.scoped_option_groups(corpus)
    assert sum(
        tenkz_shrink._option_key_names(payload).count("radius")
        for payloads in scoped["picture"].values()
        for payload in payloads
    ) == 1


def test_setup_consumers_include_picture_options() -> None:
    path = ROOT / "synthetic.tex"
    corpus = {
        path: (
            r"\tnset{pitch=10mm} "
            r"\begin{tenkz}[compact]\tn{A}\end{tenkz} "
            r"\tnpic[inline, tensor style=box]{\tn{B}}"
        )
    }
    scoped = tenkz_shrink.scoped_option_groups(corpus)["setup"][path]
    names = {
        name
        for payload in scoped
        for name in tenkz_shrink._option_key_names(payload)
    }
    for key in ("pitch", "compact", "inline", "tensor style"):
        assert key in names


def test_setup_consumers_include_only_forwarded_tree_options() -> None:
    path = ROOT / "synthetic.tex"
    corpus = {
        path: (
            r"\tntree[pitch=9mm, compact, inline, species=fermion, "
            r"tree style=ribbon, role=operator]{(a\,b)_c}"
        )
    }
    scoped = tenkz_shrink.scoped_option_groups(corpus)
    setup_names = {
        name
        for payload in scoped["setup"][path]
        for name in tenkz_shrink._option_key_names(payload)
    }
    object_names = {
        name
        for payload in scoped["object"][path]
        for name in tenkz_shrink._option_key_names(payload)
    }
    assert setup_names == {"pitch", "compact", "inline"}
    assert object_names == {
        "pitch",
        "compact",
        "inline",
        "species",
        "tree style",
        "role",
    }
    entries = [
        Entry("key", ("setup", "species", "name-list", "empty", "kernel", "")),
        Entry("key", ("object", "species", "declared-name", "empty", "kernel", "")),
    ]
    consumers = tenkz_shrink.row_consumers(entries, corpus)
    assert consumers["key:setup:species"] == set()
    assert consumers["key:object:species"] == {"synthetic.tex"}


def test_only_kernel_scopes_may_lack_consumer_groups() -> None:
    groups = {"object": {ROOT / "synthetic.tex": ["skin=box"]}}
    assert tenkz_shrink._scope_groups(groups, "kernel-wire") == {}
    try:
        tenkz_shrink._scope_groups(groups, "objct")
    except KeyError as error:
        assert "unknown registry scope: objct" in str(error)
    else:
        raise AssertionError("a misspelled non-kernel scope was accepted")


def test_cooccurrence_is_measured_per_invocation() -> None:
    entries = [
        Entry(
            "key",
            ("connection", "label", "math", "empty", "kernel", "Label."),
        ),
        Entry(
            "key",
            ("connection", "role", "name", "empty", "kernel", "Role."),
        ),
    ]
    corpus = {
        ROOT / f"synthetic-{index}.tex": (
            rf"\tnedge[label=x]{{a{index}}}{{b{index}}} "
            rf"\tnedge[role=wire]{{c{index}}}{{d{index}}}"
        )
        for index in range(5)
    }
    assert not any(
        flag["id"] == "flag:cooccur:connection:label+role"
        for flag in tenkz_shrink.flags(entries, corpus)
    )


def test_command_signatures_are_balanced_and_include_optionless_uses() -> None:
    source = r"\tnarrow[east at={1,2}, dir]{x} \tnarrow{x} \tntree{LR}"
    assert tenkz_shrink._command_invocations(source, "tnarrow") == [
        "east at={1,2}, dir",
        None,
    ]
    assert tenkz_shrink._top_level_option_parts("east at={1,2}, dir") == [
        "east at={1,2}",
        "dir",
    ]
    assert tenkz_shrink._command_invocations(source, "tntree") == [None]


def test_meters_shape() -> None:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "meters"], capture_output=True, text=True, check=True
    )
    data = json.loads(result.stdout)
    expected = {
        "m1_census",
        "m2_parser_paths",
        "m3_escape_usage",
        "m4_lines_per_case",
        "m5_aliases",
        "m6_overloads",
    }
    assert set(data) == expected, sorted(data)
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    assert set(data["m1_census"]["value"]) == {
        "kernel",
        "sugar",
        "alias",
        "escape",
        "commands",
        "environments",
    }
    assert sum(data["m1_census"]["value"].values()) == sum(
        baseline["m1_census"]["value"].values()
    )
    for meter in data.values():
        assert meter["definition"]


def test_manifest_freezes_case_denominator() -> None:
    cases = tenkz_shrink.manifest_case_paths()
    assert len(cases) == 130
    assert len(set(cases)) == 130


def test_rmp_alias_patterns_use_only_alias_ledgers() -> None:
    patterns = registry_alias_patterns()
    canonical = "dot, route=arc, out=90, in=0, label=x"
    assert not any(pattern.search(canonical) for pattern in patterns)
    assert any(pattern.search("chain axis=east") for pattern in patterns)
    assert any(pattern.search("route=curve") for pattern in patterns)


def test_baseline_matches_actuals() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "meters"], capture_output=True, text=True, check=True
    )
    assert json.loads(result.stdout) == baseline


def test_gate_requires_verdicts() -> None:
    section = tenkz_shrink.latest_session_section(
        (ROOT / "docs/tenkz/SHRINK.md").read_text()
    )
    entries = tenkz_shrink.load_registry()
    corpus = tenkz_shrink.consumer_files()
    verdicts = tenkz_shrink.session_verdict_ids(section)
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    branch, failures = tenkz_shrink.evaluate_gate(
        entries,
        corpus,
        baseline,
        copy.deepcopy(baseline),
        verdicts,
        has_extension=False,
    )
    assert branch == "verdicts"
    assert not failures, failures


def test_gate_accepts_a_decreased_census_without_verdicts() -> None:
    entries = tenkz_shrink.load_registry()
    corpus = tenkz_shrink.consumer_files()
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    previous = copy.deepcopy(baseline)
    previous["m1_census"]["value"]["kernel"] += 1
    branch, failures = tenkz_shrink.evaluate_gate(
        entries,
        corpus,
        baseline,
        previous,
        set(),
        has_extension=False,
    )
    assert branch == "decreased"
    assert not failures


def test_prechange_ratchet_requires_extension_citation() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    current = copy.deepcopy(baseline)
    previous = copy.deepcopy(baseline)
    current["m2_parser_paths"]["value"] += 1
    errors = tenkz_shrink.ratchet_errors(
        current, previous, has_extension=False
    )
    assert errors == [
        "M2 parser paths increased without an Extension-gate: #NNNN citation"
    ]
    assert not tenkz_shrink.ratchet_errors(
        current, previous, has_extension=True
    )


def test_parser_identity_swap_requires_extension_citation() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    current = copy.deepcopy(baseline)
    current["m2_parser_paths"]["identity_sha256"] = "0" * 64
    errors = tenkz_shrink.ratchet_errors(
        current, baseline, has_extension=False
    )
    assert errors == [
        "M2 parser identities changed without an Extension-gate: #NNNN citation"
    ]
    assert not tenkz_shrink.ratchet_errors(
        current, baseline, has_extension=True
    )


def test_census_correction_requires_unchanged_parser_surface() -> None:
    baseline = json.loads((ROOT / "tests/tenkz/census-baseline.json").read_text())
    current = copy.deepcopy(baseline)
    previous = copy.deepcopy(baseline)
    current["m1_census"]["value"]["kernel"] += 3
    current["m6_overloads"]["value"]["multi_typed_names"] += 1
    assert tenkz_shrink.ratchet_errors(
        current,
        previous,
        has_extension=False,
    )
    assert not tenkz_shrink.ratchet_errors(
        current,
        previous,
        has_extension=False,
        has_census_correction=True,
    )
    current["m2_parser_paths"]["value"] += 1
    assert tenkz_shrink.ratchet_errors(
        current,
        previous,
        has_extension=False,
        has_census_correction=True,
    )
    current["m2_parser_paths"]["value"] -= 1
    current["m2_parser_paths"]["identity_sha256"] = "0" * 64
    assert tenkz_shrink.ratchet_errors(
        current,
        previous,
        has_extension=False,
        has_census_correction=True,
    )


def test_extension_citation_comes_only_from_added_lines() -> None:
    patch = """--- a/old
+++ b/new
-Extension-gate: #1234
 context Extension-gate: #2345
+ordinary addition
"""
    assert "Extension-gate" not in tenkz_shrink.added_diff_text(patch)
    assert (
        tenkz_shrink.added_diff_text(patch + "+Extension-gate: #3456\n")
        .splitlines()[-1]
        == "Extension-gate: #3456"
    )


def test_ledger_history_is_append_only() -> None:
    previous = "# The shrink ledger\n\n## Session 0\nold verdict\n"
    assert not tenkz_shrink.ledger_history_errors(
        previous + "\n## Session 1\nnew verdict\n",
        previous,
    )
    assert tenkz_shrink.ledger_history_errors(
        previous.replace("old verdict", "rewritten verdict"),
        previous,
    )


def test_verdict_parser_requires_an_exact_table_row() -> None:
    section = """Agenda mentions flag:consumers:key:picture:open.

| flag | verdict |
|---|---|
| flag:consumers:key:picture:open-ended | keep; expiry 0.9 |
| flag:bad-keep | keep-because: needed |
| flag:nonsense | nonsense; expiry 0.9 |
"""
    assert tenkz_shrink.session_verdict_ids(section) == {
        "flag:consumers:key:picture:open-ended"
    }


def test_verdict_parser_rejects_expired_lifetimes() -> None:
    section = """| flag | verdict |
|---|---|
| flag:old-expiry | keep-because: old; expiry 0.8 |
| flag:current-expiry | keep-because: current; expiry 0.9 |
| flag:future-expiry | keep-because: future; expiry 1.0 |
| flag:old-execution | executes at the 0.8 freeze |
| flag:future-execution | executes at the 1.0 freeze |
| flag:doctrine | keep-because: doctrine; permanent |
"""
    assert tenkz_shrink.session_verdict_ids(
        section,
        current_milestone="0.9",
    ) == {
        "flag:current-expiry",
        "flag:future-expiry",
        "flag:future-execution",
        "flag:doctrine",
    }


def test_gate_passes_now() -> None:
    subprocess.run([sys.executable, str(SCRIPT), "gate"], check=True)


if __name__ == "__main__":
    for name, test in sorted(globals().items()):
        if name.startswith("test_") and callable(test):
            test()
            print(f"PASS {name}")
