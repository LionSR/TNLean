#!/usr/bin/env python3
"""Source-number and display regressions for campaign result tables.

Numbers follow Hastings 0705.2024v4, law16.tex, and LVV 1307.5143v1,
algo53.tex. The latter's original theorem counters give Definition 0.1,
Lemmas 1.1–1.8, and Claims/Lemmas/Corollaries in Section 2.
"""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "campaign_board"))
from collect import result_table


HEADER = """| Result | Label/name in the source | Issues | Completion: remaining work |
|---|---|---|---|"""

HASTINGS = HEADER + """
| Unnumbered theorem (area law) | No theorem label; equations `entbd` and `smd` | #9814 | Quantitative restriction |
| Lemma 1 (approximate factorization) | No lemma label; equation `prodapprox` | #9811 | Source-pair identification |
| Lemma 4 (Hermitian repair) | No lemma label | #9810 | Proved |
| Lemma 2 (bootstrap) | `ble` — bootstrap bound | #9813 | Quantitative restriction |
| Lindblad–Uhlmann step | Equation `LU` | #9812 | Proved |
| Matrix product state approximation | Unnumbered conclusion; equation `est` | #9815 | Quantitative restriction |
| Lemma 3 (Schmidt-diagonal correlations) | No lemma label; equation `fwdback` | #9816 | Positivity rate |
| Conjecture on completely positive maps | No internal label | — | Not a formalization target |
"""

LVV = HEADER + """
| Theorem 1 | `thm:main` — randomized ground-state algorithm | #9823 | Running time out of scope |
| Lemma 1.1 | `claim:energy-overlap` — energy controls overlap | #9817 | Overlap lemmas |
| Lemma 1.2 | `claim:overlap` — overlap transfer | #9817 | Overlap lemmas |
| Lemma 1.4 | `l:mpsapprox` — matrix product state approximation | #9840 | Sub-polynomial rank |
| Lemma 1.7 | `constantbondapprox` — constant rank at one cut | #9819 | Energy after trimming |
| Lemma 1.8 | `l:2` — energy after trimming | #9819 | Corrected constant |
| Corollary 1.9 | `c:1` — a low-energy constant-rank vector | #9819 | Corrected constant |
| Lemma 1.6 | `lem:eckart` — Eckart–Young theorem | #9818 | Trimming |
| Lemma 2.8 | `l:trim1` — trimming against a bounded-rank vector | #9818 | Trimming |
| Lemma 2.9 | `l:trim2` — ranks at other cuts | #9818 | Trimming |
| Lemma 2.3 | `l:gluing` — boundary contractions and gluing | #9820 | Gluing |
| Lemma 2.4 | `l:constantbondapprox` — a net of contractions | #9820 | Gluing |
| Claim 2.1 | `c:ext` — extension of a viable set | #9823 | Induction |
| Lemma 2.5 | `l:leading` — a leading eigenvector | #9820 | Gluing |
| Lemma 2.6 | `l:within` — a low-energy vector in the viable span | #9820 | Gluing |
| Claim 2.7 | `c:2` — cardinality reduction | #9820 | Gluing |
| Claim 2.10 | `c:trim` — bond-dimension trimming | #9823 | Induction |
| Power approximate projector | Equations `e:cutdown` and `e:decomp` | #9821 | Power estimate |
| Imported matrix concentration bound | `t:mcb` — imported from Tropp, not an LVV result | #9822 | Tropp Theorem 1.6, displayed as Theorem 2.13 in LVV |
| Corollary 2.14 | `c:agsp` (also `claim:sampling-agsp`) — sampled projector | #9822 | Sampling |
| Definition 0.1 | `def:viable` — viable set | #9823 | Induction |
| Claim 2.11 | `c:errorreduction` — error reduction | #9823 | Induction |
"""


class ResultTableTests(unittest.TestCase):
    def test_hastings_source_has_five_results_without_invented_labels(self):
        rows = result_table(HASTINGS)
        self.assertEqual([(r["kind"], r["num"], r["label"]) for r in rows], [
            ("Theorem", "", None), ("Lemma", "1", None), ("Lemma", "4", None),
            ("Lemma", "2", "ble"), ("Lemma", "3", None)])
        self.assertEqual([r["issues"] for r in rows], [[9814], [9811], [9810], [9813], [9816]])
        self.assertTrue(all(r["name"] for r in rows))

    def test_lvv_source_has_twenty_results_with_correct_work_issues(self):
        rows = result_table(LVV)
        self.assertEqual(len(rows), 20)
        self.assertEqual(sum(r["kind"] == "Claim" for r in rows), 4)
        by_label = {r["label"]: r for r in rows}
        self.assertEqual(by_label["constantbondapprox"]["num"], "1.7")
        self.assertEqual(by_label["c:agsp"]["num"], "2.14")
        self.assertEqual(by_label["c:agsp"]["issues"], [9822])
        self.assertNotIn("t:mcb", by_label)
        self.assertTrue(all(r["name"] and r["issues"] for r in rows))

    def test_only_issue_column_supplies_links(self):
        body = HEADER + "\n| Lemma 2 | `ble` — bootstrap | #9813 | PR #9997; compare Lemma 4 |"
        self.assertEqual(result_table(body)[0]["issues"], [9813])

    def test_legacy_tables_keep_their_number_label_and_name_rules(self):
        body = """| Result | Label/name | Issues | Completion |
|---|---|---|---|
| Theorem A | `thm:area` — area law | #9547 | Pending |
| Lemma 2.1 | `lem:tail` — spectral tail | #9813 #9836 | Proved |
| Claim 2.1 | `c:ext` — extension | #9823 | Pending |
| Lemma 2 | `ble` — bootstrap | #9813 | Pending |
"""
        rows = result_table(body)
        self.assertEqual([(r["kind"], r["num"], r["label"], r["name"], r["issues"]) for r in rows], [
            ("Theorem", "A", "thm:area", "area law", [9547]),
            ("Lemma", "2.1", "lem:tail", "spectral tail", [9813, 9836])])

    def test_explicit_table_does_not_affect_a_following_legacy_table(self):
        body = HASTINGS.rstrip("\n") + (
            "\n| Other | Source | Issues |\n|---|---|---|\n"
            "| Claim 3 | `c:other` | #9823 |"
        )
        self.assertEqual(len(result_table(body)), 5)

    def test_adjacent_different_headers_end_explicit_parsing(self):
        for header in ["| Other | Source | Issues |", "| Note | Description | Link |"]:
            for separator in ["|---|---|---|", "|:---|---:|:---:|", "|---|---|---"]:
                with self.subTest(header=header, separator=separator):
                    following = "\n".join([
                        header, separator,
                        "| Claim 3 | `c:other` | #9823 |",
                        "| Unnumbered Theorem | No source label | #9814 |",
                    ])
                    body = HASTINGS.rstrip("\n") + "\n" + following
                    self.assertEqual(result_table(body), result_table(HASTINGS))

    def test_adjacent_legacy_result_table_keeps_legacy_rules(self):
        following = """| Result | Label/name | Issues | Completion |
|---|---|---|---|
| Claim 3 | `c:other` — excluded | #9823 | Pending |
| Lemma 2 | `ble` — bare label | #9813 | Pending |
| Theorem A | `thm:area` — area law | #9547 | Pending |
"""
        rows = result_table(HASTINGS.rstrip("\n") + "\n" + following)
        self.assertEqual(rows[:5], result_table(HASTINGS))
        self.assertEqual([(r["kind"], r["num"], r["label"], r["issues"]) for r in rows[5:]],
                         [("Theorem", "A", "thm:area", [9547])])

    def test_separator_and_ignored_rows_preserve_explicit_parsing(self):
        body = HEADER + """
| Claim 1 | `c:first` — first claim | #9823 | Pending |
|---|---|---|---|
|:---|---:|:---:|---|
| Explanation | Not a source result | — | — |
| Claim 2 | `c:second` — second claim | #9823 | Pending |
"""
        self.assertEqual([r["label"] for r in result_table(body)], ["c:first", "c:second"])

    def test_adjacent_explicit_table_keeps_explicit_rules(self):
        following = HEADER + "\n| Claim 3 | `c:other` — another claim | #9823 | Pending |"
        rows = result_table(HASTINGS.rstrip("\n") + "\n" + following)
        self.assertEqual(rows[:5], result_table(HASTINGS))
        self.assertEqual([(r["kind"], r["num"], r["label"]) for r in rows[5:]],
                         [("Claim", "3", "c:other")])

    def test_browser_metadata_handles_unnumbered_and_unlabelled_results(self):
        # Evaluate the production metadata functions before any browser rendering.
        # Only the initial JSON read needs a DOM stand-in; the functions are pure.
        board = Path(__file__).resolve().parent / "campaign_board/board.js"
        kinds = ["Theorem", "Lemma", "Proposition", "Corollary", "Definition", "Remark", "Claim"]
        unnumbered = result_table(HEADER + "\n" + "\n".join(
            f"| Unnumbered {kind} (test result) | No source label | #9814 | Open gap |"
            for kind in kinds))
        self.assertEqual([r["kind"] for r in unnumbered], kinds)
        self.assertTrue(all(r["num"] == "" and r["label"] is None for r in unnumbered))
        js = r"""
const fs = require('fs'), vm = require('vm'), assert = require('node:assert/strict');
const source = fs.readFileSync(process.argv[1], 'utf8');
const prefix = source.slice(0, source.indexOf('  /* ---------- time ---------- */'));
const context = { document: { getElementById: () => ({textContent: '{"config":{}}'}) } };
vm.runInNewContext(prefix + '\nglobalThis.metadata = {resultHeading,resultName,resultSection,resultGapMatches};\n})();', context);
const f = context.metadata;
const main = {paper:'hastings',kind:'Theorem',num:'',label:null,name:'Area law'};
assert.equal(f.resultHeading(main), 'Theorem');
assert.equal(f.resultName(main), 'Area law');
assert.equal(f.resultSection(main), null);
assert.equal(f.resultSection({num:'0.1'}), 0);
assert.equal(f.resultSection({num:'2.14'}), 2);
assert.equal(f.resultSection({num:'A'}), null);
assert.equal(f.resultName({kind:'Lemma',num:'4',label:null}), 'Lemma 4');
assert(f.resultGapMatches(main, {paper:'hastings',result:'Main theorem, the doubling iteration'}));
assert(!f.resultGapMatches(main, {paper:'hastings',result:'Theorem 2, another result'}));
assert(!f.resultGapMatches(main, {paper:'lvv',result:'Main theorem, another paper'}));
const trim = {paper:'lvv',kind:'Lemma',num:'1.8',label:'l:2'};
assert(f.resultGapMatches(trim, {paper:'lvv',result:'Lemma l:2, energy of a trimmed state'}));
assert(f.resultGapMatches(trim, {paper:'lvv',result:'Lemma 1.8, energy of a trimmed state'}));
assert(!f.resultGapMatches(trim, {paper:'lvv',result:'Lemma 1.80, another result'}));
assert(!f.resultGapMatches(trim, {paper:'lvv',result:'Lemma 1.8.1, another result'}));
assert(!f.resultGapMatches(trim, {paper:'lvv',result:'Lemma l:2.1, another result'}));
const firstLemma = {paper:'hastings',kind:'Lemma',num:'1',label:null};
assert(f.resultGapMatches(firstLemma, {paper:'hastings',result:'Lemma 1, decay length'}));
assert(!f.resultGapMatches(firstLemma, {paper:'hastings',result:'Lemma 1.2, another result'}));
// Exercise every unnumbered kind admitted by the production table parser.
for (const row of JSON.parse(process.argv[2])) {
  const r = {...row, paper:'test-paper'};
  const match = result => f.resultGapMatches(r, {paper:r.paper, result});
  const prefix = `Unnumbered ${r.kind}`;
  for (const tail of ['', ', details', ' (details)', ': details', '— details', '   , details', '\t: details']) {
    assert(match(prefix + tail), `${prefix + tail} should match`);
  }
  assert(match(prefix.toLowerCase() + ', details'));
  for (const tail of ['ish', '.1', ' 2, numbered result', ' extra words', '; details']) {
    assert(!match(prefix + tail), `${prefix + tail} must not match`);
  }
  assert(!match(`Unnumbered ${r.kind === 'Claim' ? 'Lemma' : 'Claim'}, another kind`));
  assert(!f.resultGapMatches(r, {paper:'another-paper', result:prefix}));
  assert(!f.resultGapMatches({...r, num:'2'}, {paper:r.paper, result:prefix}));
  assert(!f.resultGapMatches(r, {paper:r.paper}));
  assert.equal(match('Main theorem, details'), r.kind === 'Theorem');
  assert.equal(match('Theorem, details'), r.kind === 'Theorem');
  if (r.kind !== 'Theorem') assert(!match(`${r.kind}, missing unnumbered qualifier`));
}
for (const prefix of ['Main theorem', 'Theorem']) {
  assert(f.resultGapMatches(main, {paper:main.paper, result:prefix}));
  for (const tail of ['ish', '.1', ' 2, another result', ' extra words']) {
    assert(!f.resultGapMatches(main, {paper:main.paper, result:prefix + tail}));
  }
}
console.log('Campaign result browser metadata: passed');
"""
        run = subprocess.run(["node", "-e", js, str(board), json.dumps(unnumbered)],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == "__main__":
    unittest.main()
