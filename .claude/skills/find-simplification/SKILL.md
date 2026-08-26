---
name: find-simplification
description: 'Use when working in TNLean to find non-obvious simplification candidates in the Lean development and record them as proof-debt ledger entries, `proof-debt` issues, or dated audit notes; especially for zero-reference declarations, pass-through wrappers, Mathlib shadows, hand-mirrored files, numbered-sequel scaffolding, stricter-hypothesis specializations kept beside their general theorem, degenerate-case apparatus, and parallel predicate families with bridge lemmas.'
---

# Finding TNLean Simplifications

This skill turns a broad "find things to simplify" request into evidence-backed candidates that remove or collapse existing Lean surface area. It is guidance, not a checklist: follow the imports, keep judgment active, and prefer a few proven candidates over a pile of thin guesses. The tournament workflows (`proof-debt-tournament`, `proof-shrink-tournament`) are the mass survey; this skill is the hand-driven version for a targeted directory, a PR review, or a weekly audit slice. `lean-simplifier` (plugin skill) executes a cleanup on a file once the candidate is chosen; this skill finds and proves the candidate.

## Start With Repo Context

- Read `docs/proof_debt.md` (the loop rules, the category table, "Deletion outranks abstraction") and the open sections of `docs/proof_debt_ledger.md`. A candidate that duplicates an open `D<n>`/`S<n>` entry is an evidence update to that entry, not a find.
- Read `CLAUDE.md` §"Degenerate readings are conventions, not gaps" and §"Faithfulness rule". They decide two recurring calls: degenerate-case apparatus is deletable by policy; a stricter-hypothesis theorem sitting beside a faithful one is a specialization, not the formalization.
- Read `docs/project_conventions.md` §Style: the pass-through exception lets a forwarding declaration go without a deprecation alias, provided non-`Archive` uses are migrated, no blueprint `\lean{...}` cites it, and the PR body plus an audit note name each removal.
- Skim `docs/audits/` for the area (filenames carry dates and issue numbers) — `*_pass_through*.md`, `*_dead_module_deletion.md`, and the `2026-08-23_nonzero_coefficient_convention.md` cleanup record what was already deleted, retained on purpose, or deferred to a tracked issue (e.g. #7135). Re-proposing a retained item must beat the recorded reason.
- Search `is:issue label:proof-debt` and `label:cleanup`, open *and* closed, plus the tracking issue (#4529) before writing anything new.

## Settled Surfaces — Do Not Propose Collapsing

Treat these as intentional by default; trimming an unused declaration *inside* one is fine, collapsing the seam is not:

- The QICLean boundary. Channel, spectral, Perron–Frobenius, and channel-generic Kraus/Wielandt theory live in the companion library; do not propose re-homing it here or re-implementing a QICLean API locally. The reverse direction — a TNLean lemma that QICLean already exports — is a strong candidate.
- The generated aggregators (`TNLean.lean`, per-directory `TNLean/X.lean` from `scripts/generate_import_aggregators.py`). Their import lists are a build artifact, not a consumer count: "imported only by the aggregator" is evidence of dead weight, not of use.
- The promoted tactics and simp sets in `TNLean/MPS/Tactic/Basic.lean` and the ledger in `docs/tactic_patterns.md`. Repetition below the rule of three is a *candidate* for that ledger, not a reason to add a tactic.
- `Archive/`. Excluded from root imports; it is neither a consumer nor a deletion target unless the user asks.
- Blueprint-cited declarations. Anything named by a `\lean{...}` tag under `blueprint/src/` is load-bearing until the blueprint entry is redirected to the survivor in the same PR.
- The `lakefile.toml` lean options and the CI file policies (`scripts/check_numbered_lean_files.py`, `scripts/check_oversized_lean_files.py`, `scripts/check_forbidden_lean_tokens.py`). Proposing to make a file *pass* them is welcome; proposing to loosen them is not.

## What Counts As A Strong Candidate

A strong simplification removes, folds, or demotes something real and has evidence that the current design costs more than it buys. Lean gives sharper evidence than most languages: a declaration's consumers are exactly the identifiers that elaborate against it.

- A theorem, definition, or structure with zero references outside its own declaration, excluding instances and `@[simp]`/`@[grind]`/`@[ext]`-tagged lemmas, and not cited by any blueprint `\lean{}` tag. Whole files reachable only through the generated aggregator are the file-level version.
- A pass-through: a declaration whose body is `exact foo _ _`, `foo.1`, a field projection, or a `simpa using` of one lemma, exported under a second name. `docs/project_conventions.md` makes these deletable without an alias.
- A Mathlib shadow: a local lemma provable by `exact?`/`simp` from Mathlib v4.34 alone, or a local definition Mathlib already has (`Matrix.trace_mul_comm`, `Finset.sum_comm`, `Matrix.IsHermitian`, `LinearMap.range`, …). Check `.lake/packages/mathlib/Mathlib/` and the Mathlib-replacement audits in `docs/audits/` (`*_mathlib_*_replacement_audit.md`) for what a toolchain bump already made available.
- A stricter-hypothesis theorem kept beside the faithful one: `foo_of_isNormal_leftCanonical` still present after `foo_of_isNormal` landed, with the special case a one-line corollary. Per the faithfulness rule the specialization is a different theorem; if nothing consumes it, it goes.
- Degenerate-case apparatus: `raw`/`active` predicate pairs with bridge lemmas, counterexample modules for a literal reading, `∀ k, μ k ≠ 0` hypotheses repeated downstream when the definition carries them, `\notready` "printed status" blueprint nodes. `CLAUDE.md` says to delete the scaffolding, not document it — but first check that the convention is actually forced by the definition, not merely suggested.
- Hand-mirrored developments: vertical/horizontal, left/right, red/blue files that are renames of each other (the ledger records 84 exact pairs), or a module docstring admitting "this file transposes X". One side plus a transport lemma (`PEPS/IsoTransport.lean`, `Matrix.reindex_*` in `TNLean/Algebra/MatrixReindex.lean`) is the candidate; reproving both is the debt.
- Numbered-sequel scaffolding after the capstone: `Foo2.lean`, `Foo3.lean`, `FooV2.lean`, `FooCore.lean`+`FooBridge.lean` chains whose intermediate lemmas have a single consumer in the next file. Inline the chain into the capstone or delete the abandoned branch; `scripts/check_numbered_lean_files.py` already forbids new ones.
- A parallel predicate or structure family (`IsFooA`/`IsFooB`, `Foo`/`Foo'`/`FooBundled`) with bridge lemmas in both directions and one member carrying all downstream traffic.
- A wrapper structure that bundles hypotheses only so one theorem can take a single argument, when the theorem has one caller.
- Proofs that reprove a general fact inline several times (`Matrix.mul_assoc` shuffles, `Finset.sum` reindexing, `Fin` case splits) because a helper lemma or simp lemma is missing; the candidate is the lemma, and the ledger for tactic-shaped repetition is `docs/tactic_patterns.md`.

Thin candidates are not enough: a single non-terminal `simp`, a stray `set_option`, "this proof is long" without a slicker argument in hand, or reformatting. Batch those into a hygiene PR or leave them.

## Survey Broadly

Use parallel subagents when the user asks for breadth. Give each agent one directory and require path:line evidence, not impressions. Useful slices for this repo:

- `MPS/Core`, `MPS/Chain`, `MPS/Overlap`: definitional API — duplicated `evalWord`/transfer lemmas, parallel canonical-form predicates.
- `MPS/FundamentalTheorem`, `MPS/CanonicalForm`, `MPS/BNT`, `MPS/Structure`: the forked general/special pairs and the ch23-style superseded routes.
- `PEPS/`: the largest mirror and sequel concentration (RegionBlock, CoarseThreeSite, vertical/horizontal pairs).
- `Wielandt/`, `Spectral/`, `Algebra/`: Mathlib shadows and QICLean shadows — lemmas that moved upstream but left a local copy.
- `MPS/MPDO`, `MPS/RFP`, `MPS/ParentHamiltonian`, `QCA/`: staged developments where the capstone landed and the staging did not leave.
- `blueprint/src/chapter/`: `\lean{}` tags pointing at a wrapper rather than the theorem, and `\notready` nodes beside a `\leanok` twin.

Do not let the first good candidate stop the survey. Start with the largest files and the files with the most importers: `python3 scripts/loc_report.py` and `python3 scripts/lake_build_hotspots.py` give the size and build-cost ranking; `rg -l "^import TNLean.X.Y" TNLean` gives the importer count of a module.

## Audit Hypotheses And Layer Boundaries

For every hypothesis on a candidate theorem, name where it is discharged downstream. A hypothesis that every caller discharges by the same lemma belongs inside the theorem; a hypothesis no caller can discharge (a bridge structure with no instance anywhere in the tree — the retired ch23 route's `SameStateBridgeHyp` was the precedent, ledger entry S5) marks the whole route as superseded. A hypothesis absent from the cited paper is a faithfulness defect, never elegance — check `docs/paper-gaps/` before touching it.

For every structure field, name a consumer that projects it. Fields read only by the structure's own constructor lemmas are staging.

For every layer crossing (`Algebra` → `MPS` → `PEPS`, TNLean → QICLean), check the direction. A lemma about bare matrices living under `MPS/` is a candidate to move down or to replace by its Mathlib/QICLean form; a lemma in `Algebra/` mentioning `MPSTensor` is mis-layered.

## Local Lemma Versus Mathlib Or QICLean

The default runs toward the upstream library: the project reuses Mathlib and QICLean lemmas rather than reproving them. For each local lemma that smells standard, try, in order: `exact?` on the statement with the local proof deleted; `rg` of the conclusion's head symbol under `.lake/packages/mathlib/Mathlib/` and `.lake/packages/qiclean/`; the Mathlib-replacement audits for the current toolchain. A local lemma that is a *strict* generalization of the Mathlib one, or that Mathlib states for a different carrier, stays — record why in its docstring if it is not already there.

A genuinely new Mathlib-shaped lemma can be the right answer when it deletes several local variants; state which variants it retires and whether it is upstreamable.

## Prove Or Reject Each Candidate

For every declaration, classify consumers before writing:

- Production corpus: `TNLean/` (excluding `Archive/`), `blueprint/src/` (`\lean{...}` tags), `scripts/*.lean`, and the docstrings of surviving declarations.
- Non-production corpus: `Archive/`, `docs/audits/` snapshots, `Notes/`, `Papers/`, comments.
- Ambiguous corpus: `docs/glossary.md` and `docs/paper-gaps/` — a declaration named there is a public predicate or a documented restriction; migrate the reference rather than counting it as a blocker.

Use `rg -w` on the exact name first, including the dot-suffixed forms callers use (`.foo`, `foo.symm`, `foo.mp`), then confirm by deleting the declaration and running `lake build TNLean.Path.To.Module` — Lean's consumer count is the elaboration result, not the grep. Use `lake build`, not `lake env lean`, when the answer depends on linter output (unused-variable, unused-simp-args, `docBlame`). For blueprint exposure run `cd blueprint && leanblueprint checkdecls` after the removal; for `#print axioms`-style integrity keep `rg -n "sorry|axiom"` on every touched file.

Reject or downgrade a candidate when:

- A production consumer exists and removing it would change what is proved (a feature decision, not a cleanup).
- The design is justified by a paper-gap note, a dated audit note, or a ledger entry marked retained, and the new evidence does not beat that reason.
- The removal forces unrelated churn — renames across dozens of files — without reducing the public surface or the hypothesis lists.
- The candidate is correct but tiny; batch it with related finds in one entry or one PR.
- The "simplification" is a net-positive-line abstraction. `docs/proof_debt.md` ranks deletion above abstraction; a net-positive refactor must name the future deletion it enables.

## Record The Candidate

Durable findings go to one of three places:

- **The proof-debt ledger** (`docs/proof_debt_ledger.md`) for a structural debt in the loop's category set — use the entry format in `docs/proof_debt.md` (status, verified evidence, remediation, first PR), placed in rank order, and attach a `proof-debt` issue as a sub-issue of the tracking issue (#4529).
- **A `proof-debt` (or `cleanup`) GitHub issue** for a bounded deletion: plain mathematical title, evidence with `path:line` citations and grepped-then-built consumer counts, estimated net line delta, risk level, blueprint tags to redirect. Dedupe against open and closed issues first; consolidate into the issue that owns the topic rather than filing a duplicate.
- **A dated audit note** under `docs/audits/yyyy-mm-dd_<topic>.md` when the finding needs an argument — a pass-through retirement decision, a retained-on-purpose ruling, a mirror-collapse plan — following the existing notes' style (what was checked, what is retained and why, what is deferred and to which issue).

Be concrete enough that an implementing PR can follow the trail: the declarations by full name, the survivor each maps to, the blueprint labels to redirect, and the net line estimate. One entry per durable candidate; do not pad the count.

## Validation And PR Hygiene

For record-only work (ledger, issue, audit note): `git diff --check` and the prose rules in the lean-conventions skill (no Lean identifiers in blueprint prose). For a deletion PR: `lake exe cache get` if the toolchain or a dependency moved, `lake build` clean with the package lean options, `rg -n "sorry|axiom"` on touched files, `python3 scripts/fetch_tenkz.py && cd blueprint && leanblueprint checkdecls` when a `\lean{}` tag was redirected, and `python3 scripts/loc_report.py` for the net line delta.

A PR implementing a simplification is titled `refactor(scope):` and its body states the net line delta (`docs/proof_debt.md` §shrink rhythm), the ledger entry or issue it burns down, each removed declaration with its replacement (the pass-through exception requires this plus an audit note), and any blueprint labels redirected. A removed name whose old spelling encoded banned terminology gets no deprecation alias; say so in the body. A burn-down PR that leaves "old and new side by side" is in-progress, not done, and carries the issue that removes the old side.

When reporting back, summarize: how many candidates went to the ledger, to issues, into existing records, or were rejected with evidence; the directories surveyed; what was excluded as settled; which checks passed.
