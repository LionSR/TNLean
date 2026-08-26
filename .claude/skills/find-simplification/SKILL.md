---
name: find-simplification
description: 'Use when working in TNLean to find non-obvious simplification candidates in the Lean development and record them as proof-debt ledger entries, `proof-debt` issues, or dated audit notes; especially for zero-reference declarations, pass-through wrappers, Mathlib shadows, hand-mirrored files, numbered-sequel scaffolding, stricter-hypothesis specializations kept beside their general theorem, degenerate-case apparatus, and parallel predicate families with bridge lemmas.'
---

# Finding Simplifications In A Lean Development

This skill turns a broad "find things to simplify" request into evidence-backed candidates that remove or collapse existing surface area. It is guidance, not a checklist: follow the dependencies, keep judgment active, and prefer a few proven candidates over a pile of thin guesses. The tournament workflows (`proof-debt-tournament`, `proof-shrink-tournament`) are the mass survey; this skill is the hand-driven version for a targeted directory, a PR review, or a weekly audit slice. `lean-simplifier` (plugin skill) executes a cleanup on a file once the candidate is chosen; this skill finds and proves the candidate.

## What Simplification Means

Simplification is the removal of structure that the problem does not demand. Every codebase accumulates two kinds of structure: the kind the subject forces (a theorem needs its hypotheses; a channel needs its Kraus operators) and the kind the *process* of building left behind — exploration branches, staging, defensive generality, copies made under deadline, seams built for a second consumer that never arrived. Only the second kind is simplifiable, and most of it hides in plain sight because each piece was reasonable when written.

The recurring shapes, in any language:

- **Dead weight.** Things with no consumer: unused exports, unreachable files, tests that pin retired behavior, documentation of deleted features. The cheapest wins; the only question is proving the absence of consumers.
- **Duplication.** The same fact represented twice — copied code, mirrored modules, a value re-derived at several call sites, two APIs for one concept with bridges between them. The fix is one owner; the risk is that the two copies drifted and one drift is load-bearing.
- **Speculative generality.** Parameters with one value, registries with one entry, abstractions with one implementation, configuration nobody sets. Generality is only free when it is used; otherwise it is a tax on every reader and every proof.
- **Indirection that only relocates complexity.** Wrappers, facades, factories, and helper layers that add a name without adding a decision. If the wrapper's body is a single call, the caller could make that call.
- **Scaffolding after the capstone.** Intermediate results, compatibility shims, migration paths, and staged variants kept after the thing they supported landed. These have an expiry date and rarely get one.
- **Special cases beside the general case.** The narrow version proved first, still present after the general version subsumed it. Whether it stays is a question of consumers, not sentiment.
- **Hand-rolled code the platform already provides.** A local reimplementation of a standard-library or well-maintained-dependency facility. The find is the exact upstream name it duplicates.
- **Degenerate-case apparatus.** Machinery for inputs the problem never produces: empty collections, zero dimensions, the null configuration. When the intended domain excludes the case, model the exclusion once in the definition and delete the machinery.

Three disciplines separate a find from a guess. **Consumers, not impressions**: classify every reference by whether it is production, test/doc, or ambiguous, and prove the count by the strongest available means (for code, by removing the thing and building). **Net, not gross**: count what the replacement adds — bridges, generalizations, migrations — against what leaves; a "simplification" that adds elements needs its justification built in. **Deletion outranks abstraction**: when a duplication can be resolved by abstracting or by deleting one side, the deletion is smaller, safer, and more honest about what is actually needed. And respect settled decisions: a design with a recorded rationale is challenged with new evidence, not re-litigated.

## How Simplification Looks In Lean

A proof assistant makes the shapes above unusually sharp, because a declaration's consumers are exactly the identifiers that elaborate against it, and a statement's content is exactly its hypotheses and conclusion.

- **Dead weight** is a declaration referenced only by itself, or a file reachable only through an import aggregator. The compiler is the oracle: delete it and build.
- **Duplication** is the same lemma re-proved under two names, or two developments related by a rename (left/right, row/column, one orientation of a lattice against the other) when a transport lemma would carry one to the other.
- **Speculative generality** is a typeclass or universe parameter instantiated once, or a bundled hypothesis structure with one instance. Its opposite is also debt: a *special-case* theorem kept after the general one landed, when the special case is a one-line corollary.
- **Indirection** is the pass-through: `exact foo`, a field projection, a `simpa using` of one lemma, exported under a second name.
- **Scaffolding** is the numbered-sequel chain (`Foo`, `Foo2`, `FooV2`, `FooCore`+`FooBridge`) whose intermediate lemmas each have one consumer in the next file, kept after the capstone theorem was proved.
- **Hand-rolled code** is the Mathlib shadow: a local lemma that `exact?` closes from the library alone, or a local definition the library already carries under another name. Library upgrades create new shadows silently.
- **Degenerate cases** are the `≠ 0`/`0 <` side conditions repeated on every downstream statement, the parallel `raw`/`active` predicate pair with bridge lemmas, and the counterexample module refuting a hyper-literal reading nobody intended.
- **Hypotheses** are their own category. A hypothesis every caller discharges by the same lemma belongs inside the theorem; a hypothesis no caller can discharge marks its whole route as superseded; a hypothesis absent from the cited source is not a simplification target at all but a faithfulness defect.

Three shapes are invisible to consumer counting, because counting starts from a declaration and asks who uses it. These start somewhere else:

- **Name collisions.** The same fully-qualified name declared in two modules that are both in the root import closure. Start from a *name* and count its **definitions**: walk `namespace`/`end`, prefix each declaration head, and report every name with more than one site. It is a thirty-line script and it finds duplications no reference table shows.
- **`private` re-declaration.** A `private` helper has no cross-module consumers by construction, so consumer counting can never judge it — and privacy is exactly what provokes a downstream file to re-declare the same helper. Compare private bodies across files in the same directory instead of counting them.
- **Unused imports.** The cheapest dead weight in a Lean repo and wholly invisible to a declaration survey: one import line can drag a multi-thousand-line compile cone into a module. For every import, name an identifier it supplies.

Two dialect notes on the shapes above. The sequel chain here is usually not `Foo2.lean` but a **hypothesis-strength suffix ladder** — `foo`, `foo_c1`, `foo_c1_pgvwc07`, `foo_c1_pgvwc07_of_dualFixedPoint` — where each suffix weakens a hypothesis and the unsuffixed root is the abandoned strict version; look for suffix ladders, not for digits. And a systematic name-pair is a **mirror only when a transport map exists** that carries one side to the other. Without one, the pair is content: the left/right families in `MPS/MPU` are the two source cuts of a single tensor, both stated by the source paper, and collapsing them would delete mathematics.

Proof text is the one place where "shorter" is not automatically simpler: a proof that became opaque to save lines is worse. The proof-level find is a missing helper or simp lemma that several proofs re-derive inline, not a golfed tactic block.

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

## Where The Shapes Live Here

Read the newest note in `docs/audits/` for your area **before** using this list. The counts below are snapshots from past tournaments, and the tree is swept often: a post-cleanup note names both the classes just removed and the ones deliberately deferred, which is the difference between an hour of dead-end grepping and two lines of rejection text. Treat every concentration named here as historical until that note confirms it.

The general shapes above, with the repo's known concentrations and the policy that makes each deletable:

- Zero-reference declarations (instances and attribute-carrying lemmas go to the build-checked batch rather than the candidate list; blueprint-tagged names are out): ledger entry S2 recorded ~185 across ~103 files as of 2026-07-20, since heavily swept. Files imported only by the generated aggregator are the file-level version.
- Pass-throughs: deletable without an alias under `docs/project_conventions.md` §Style, provided the PR body and an audit note name each removal with its replacement.
- Mathlib and QICLean shadows: check `.lake/packages/mathlib/Mathlib/`, `.lake/packages/qiclean/`, and the toolchain-bump audits `docs/audits/*_mathlib_*_replacement_audit.md`, which list what the current Mathlib newly provides.
- Stricter-hypothesis twins (`foo_of_isNormal_leftCanonical` beside `foo_of_isNormal`): the faithfulness rule in `CLAUDE.md` already classifies the twin as a different theorem; with no consumer it goes.
- Degenerate-case apparatus: `CLAUDE.md` §"Degenerate readings are conventions, not gaps" says delete the scaffolding, not document it — after checking that the definition actually forces the convention (a positivity field on one index says nothing about a triple).
- Mirrors: ledger entry D10 records 84 exact vertical↔horizontal rename pairs among PEPS top-level declarations; the left/right and blue/complement families are separate, uncounted. TNLean-local transport lives in `PEPS/IsoTransport.lean`. Matrix-level transport (`Matrix.reindex_mul_reindex` and friends) is QICLean's, so a TNLean copy of it is a deletion candidate rather than machinery to reuse locally.
- Numbered sequels: ~50 files / ~23k lines at the last count; `scripts/check_numbered_lean_files.py` forbids new ones, so the remaining chains are the target.
- Inline re-derivations (`Matrix.mul_assoc` shuffles, `Finset.sum` reindexing, `Fin` case splits): the candidate is the missing lemma; tactic-shaped repetition goes to `docs/tactic_patterns.md` instead.

Thin candidates are not enough: a single non-terminal `simp`, a stray `set_option`, "this proof is long" without a slicker argument in hand, or reformatting. Batch those into a hygiene PR or leave them.

## Survey Broadly

Use parallel subagents when the user asks for breadth. Give each agent one directory and require path:line evidence, not impressions. Useful slices for this repo:

- `MPS/Core`, `MPS/Chain`, `MPS/Overlap`: definitional API — duplicated `evalWord`/transfer lemmas, parallel canonical-form predicates.
- `MPS/FundamentalTheorem`, `MPS/CanonicalForm`, `MPS/BNT`, `MPS/Structure`: the forked general/special pairs and the ch23-style superseded routes.
- `PEPS/`: the largest mirror and sequel concentration (RegionBlock, CoarseThreeSite, vertical/horizontal pairs).
- `Wielandt/`, `Spectral/`, `Algebra/`: Mathlib shadows and QICLean shadows — lemmas that moved upstream but left a local copy.
- `MPS/MPDO`, `MPS/RFP`, `MPS/ParentHamiltonian`, `QCA/`: staged developments where the capstone landed and the staging did not leave.
- `blueprint/src/chapter/`: `\lean{}` tags pointing at a wrapper rather than the theorem, and `\notready` nodes beside a `\leanok` twin.

Do not let the first good candidate stop the survey. Start with the largest files and the files with the most importers: `python3 scripts/loc_report.py` gives the size ranking, and `lake build 2>&1 | tee /tmp/build.log` followed by `python3 scripts/lake_build_hotspots.py /tmp/build.log` gives the build-cost ranking (the script ranks jobs from a saved log and needs that path). `rg -l "^import TNLean.X.Y$" TNLean` gives the importer count of a module.

## Audit Hypotheses And Layer Boundaries

For every hypothesis on a candidate theorem, name where it is discharged downstream (the retired ch23 route's never-instantiated `SameStateBridgeHyp`, ledger entry S5, is the precedent for a hypothesis that condemns its whole route). A hypothesis absent from the cited paper is a faithfulness defect, never elegance — check `docs/paper-gaps/` before touching it.

For every structure field, name a consumer that projects it. Fields read only by the structure's own constructor lemmas are staging.

For every layer crossing (`Algebra` → `MPS` → `PEPS`, TNLean → QICLean), check the direction. A lemma about bare matrices living under `MPS/` is a candidate to move down or to replace by its Mathlib/QICLean form; a lemma in `Algebra/` mentioning `MPSTensor` is mis-layered.

## Local Lemma Versus Mathlib Or QICLean

The default runs toward the upstream library: the project reuses Mathlib and QICLean lemmas rather than reproving them. For each local lemma that smells standard, try, in order: `exact?` on the statement with the local proof deleted; `rg` of the conclusion's head symbol under `.lake/packages/mathlib/Mathlib/` and `.lake/packages/qiclean/`; the Mathlib-replacement audits for the current toolchain.

Search by the shape of the statement, not by the name. The two hardest shadows to find share no token with their upstream twin — `IsOrthogonalProjection.exists_support_isometry` against QICLean's `exists_range_isometry` is invisible to any name grep, and what found it was reading a bare-matrix lemma sitting in an MPS file and then grepping the conclusion's form (`Vᴴ * V = 1 ∧ V * Vᴴ`). Mathlib has a replacement-audit index per toolchain bump; QICLean has none, so its shadows must be hunted this way. A local lemma that is a *strict* generalization of the Mathlib one, or that Mathlib states for a different carrier, stays — record why in its docstring if it is not already there.

A genuinely new Mathlib-shaped lemma can be the right answer when it deletes several local variants; state which variants it retires and whether it is upstreamable.

## Prove Or Reject Each Candidate

For every declaration, classify consumers before writing:

- Production corpus: `TNLean/` (excluding `Archive/`), `blueprint/src/` (`\lean{...}` tags), `scripts/*.lean`, and the docstrings of surviving declarations.
- Non-production corpus: `Archive/`, `docs/audits/` snapshots, `Notes/`, `Papers/`, comments.
- Ambiguous corpus: `docs/glossary.md` and `docs/paper-gaps/` — a declaration named there is a public predicate or a documented restriction; migrate the reference rather than counting it as a blocker.

### Counting consumers without fooling yourself

Grep is the cheap filter and it is wrong by default in this codebase. Every rule below was paid for by a survey that reported live declarations as dead, or dead ones as live.

- **Search the final component, not the full name.** A declaration `Ns.Pred.foo` is invoked as `h.foo` or `W.foo`; the token `Ns.Pred.foo` never appears at the call site, so `rg -w 'Ns.Pred.foo'` returns zero for a lemma used three lines below. Match the last component with an optional dotted prefix and permit a leading `.`. The over-count from homonyms elsewhere is the safe direction — resolve it by reading the hits.
- **Beware the upstream twin.** Matching the bare final component over-counts systematically for exactly the shape you most want to find: TNLean mirrors QICLean names, so `Kraus.foo` and `MPSTensor.foo` share a suffix and the upstream calls look like local consumers. Accept a hit only when its namespace prefix is empty or a suffix of the declaring namespace.
- **Lean identifiers are not ASCII words.** Names here carry `σ`, `ₗ`, `₂`, `'`, `ᵀ`. `rg -w` and any hand-built `[A-Za-z0-9_]` class truncate them silently, turning `restrictSubRegionσ` into `restrictSubRegion` and manufacturing pages of false zeros. Use `rg -F` on the full name, and extract declaration names with a negated class such as `[^\s({\[:]+`.
- **Never `rg -F -f namelist`.** Ripgrep's leftmost-first alternation lets a short name shadow a longer one containing it, and the shadowed names come back with zero hits and no error. Loop one name at a time, or tokenize the corpus once and join against the declaration list.
- **Run a control.** Before trusting any counting pipeline, run it on a name you know is used, and on the declaration itself. A declaration always references itself, so **a count of zero is a bug in your matcher, never evidence.**
- **Subtract the module docstring.** Nearly every module here lists its results as backticked bullets under `## Main contents`, so a genuinely dead declaration scores 2, not 1. Strip doc comments and backticked spans before counting, or a naive `count > 0` filter discards your best finds.
- **Dead weight is a closure, not a grep.** Zero-reference declarations are only the tips: a dead subgraph keeps itself alive by internal references. Attribute every reference to its enclosing declaration, then iterate "dead if all its references live inside declarations already marked dead" to a fixpoint. In one area this took a find from 145 to 434 lines. Apply the same step *after* each deletion — removing a lemma strands the private helpers only it used.

### Blueprint exposure comes first

In a blueprint-heavy chapter the normal shape of a *finished* theorem is "no Lean consumer, one `\lean{}` tag". Ranking by reference count before intersecting with the tag set therefore wastes most of a survey — in `MPDO/Physical*`, 174 declarations have zero external Lean references and exactly two survive the intersection. Build the `\lean{}` tag set for the area first, intersect, then rank what remains.

Getting that census right needs care: tags wrap across lines with a LaTeX `%` continuation **inside** the braces, as in `\lean{MPOTensor.EtaLocalStructureData.%` followed by `    exists_...}`. A per-line grep and a naive `\lean\{([^}]*)\}` scan both miss these, and more than one survey nearly deleted a tagged theorem. Strip `%\s*\n\s*` before matching, then cross-check by grepping the bare short name across `blueprint/src/`.

Measure density before choosing a lens. Above roughly two-thirds tag coverage the tag-visible shapes are exhausted, and what remains is what a tag cannot name: `private` forwarders, structure-parent aliases, carrier restatements. Likewise, if an area's zero-reference rate is under about 2%, that lens is spent — pivot rather than grinding it.

### Then let the compiler answer

Grep proposes; elaboration decides. Confirm by deleting the declaration and rebuilding — the consumer count is the elaboration result.

Rebuild the right thing, though. `lake build TNLean.Path.To.Module` builds that module's *dependencies*, not its *importers*, so a declaration whose only consumer is downstream still elaborates cleanly and looks dead. The module target is the fast inner loop; the verdict needs a root `lake build` (or an explicit build of the reverse dependents, which `rg -l "^import TNLean.Path.To.Module$" TNLean` lists). A candidate proved dead only by a module-target build has not been proved dead.

Use `lake build`, not `lake env lean`, whenever the answer depends on linter output (unused-variable, unused-simp-args, `docBlame`): `lake env lean` drops the lakefile `leanOptions` and runs no linters.

This is also the only honest way to clear an attribute-carrying lemma. A `@[simp]`/`@[grind]`/`@[ext]` lemma with no named call site is not thereby alive — it may be firing inside a bare `simp`, or it may be unfireable (a `rfl` projection of a nine-argument constructor that never occurs fully applied). Grep cannot separate these, so do not silently exclude them: collect them into a build-checked batch, delete the attribute, and let the build rule. One area lost 240 deletable lines to treating the exclusion as a verdict.

When a survey is read-only and cannot build, settle a Lean semantics question — does dot notation resolve through `extends` into the parent structure? — with a five-line standalone probe file elaborated by `lake env lean` in the scratchpad, rather than by reasoning about it.

For blueprint exposure run `cd blueprint && leanblueprint checkdecls` after the removal; for proof integrity keep `rg -n "sorry|axiom"` on every touched file.

Reject or downgrade a candidate when:

- A production consumer exists and removing it would change what is proved (a feature decision, not a cleanup).
- The design is justified by a paper-gap note, a dated audit note, or a ledger entry marked retained, and the new evidence does not beat that reason. Check the same records for the *module path*, not only the declaration: an aggregator-only file is evidence of dead weight only after `docs/paper-gaps/` and `docs/audits/` come back empty for it.
- The deletion was already made and rolled back. `git log --diff-filter=D -- <path>` and a search of merge commits for the name cost one command and save re-proposing a decision the maintainer already reversed.
- The declaration sits in a counterexample or witness module whose docstring advertises it as the file's claim. An uncited lemma there is the point of the file, not scaffolding.
- It is a `@[deprecated]` declaration inside the transition window. The window is **six months** (lean-conventions, deprecation section); a deprecation dated last month has not expired, however dead it looks.
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

For record-only work (ledger, issue, audit note): `git diff --check` and the prose rules in the lean-conventions skill (no Lean identifiers in blueprint prose). For a deletion PR: `lake exe cache get` before the first build in any fresh, cloned, or cache-cleared worktree, and after any toolchain or dependency change — `CLAUDE.md`'s canonical cache rule is that Mathlib is never rebuilt from source, and skipping the fetch is what triggers the hours-long rebuild; then `lake build` clean with the package lean options, `rg -n "sorry|axiom"` on touched files, `python3 scripts/fetch_tenkz.py && cd blueprint && leanblueprint checkdecls` when a `\lean{}` tag was redirected, and `python3 scripts/loc_report.py` for the net line delta.

Two of the CI guards are **diff-scoped**, which makes them easy to miss and easy to misread:

```bash
python3 scripts/check_reader_facing_prose.py --root . --diff-base origin/main --ci
python3 scripts/check_forbidden_lean_tokens.py
```

Run them with the base ref, exactly as CI does. Both judge *added* lines, so they fail on a clean tree too — a bare run tells you nothing, and the pre-existing violations elsewhere in the tree are not yours to fix. Two consequences bite in practice. `check_reader_facing_prose.py` reads **committed** content when given `--diff-base`, so a fix in the working tree looks ineffective until it is committed. And `check_forbidden_lean_tokens.py` counts a *reworded* line as an addition: editing a sentence that happens to contain `sorry` — a docs table cell reading "sorry-free", say — trips it even though nothing new was introduced. When that happens, leave the original line untouched and put the correction in a neighbouring paragraph or a header.

The prose guard also settles where a follow-up gets recorded: Lean docstrings cite the mathematics, never an issue number. A migration issue belongs in the PR description, not in the module.

A PR implementing a simplification is titled `refactor(scope):` and its body states the net line delta (`docs/proof_debt.md` §shrink rhythm), the ledger entry or issue it burns down, each removed declaration with its replacement (the pass-through exception requires this plus an audit note), and any blueprint labels redirected. A removed name whose old spelling encoded banned terminology gets no deprecation alias; say so in the body. A burn-down PR that leaves "old and new side by side" is in-progress, not done, and carries the issue that removes the old side.

When reporting back, summarize: how many candidates went to the ledger, to issues, into existing records, or were rejected with evidence; the directories surveyed; what was excluded as settled; which checks passed.
