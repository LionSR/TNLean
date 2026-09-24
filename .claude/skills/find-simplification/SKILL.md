---
name: find-simplification
description: 'TNLean addendum to the texra-lean-skills `find-simplification` skill; load both when finding simplification candidates in TNLean and recording them as proof-debt ledger entries, `proof-debt` issues, or dated audit notes. Supplies the repository context the plugin skill asks for: the debt records, settled surfaces, known concentrations, QICLean shadows, and the validation commands.'
---

# Finding Simplifications In TNLean

The method lives in the plugin skill `texra-lean-skills:find-simplification`
(installed through `.claude/settings.json`; Codex users run the texra-lean-skills
`install.sh`): the shapes of removable structure and how each looks in Lean,
consumer counting and its grep pitfalls, blueprint-first ranking, proof by
build, the reject list, and recording. Load it first. This file supplies only
what that skill tells you to look up in the project.

The tournament workflows (`proof-debt-tournament`, `proof-shrink-tournament`)
are the mass survey; this skill is the hand-driven version for a targeted
directory, a PR review, or a weekly audit slice. `lean-simplifier` executes a
cleanup once the candidate is chosen.

## Project context to read first

- `docs/proof_debt.md` (the loop rules, the category table, "Deletion outranks
  abstraction") and the open sections of `docs/proof_debt_ledger.md`. A
  candidate that duplicates an open `D<n>`/`S<n>` entry is an evidence update
  to that entry, not a find.
- `CLAUDE.md` §"Degenerate readings are conventions, not gaps" and
  §"Faithfulness rule". They decide two recurring calls: degenerate-case
  apparatus is deletable by policy; a stricter-hypothesis theorem sitting
  beside a faithful one is a specialization, not the formalization.
- `docs/project_conventions.md` §Style: the pass-through exception lets a
  forwarding declaration go without a deprecation alias, provided non-`Archive`
  uses are migrated, no blueprint `\lean{...}` cites it, and the PR body plus
  an audit note name each removal. The exception covers pass-throughs,
  bundled-structure fields, and named proof steps, not results with
  independent mathematical content; those take the six-month deprecation
  window of the lean-conventions skill.
- `docs/audits/` for the area (filenames carry dates and issue numbers):
  `*_pass_through*.md`, `*_dead_module_deletion.md`, and the
  `2026-08-23_nonzero_coefficient_convention.md` cleanup record what was
  already deleted, retained on purpose, or deferred to a tracked issue (e.g.
  #7135). Check them for the *module path*, not only the declaration.
- `is:issue label:proof-debt` and `label:cleanup`, open *and* closed, plus the
  tracking issue (#4529).

## Settled surfaces

Trimming an unused declaration *inside* one of these is fine; collapsing the
seam is not.

- The QICLean boundary. Channel, spectral, Perron–Frobenius, and
  channel-generic Kraus/Wielandt theory live in the companion library; do not
  propose re-homing it here or re-implementing a QICLean API locally. The
  reverse direction — a TNLean lemma that QICLean already exports — is a
  strong candidate.
- The generated aggregators (`TNLean.lean`, per-directory `TNLean/X.lean` from
  `scripts/generate_import_aggregators.py`). "Imported only by the aggregator"
  is evidence of dead weight, not of use.
- The promoted tactics and simp sets in `TNLean/MPS/Tactic/Basic.lean` and the
  ledger in `docs/tactic_patterns.md`. Repetition below the rule of three is a
  *candidate* for that ledger, not a reason to add a tactic.
- `Archive/`: excluded from root imports; neither a consumer nor a deletion
  target unless the user asks.
- Blueprint-cited declarations under `blueprint/src/`, until the entry is
  redirected to the survivor in the same PR.
- The `lakefile.toml` lean options and the CI file policies
  (`scripts/check_numbered_lean_files.py`,
  `scripts/check_oversized_lean_files.py`,
  `scripts/check_forbidden_lean_tokens.py`). Making a file *pass* them is
  welcome; loosening them is not. These scripts stay repository-local; the
  plugin's `assets/` carries a generalized form for other projects, not a copy
  to keep in sync.

## Where the shapes live here

Read the newest note in `docs/audits/` for your area **before** using this
list. The counts are snapshots from past tournaments and the tree is swept
often; a post-cleanup note names both the classes just removed and the ones
deliberately deferred.

- Zero-reference declarations: ledger entry S2 recorded ~185 across ~103 files
  as of 2026-07-20, since heavily swept. Files imported only by the generated
  aggregator are the file-level version.
- Pass-throughs: deletable without an alias under the §Style exception above.
- Mathlib and QICLean shadows: `.lake/packages/mathlib/Mathlib/`,
  `.lake/packages/qiclean/`, and the toolchain-bump audits
  `docs/audits/*_mathlib_*_replacement_audit.md`. QICLean has no replacement
  index, so hunt its shadows by statement shape:
  `IsOrthogonalProjection.exists_support_isometry` against QICLean's
  `exists_range_isometry` shares no token with it and was found by grepping
  the conclusion's form (`Vᴴ * V = 1 ∧ V * Vᴴ`).
- Stricter-hypothesis twins (`foo_of_isNormal_leftCanonical` beside
  `foo_of_isNormal`): the faithfulness rule classifies the twin as a different
  theorem; with no consumer it goes.
- Degenerate-case apparatus: delete the scaffolding, after checking that the
  definition actually forces the convention (a positivity field on one index
  says nothing about a triple).
- Mirrors: ledger entry D10 records 84 exact vertical↔horizontal rename pairs
  among PEPS top-level declarations; the left/right and blue/complement
  families are separate, uncounted. TNLean-local transport lives in
  `PEPS/IsoTransport.lean`; matrix-level transport (`Matrix.reindex_mul_reindex`
  and friends) is QICLean's, so a TNLean copy of it is a deletion candidate.
  The left/right families in `MPS/MPU` are *not* mirrors: they are the two
  source cuts of a single tensor, both stated by the source paper.
- Numbered sequels: digit-suffixed files (~50 files / ~23k lines at the last
  count, policed by `scripts/check_numbered_lean_files.py`), and separately,
  hypothesis-strength suffix ladders on declaration names (e.g.
  `foo_c1_pgvwc07_of_dualFixedPoint`), which are file-invisible and found by
  searching for suffix ladders rather than digits.
- Superseded routes: the retired ch23 route's never-instantiated
  `SameStateBridgeHyp` (ledger entry S5) is the precedent for a hypothesis
  that condemns its whole route.
- Inline re-derivations (`Matrix.mul_assoc` shuffles, `Finset.sum` reindexing,
  `Fin` case splits): the candidate is the missing lemma; tactic-shaped
  repetition goes to `docs/tactic_patterns.md`.
- Layering: `Algebra/` holds tensor-network-facing compatibility results, so a
  generic matrix lemma parked there becomes the next QICLean shadow — upstream
  it to QICLean, or leave it where it is and record why. A lemma in `Algebra/`
  mentioning `MPSTensor` is mis-layered.

## Survey slices

- `MPS/Core`, `MPS/Chain`, `MPS/Overlap`: definitional API — duplicated
  `evalWord`/transfer lemmas, parallel canonical-form predicates.
- `MPS/FundamentalTheorem`, `MPS/CanonicalForm`, `MPS/BNT`, `MPS/Structure`:
  forked general/special pairs and superseded routes.
- `PEPS/`: the largest mirror and sequel concentration (RegionBlock,
  CoarseThreeSite, vertical/horizontal pairs).
- `Wielandt/`, `Spectral/`, `Algebra/`: Mathlib and QICLean shadows.
- `MPS/MPDO`, `MPS/RFP`, `MPS/ParentHamiltonian`, `QCA/`: staged developments
  where the capstone landed and the staging did not leave.
- `blueprint/src/chapter/`: `\lean{}` tags pointing at a wrapper rather than
  the theorem, and `\notready` nodes beside a `\leanok` twin.

Rank by `python3 scripts/loc_report.py` (size) and by build cost:
run the canonical build command from `CLAUDE.md` (`scripts/lake_build_locked.sh`
on macOS, or cache-fetch plus `lake build` on Linux) piped to `tee /tmp/build.log`,
then run `python3 scripts/lake_build_hotspots.py /tmp/build.log`.

## Consumer corpus and blueprint density

- Production: `TNLean/` (excluding `Archive/`), `blueprint/src/`, `scripts/*.lean`,
  and docstrings of surviving declarations. Nearly every module lists its
  results under `## Main contents`, so a dead declaration scores 2, not 1.
- Non-production: `Archive/`, `docs/audits/` snapshots, `Notes/`, `Papers/`.
- Ambiguous: `docs/glossary.md` and `docs/paper-gaps/` — migrate the reference.
- Blueprint tag census: the plugin's `lean_tag_census.py` and
  `scripts/blueprint_lean_sync.py::_split_lean_decls` agree on TNLean (8949
  names on 2026-09-24). In `MPDO/Physical*`, 174 declarations have zero
  external Lean references and exactly two survive the tag intersection.

## Validation and PR hygiene

- Record-only work (ledger, issue, audit note): `git diff --check` and the
  prose rules of the lean-conventions skill.
- Build only through the canonical build commands in `CLAUDE.md`: on macOS,
  route through `scripts/lake_build_locked.sh`; on Linux, fetch and verify the
  cache first before running `lake build`. The dead-code verdict needs the root
  build, not a module target.
- `python3 scripts/fetch_tenkz.py && cd blueprint && leanblueprint checkdecls`
  after a `\lean{}` redirect; without the fetch the check fails for missing
  setup and that reads like a clean "no tag" verdict.
- `python3 scripts/check_forbidden_lean_tokens.py`, bare, before each commit.
  Its `--base-ref` defaults to `HEAD`, so it checks the working tree; do not
  point it at a branch base, where its textual match fires on ordinary English
  ("adjacent factors admit…"). It runs in the auto-fix workflow, not in
  `pr-ci.yml`.
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base origin/<base> --ci`
  is the PR gate and judges only added lines, from **committed** content — a
  fix in the working tree looks ineffective until committed; run bare, it
  scans the whole tree and fails on others' violations. Its rule that bites a
  deletion PR: a Lean docstring cites the mathematics, never an issue number.
- Both guards count a reworded line as an addition: editing a sentence that
  contains `sorry` trips the token guard. Leave the original line and put the
  correction nearby.
- Records: ledger entries in `docs/proof_debt_ledger.md` use the entry format
  of `docs/proof_debt.md` (status, verified evidence, remediation, first PR),
  in rank order, with a `proof-debt` issue as a sub-issue of #4529; issues
  take plain mathematical titles; audit notes go to
  `docs/audits/yyyy-mm-dd_<topic>.md`.
- A simplification PR is titled `refactor(scope):` and its body states the net
  line delta (`docs/proof_debt.md` §shrink rhythm) and the ledger entry or
  issue it burns down. A removed name whose old spelling encoded banned
  terminology gets no deprecation alias; say so in the body.
