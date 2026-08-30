# CLAUDE.md

This file provides guidance to AI coding assistants working with code in this repository.

## Project Overview

TNLean is a Lean 4 formalization of the mathematics of tensor networks: matrix product states (MPS), their canonical forms and gauge structure, and the theorems that classify them — including the **Fundamental Theorem of Matrix Product States** and **Quantum Wielandt theory**. Built on Mathlib v4.34.0-rc1. The finite-dimensional quantum-channel theory this rests on (following Wolf's *Quantum Channels & Operations*) no longer lives in this repository; it is developed in the companion library [QICLean](https://github.com/LionSR/QICLean), which TNLean depends on. Blueprint diagrams are drawn by the companion package [tenkz](https://github.com/LionSR/tenkz), pinned from `tenkz.toml` and fetched with `python3 scripts/fetch_tenkz.py`.

## Build Commands and Mathlib Cache Policy

**Canonical cache rule:** never rebuild Mathlib from source in a fresh, cloned,
or cache-cleared worktree. After adding or updating a Mathlib dependency, fetch
its prebuilt artifacts **before** any `lake build` or local Lean check:

```bash
# Fetch pre-built Mathlib artifacts after a Mathlib/toolchain/dependency update.
# Do this before `lake build` or `lake env lean`; otherwise Mathlib can rebuild
# from source and take hours.
lake exe cache get

# Only after the cache fetch succeeds:
lake build
# Linter-bearing verification of one module (uses the package leanOptions):
lake build TNLean.Path.To.File
# Optional fast elaboration only; this does not use the package leanOptions:
lake env lean TNLean/Path/To/File.lean
```
# Check for sorrys/axioms in changed files
rg -n "sorry|axiom" TNLean/Path/To/File.lean || true

# Blueprint validation. Requires leanblueprint plus the pinned shared
# plasTeX plugin (blueprint/src/plastex.cfg loads it unconditionally):
#   pip install leanblueprint 'git+https://github.com/LionSR/texra-blueprint@v0.3.8'
# Run after lake build succeeds.
python3 scripts/fetch_tenkz.py
cd blueprint && leanblueprint checkdecls

# Blueprint web/PDF generation
cd blueprint && leanblueprint web
cd blueprint && leanblueprint pdf
```

## Lean Toolchain & Dependencies

- **Lean**: v4.34.0-rc1 (pinned in `lean-toolchain`)
- **Mathlib**: v4.34.0-rc1
- **checkdecls**: Blueprint declaration checker (PatrickMassot/checkdecls)
- **Gametheory**: Custom Brouwer fixed-point theorem library (LionSR/Brouwer)

### Lean Options (lakefile.toml)

- `relaxedAutoImplicit = false` — strict implicit arguments, no auto-implicit
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `weak.linter.mathlibStandardSet = true` — enables Mathlib's standard linters
  during `lake build`; the `weak.` value is a default that source options may
  override
- `maxSynthPendingDepth = 3` — typeclass synthesis depth limit

## Architecture

TNLean contains the tensor-network layers and depends on QICLean for matrix
analysis, topology, channel and entropy theory, quantum Perron--Frobenius and
spectral results, and channel-generic Kraus/Wielandt APIs. See
`docs/import_structure.md`; `TNLean.lean` is generated.

| Layer | Modules | Content |
|-------|---------|---------|
| **0** | `Algebra/` | Tensor-network-facing algebra and compatibility results not owned by QICLean |
| **3** | `MPS/Defs`, `MPS/Chain/`, `MPS/Core/`, `MPS/Overlap/` | MPSTensor definition, finite-Kraus compatibility wrappers, word evaluation, blocking, transfer matrices, overlap matrices |
| **4** | `MPS/FundamentalTheorem/`, `MPS/Symmetry/` | Single-block FT, gauge equivalence, on-site/virtual symmetries, cocycle coboundary |
| **5** | `MPS/BNT/`, `MPS/CanonicalForm/`, `MPS/Structure/`, `MPS/Irreducible/`, `MPS/Periodic/`, `MPS/FundamentalTheorem/Multi/` | Multi-block assembly, BNT canonical forms, permutation rigidity, periodic tensors |
| **5b** | `MPS/RFP/` | Renormalization fixed-point scaffolding |
| **6** | `Wielandt/` | Tensor-typed span-growth, primitivity, and Wielandt consequences built on QICLean |

**Other modules**: `PiAlgebra/` (pi-algebra FT variants), `PEPS/` (two-dimensional fundamental-theorem development for torus, cycle, and normal-tensor routes), `MPS/MPDO/` (density operator foundations), `QCA/` (quasi-local and cellular-automaton layer), `Spectral/` (MPS-specific transfer-operator gap and overlap-decay results), and `Archive/` (legacy, excluded from root imports).

### Key Types and Definitions

- `MPSTensor d D` — a `Fin d`-indexed family of `D*D` complex matrices
- `evalWord A w` — product of matrices along word `w : List (Fin d)`
- `IsInjective A` — matrices of `A` span the full matrix algebra
- `SameMPV A B` / `SameMPV₂` — same matrix product vector family
- `GaugeEquiv A B` — conjugation by invertible matrix (`B i = X * A i * X⁻¹`)
- `IsBNTCanonicalForm` — paper-faithful basis-of-normal-tensors canonical form predicate
- `cumulativeSpan A n` — span of all products of length <= n
- `IsNormal A` — the project's normality notion for Wielandt theory
- `transferMap A` — the CP map `rho -> sum_i A_i * rho * (A_i)^H`

## Conventions & Style Guides

Shared conventions (Mathlib style, naming, documentation, PR review, proof
integrity, prose style) live in the `lean-conventions` skill of
texra-ai/texra-lean-skills, auto-installed via `.claude/settings.json` —
consult the skill, and `docs/project_conventions.md` for TNLean-local
addenda. In particular, TNLean does not promise a stable public Lean API and
does not retain otherwise dead declarations solely as deprecated compatibility
aliases. Repo-specific conventions live in `docs/`; read the relevant file
before working in that area:

| File | Covers |
|------|--------|
| `lean-conventions` skill | Mathlib style, naming, documentation, PR review, proof integrity, prose style (canonical; installed) |
| [`docs/project_conventions.md`](docs/project_conventions.md) | TNLean-local addenda to the shared conventions |
| [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) | PR title format (`type(scope): description`), issue conventions, label taxonomy, review checklist, mathematical-language renames |
| [`docs/glossary.md`](docs/glossary.md) | Canonical public predicates, mathematical meanings, source anchors, sanctioned bridges, and caveats |
| [`docs/pr_review_management.md`](docs/pr_review_management.md) | PR triage process, comment API mapping, merge decisions |
| [`docs/blueprint_style_guide.md`](docs/blueprint_style_guide.md) | LaTeX conventions, `\lean{}`/`\leanok` tags, notation table, `\uses` rules, blueprint build commands |
| [`docs/ci-automation.md`](docs/ci-automation.md) | CI workflows, auto-fix loops, iteration caps, commit message conventions |
| [`docs/lake_build_cache.md`](docs/lake_build_cache.md) | Local Lake cache reuse and changed-module compilation-time limits |
| [`docs/tactic_development.md`](docs/tactic_development.md) | Tactic self-improvement loop: detecting repeated proof patterns, promotion criteria, design rules for custom tactics/simp sets |
| [`docs/tactic_patterns.md`](docs/tactic_patterns.md) | Living pattern ledger: promoted tactics, candidate patterns awaiting abstraction |
| [`docs/proof_debt.md`](docs/proof_debt.md) | Weekly proof-debt loop, ledger format, shrink rhythm; the `find-simplification` skill (`.claude/skills/`) is its hand-driven audit |

### Quick Reference (from the docs above)

- **PR titles**: `type(scope): description` -- types: `feat`, `fix`, `refactor`,
  `doc`, `style`, `ci`, `chore`; scope is shortened module path without
  `TNLean/` prefix
- **Issue titles**: plain mathematical titles, not `type(scope): ...`; use
  `Tracking: <area>` for trackers and keep titles bracket-free
- **Naming**: Definitions use `camelCase`, predicates use `IsPrefix`, and
  theorem names use underscore-separated components. An embedded definition
  keeps its `camelCase` spelling, while an embedded predicate is
  lower-camel-cased (`Is` becomes `is`). Internal word boundaries are never
  split, as in `evalWord_tensorProduct` and
  `isNormalTensor_of_isNormal_leftCanonical`.
  Files use `CamelCase.lean`.
- **Proof integrity blockers**: `sorry`, `admit`, `native_decide`, `unsafeCast`, `axiom`, circular reasoning
- **Blueprint prose**: Pure mathematics only — no Lean identifiers in text, no software jargon (see banned terms list in blueprint style guide)
- **Paper references**: Cite theorem numbers in docstrings (e.g., "Wolf Thm 6.3", "arXiv:1606.00608 Appendix A")
- **Mathematical renames**: When renaming a declaration whose old name encodes misleading terminology (banned vocabulary in the lean-conventions prose_style reference, §2), skip the `@[deprecated] alias` and state the reason in the PR body (see `docs/CONTRIBUTING.md` §Mathematical-language renames).

## Workflow

### Mathlib Scouting

When writing new proofs or closing sorrys, scout Mathlib first:
- Use `exact?`, `apply?`, `rw?`, `simp?` tactics
- Grep Mathlib source: `.lake/packages/mathlib/Mathlib/` for related definitions/theorems
- Reuse Mathlib lemmas rather than reproving from scratch
- Not needed for cosmetic fixes, docstrings, imports, or renaming

### Tactic Self-Improvement Loop

Proof text must grow sublinearly with mathematical content: a tactic pattern
paid for three times gets abstracted, not copied a fourth time. The full
process is in `docs/tactic_development.md`; the pattern ledger is
`docs/tactic_patterns.md`. In every proof-writing session:

1. **Consult** the ledger's promoted section first and use existing custom
   tactics/simp sets (`mpv_ext`, `transfer_simp` in
   `TNLean/MPS/Tactic/Basic.lean`) where they apply — hand-writing a pattern
   that has a promoted tactic is a review-blocking style issue.
2. **Detect** repetition while writing, and in proof-heavy PRs run:

   ```bash
   python3 scripts/tactic_pattern_scan.py
   ```

3. **Record** noticed repetition as a candidate entry in the ledger — in the
   same PR; recording is cheap and needs no design decision.
4. **Promote** when a pattern hits ≥ 3 occurrences across ≥ 2 files (rule of
   three): prefer a lemma, then a simp set, then `@[grind]` annotations +
   `grind` for goal-closing patterns, then a macro, then an elab tactic
   (weakest mechanism that removes the duplication). Refactor the known call
   sites and update the ledger entry.

### Blueprint Updates

When adding or completing (removing sorry from) theorems/lemmas:
1. Update the corresponding entry in `blueprint/src/chapter/*.tex`
2. Add `\lean{DeclarationName}` and `\leanok` tags for new results
3. Add `\leanok` to `\begin{proof}` for newly proven results
4. Validate with `lake build` then `leanblueprint checkdecls`

### General Rules

- Prefer minimal diffs
- Do not leave unrelated new sorrys
- Before changing theorem statements, first try to complete the proof using existing lemmas
- If a mathematical result looks wrong or suspiciously general, check the LaTeX sources in `Papers/` and `Notes/` for the original theorems

### Faithfulness rule

**A theorem is "formalized" only when its Lean signature has no hypothesis
absent from the cited source's statement.** Adding hypotheses — even
mathematically natural ones — produces a *different* theorem and must
not be marked `\leanok` against the source's blueprint label.

This applies to every formalized result, not only those undergoing active
paper-realignment. The check is on hypotheses, not just conclusions:

- A Lean theorem whose conclusion matches the source but whose hypotheses
  are stricter than the source's is **not** the formalization of the source
  theorem. It is a different theorem (a corollary or specialization).
- The blueprint label citing the source must point to a Lean statement
  with the source's hypothesis set, not to a stronger-hypothesis variant.
- If the only available Lean theorem has extra hypotheses, the blueprint
  must either: (a) drop the `\leanok` and `\lean{...}` tags from the
  source-labelled entry, or (b) state the source's theorem as a
  separate blueprint entry with `\leanok` only after a faithful Lean
  version exists.

Scope-restricted theorems may be marked `\leanok` only against a blueprint
statement that explicitly states the restriction. Such an entry must not be
presented as the source theorem itself. The unrestricted source theorem remains
unformalized until a Lean statement with the source's hypothesis set exists.

A paper-gap note in `docs/paper-gaps/` is required whenever a
stricter-hypothesis Lean version is the *only* available formalization of
a source theorem. The note must identify the missing hypothesis and the
elimination plan (formalize the source-faithful version, derive the
stricter version inside a particular argument, etc.).

When the formalization of the source theorem lives in the QICLean
companion library, the required note lives in QICLean's `docs/paper-gaps/`
collection instead of this repository's (the Wolf notes were consolidated
there by #6906). TNLean must still reference the note wherever the
restriction is load-bearing: blueprint prose cites `\cite{gap:<slug>}`
with a bibliography entry carrying the published URL; docstrings and
`docs/` files cite the published URL directly. A local copy of a
QICLean-owned note must not be reintroduced.

This rule was retroactively codified after the equalMPS audit
(`docs/paper-gaps/cpsv16_equalMPS_gauge_phase_gap.tex`) found that the
proportionality-conditional Lean theorem was being treated as the
formalization of the proportionality-free source lemma.

### Paper-realignment mode

When the formalization has drifted from the cited source and the work is
**realigning the Lean development to the paper** (replacing wrong hypotheses,
removing divergent structures, restating theorems to match the source), the
default `sorry`/`axiom` blockers from the lean-conventions proof-integrity rules are temporarily
relaxed. The priority is **getting the statements right**; proofs are
restored after.

#### Source-citation requirement

In paper-realignment mode every restated definition, hypothesis field, or
theorem **must carry a docstring referencing the source by paper label or line
range**. The minimum acceptable forms:

- `arXiv:1606.00608, eq:II_CF1` — equation/theorem label
- `arXiv:1606.00608, lines 1170–1192` — line range in the local source PDF/tex
- `CPSV16, Lemma Lem1` — paper short name plus internal label
- `Wolf §6.2` — published section reference

For Lean fields and theorems whose mathematical content is being aligned to a
specific paper passage, the docstring must say *which* passage. Inline
identifiers without a source reference are unreviewable in this mode: a
reviewer cannot tell whether the field/theorem is faithful or invented.

This rule applies whether or not the proof is `sorry` — the *statement* is
the load-bearing artifact during realignment.

#### Marking unfaithful theorems

A theorem or lemma is **unfaithful** when its proof relies on a hypothesis or
intermediate lemma that is known to deviate from the cited source — typically
because the hypothesis was smuggled into the formalization, the proof
shortcuts a load-bearing source step, or the result is restated more weakly
than the paper would prove. Unfaithful theorems must carry a docstring
marker so a future reader (or a follow-up PR) can locate them.

The marker is a docstring section starting with `**Unfaithful:**` that names
the load-bearing deviation, cites the paper-gap note documenting it, and
sketches the elimination plan. Minimum form:

```
**Unfaithful:** This proof currently relies on `<hypothesis or lemma>`,
which deviates from `<paper, label or line range>`. Documented in
`docs/paper-gaps/<note>.tex`. Elimination: replace by `<faithful
substitute>`; tracked in `<issue or PR>`.
```

The marker propagates to dependent theorems: any theorem whose proof
transitively calls an unfaithful one is itself unfaithful and must carry its
own marker. The marker is removed only when every transitively-cited
dependency is faithful.

Reviewers should not approve a paper-realignment PR that introduces an
unfaithful theorem without the marker. The marker makes the deviation
auditable and keeps the elimination plan visible.

#### Locally-fixable deviations

Not every paper deviation rises to **Unfaithful**. When the cited source
contains a small typo, a locally-fixable gap (a missing or off-by-one
constant, a clarification needed at one step), or a scope restriction that
the paper proves more generally but the local result handles only a
sub-case, the formalization may proceed without the full **Unfaithful**
ceremony. These cases must still:

- Cite a paper-gap document (under `docs/paper-gaps/`) that records the
  deviation in mathematical terms; if no note exists, write a short one
  before merging.
- Use a lighter-weight in-source marker. The recommended forms are
  `**Scope restriction (...):**` for sub-case proofs, or
  `**Local fix (...):**` for typo/constant adjustments. Both forms must
  reference the paper-gap document by file path.
- Be inline-readable: the marker should let a reader recognize the
  deviation without leaving the file.

The **Unfaithful** marker is reserved for deviations that would be
mathematically wrong without follow-up work (the proof is unprovable, or
the statement smuggles an unwarranted hypothesis). The lighter markers
are for deviations that are mathematically correct as stated, just
narrower or differently phrased than the source.

#### Degenerate readings are conventions, not gaps

A source definition read hyper-literally often admits a degenerate case
that its authors plainly do not intend: a canonical-form summand with
coefficient zero, a basis member that contributes nothing at every
length, a sector of probability zero, an empty block padding the bond
dimension. Such a reading is **not** a faithfulness gap. The intended
reading is adopted as the library's convention, baked into the definition
(a `≠ 0` or `0 <` field), and recorded once as a **Local fix** with a
one-page paper-gap note. The convention must not be modeled:

- no parallel predicate families (`raw` versus `active`, `literal` versus
  `normalized`) with bridge lemmas between them;
- no counterexample modules refuting the literal reading;
- no `\notready` "printed status" blueprint nodes beside the formalized
  theorem;
- no side hypotheses (`∀ k, μ k ≠ 0`) repeated on every downstream
  statement when the definition already carries them;
- no per-declaration marker stamped across a whole module; one marker on
  the definition or in the module docstring suffices.

The marker rule applies to every marker family, not only degenerate
readings: one `**Scope restriction**` or `**Local fix**` marker per
(restriction, module), placed on the module docstring or the defining
declaration; a per-declaration marker is justified only when that
declaration's restriction differs from the module's.

Consolidation is per module, and the surviving marker stays
self-contained: it states the deviation and cites the paper-gap note by
path, so the module remains auditable on its own. A sentence naming
another Lean module is not a marker. A consolidated marker must also
claim no more than it covers: when only some declarations of a module
carry the restriction, name them or leave the marker on them, rather
than asserting it of the whole module.

Every item on that list multiplies downstream statements and hypothesis
lists and makes further proof writing harder. When an audit finds such a
reading, the repair is to delete the scaffolding, not to document it.
The 2026-08-23 nonzero-coefficient cleanup
(`docs/audits/2026-08-23_nonzero_coefficient_convention.md`) removed
about 2,300 lines built around one such reading.

A genuine source error is different: a printed claim that fails on
nondegenerate data (an explicit tensor with nonzero weights, a wrong
exponent, an off-by-one chain length) keeps its counterexample and its
**Local fix** or **false-source** record.

Two limits keep the convention from swallowing real content.

First, silence is not always an omission. Before reading a qualifier into
a definition, check whether the source attaches that same qualifier
explicitly at comparable statements. If it does, its absence here is a
choice, the unrestricted reading is the faithful one, and supplying the
qualifier would add a hypothesis the source does not carry. A witness
that the unrestricted definition admits is then a genuine witness, and
its counterexample stays.

Second, the convention must actually be in the definition before the
apparatus modeling it is deleted. Deleting a counterexample while the
predicate still admits its witness leaves the predicate wrong and the
gap invisible. Check what the structure forces rather than what it
suggests: a positivity field indexed by one label does not constrain a
family indexed by a triple, and a field that constrains entries says
nothing about an empty index.

A paper-realignment PR may:

- Delete fields, hypotheses, or whole theorems that are documented as
  divergent from the cited source (with the divergence recorded in
  `docs/paper-gaps/`).
- Leave `sorry` in proof bodies whose old proof depended on the deleted
  data, when the paper-faithful replacement is the next step.
- Cascade signature changes through downstream consumers, also using
  `sorry` if necessary, rather than reverting to keep the build proof-clean.

A paper-realignment PR must:

- Cite the relevant `docs/paper-gaps/*.tex` note documenting the divergence
  in the PR description.
- Identify, in the PR description, every `sorry` introduced and the
  paper-faithful theorem that will discharge it.
- Be scoped tightly — no unrelated refactors or feature additions.
- Be followed by tracked implementation issues for the missing
  paper-faithful proofs.

In paper-realignment mode the standard "do not add sorry" rule is the
*wrong* heuristic: keeping a divergent proof intact to avoid `sorry`
preserves a result the source does not assert. Reviewers should evaluate
paper-realignment PRs against the paper-gap note and the planned
follow-up, not against the temporary `sorry` count.

## Lean proof automation ledger

| Name | Kind | Use when | Defined in |
|---|---|---|---|
| `List.ofFn_reverse` | helper theorem | Reversing a `List.ofFn`-indexed finite word by precomposition with `Fin.rev` | `QICLean/Kraus/Word.lean` (QICLean dependency) |
| `verticalAssembledTensor_apply_copy_same` | helper theorem | Evaluating an assembled vertical tensor at two coordinates in the same retained multiplicity copy | `TNLean/MPS/MPDO/VerticalSectorCoordinates.lean` |
| `exists_blockDiagonal_boundary_chainGroundSpace_of_global_cut_of_openBoundary` | helper theorem | Closing block-diagonal boundaries from an open-boundary representation and a simultaneous span across the complementary global cut | `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean` |
| `BlockSumGroundSpace.exists_blockDiagonal_boundary_of_mem_iSup_groundSpace` | helper theorem | Assembling membership in the sum of open-boundary block spaces into one weighted block-diagonal boundary matrix | `TNLean/MPS/ParentHamiltonian/BlockSumGroundSpace.lean` |
| `SpinChain.quasiLocalTranslation_mul` | helper theorem | Rewriting a product of quasi-local translations as translation by the reversed sum of displacements | `TNLean/QCA/QuasiLocalTranslation.lean` |
| `SpinChain.quasiLocalTranslation_inv` | helper theorem | Rewriting the group inverse of a quasi-local translation as translation by the negative displacement | `TNLean/QCA/QuasiLocalTranslation.lean` |
| `SpinChain.quasiLocalTranslation_one` | helper theorem | Rewriting the identity automorphism as quasi-local translation by zero | `TNLean/QCA/QuasiLocalTranslation.lean` |
| `Kraus.map_compressed_fixedPoint` | helper theorem | Preserving a supported fixed point under finite-Kraus compression along an isometry | `QICLean/Channel/KrausCornerCompression.lean` (QICLean dependency) |
| `MPSTensor.eq_zero_of_forall_trace_mul_right_eq_zero` | helper theorem | Concluding that a matrix is zero from vanishing trace pairings against every one-site matrix of an injective tensor | `TNLean/MPS/Core/TracePairing.lean` |
| `MPOTensor.IsSAL.physTraceTransfer_ne_zero` | helper theorem | Deriving nonvanishing of the one-site physical-trace transfer from the positive-length normalization clause in saturation of the area law | `TNLean/MPS/MPDO/SALTraceTransfer.lean` |
| `Finset.sum_eq_sum_subtype_ne_zero` | helper theorem | Restricting a finite sum to the subtype where a weight is nonzero when the remaining summands vanish | `TNLean/Algebra/FinsetSubtypeSum.lean` |
| `Complex.ofReal_sqrt_sq` | helper theorem | Squaring the complex coercion of a nonnegative real square root | `TNLean/Algebra/ComplexSqrt.lean` |
| `Matrix.IsIsometry.kronecker` | helper theorem | Preserving matrix isometries under the Kronecker product | `QICLean/Algebra/MatrixIsometryKronecker.lean` (QICLean dependency) |
| `Matrix.reindexLinearEquiv_mul` | helper theorem | Multiplying matrices transported along compatible row, middle, and column equivalences; instantiate all three equivalences explicitly | `Mathlib/LinearAlgebra/Matrix/Reindex.lean` |
| `Matrix.entry_eq_of_heq` | helper theorem | Equating entries of a dependent family of matrices from the index equation and two heterogeneous coordinate identifications | `TNLean/MPS/MPDO/PhysicalSectorFactorization.lean` |
| `MPSTensor.cyclic_projection_mul_left` | helper theorem | Multiplying out the adjoint transfer map applied to a cyclic-sector projection times an arbitrary matrix, instead of rebuilding the Kadison–Schwarz multiplicative-domain argument | `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` |
| `MPSTensor.cyclic_projection_mul_right` | helper theorem | The same on the other side: the adjoint transfer map applied to an arbitrary matrix times a cyclic-sector projection | `TNLean/MPS/Periodic/SectorIrreducibility/HLift.lean` |
| `Fin.cyclic_induction` | helper theorem | Proving a predicate on a finite cyclic index from the zero case and one step of adding one, instead of re-running the induction on the underlying natural number | `TNLean/Algebra/FinCyclicInduction.lean` |
| `LinearMap.exists_smulRight_of_finrank_range_eq_one` | helper theorem | Factoring a linear map with one-dimensional range into a scalar functional and a normalized nonzero range vector | `TNLean/Algebra/RankOneFactorization.lean` |
