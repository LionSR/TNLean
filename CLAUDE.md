# CLAUDE.md

This file provides guidance to AI coding assistants working with code in this repository.

## Project Overview

TNLean is a Lean 4 formalization of the **Fundamental Theorem of Matrix Product States**, **Quantum Wielandt theory**, and finite-dimensional **quantum-channel theory** (following Wolf's *Quantum Channels & Operations*). Built on Mathlib v4.29.0.

## Build Commands

```bash
# Fetch pre-built Mathlib oleans (run once, or after toolchain/dependency updates)
lake exe cache get

# Full build
lake build

# Check a single file (fastest feedback loop)
lake env lean TNLean/Path/To/File.lean

# Check for sorrys/axioms in changed files
rg -n "sorry|axiom" TNLean/Path/To/File.lean || true

# Blueprint validation (requires leanblueprint; run after lake build succeeds)
cd blueprint && leanblueprint checkdecls

# Blueprint web/PDF generation
cd blueprint && leanblueprint web
cd blueprint && leanblueprint pdf

```

## Lean Toolchain & Dependencies

- **Lean**: v4.29.0 (pinned in `lean-toolchain`)
- **Mathlib**: v4.29.0
- **checkdecls**: Blueprint declaration checker (PatrickMassot/checkdecls)
- **Gametheory**: Custom Brouwer fixed-point theorem library (LionSR/Brouwer)

### Lean Options (lakefile.toml)

- `relaxedAutoImplicit = false` — strict implicit arguments, no auto-implicit
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `maxSynthPendingDepth = 3` — typeclass synthesis depth limit

## Architecture

The source lives in `TNLean/` and is organized into **layers 0-6 with sublayers** (see `TNLean.lean` for the full import graph):

| Layer | Modules | Content |
|-------|---------|---------|
| **0** | `Algebra/`, `Analysis/`, `Topology/`, `Axioms/` | Matrix lemmas, trace pairings, Gram matrices, Frobenius norms, Skolem-Noether, cocycle cohomology, Brouwer FPT |
| **1-2** | `Channel/` (Basic, Choi, Kraus, Stinespring, Transfer) | Quantum channel representations (Wolf Ch. 2) |
| **2b-2c** | `Channel/Schwarz/`, `Channel/FixedPoint/`, `Channel/Irreducible/`, `Channel/Peripheral/`, `Channel/Semigroup/`, `QPF/`, `Spectral/` | Kadison-Schwarz, Perron-Frobenius, spectral theory, peripheral spectrum, GKSL semigroups (Wolf Ch. 5-7) |
| **3** | `MPS/Defs`, `MPS/Chain/`, `MPS/Core/`, `MPS/Overlap/` | MPSTensor definition, word evaluation, blocking, transfer matrices, overlap matrices |
| **4** | `MPS/FundamentalTheorem/`, `MPS/Symmetry/` | Single-block FT, gauge equivalence, on-site/virtual symmetries, cocycle coboundary |
| **5** | `MPS/BNT/`, `MPS/CanonicalForm/`, `MPS/Structure/`, `MPS/Irreducible/`, `MPS/Periodic/`, `MPS/FundamentalTheorem/Multi/` | Multi-block assembly, BNT canonical forms, permutation rigidity, periodic tensors |
| **5b** | `MPS/RFP/` | Renormalization fixed-point scaffolding |
| **6** | `Wielandt/` | Span-growth, rank-one extraction, rectangular span, Wielandt bound, primitivity equivalences |

**Other modules**: `PiAlgebra/` (pi-algebra FT variants), `PEPS/` (exploratory), `MPS/MPDO/` (density operator foundations), `Archive/` (legacy, excluded from root imports), `Scratch/` (experimental).

### Key Types and Definitions

- `MPSTensor d D` — a `Fin d`-indexed family of `D*D` complex matrices
- `evalWord A w` — product of matrices along word `w : List (Fin d)`
- `IsInjective A` — matrices of `A` span the full matrix algebra
- `SameMPV A B` / `SameMPV₂` — same matrix product vector family
- `GaugeEquiv A B` — conjugation by invertible matrix (`B i = X * A i * X⁻¹`)
- `IsCanonicalFormBNT` — basis-normal-triangular canonical form predicate
- `cumulativeSpan A n` — span of all products of length <= n
- `IsNormal A` — the project's normality notion for Wielandt theory
- `transferMap A` — the CP map `rho -> sum_i A_i * rho * (A_i)^H`

## Conventions & Style Guides

Detailed conventions live in `docs/`. Read the relevant file before working in that area:

| File | Covers |
|------|--------|
| [`docs/MATHLIB_style.md`](docs/MATHLIB_style.md) | Code formatting, line length (100 chars), declarations, tactic style, whitespace, transparency, deprecation |
| [`docs/MATHLIB_naming.md`](docs/MATHLIB_naming.md) | Capitalization rules, symbol-to-name dictionary, variable conventions |
| [`docs/MATHLIB_doc.md`](docs/MATHLIB_doc.md) | Module docstrings, definition docstrings, sectioning comments, BibTeX citations |
| [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) | PR title format (`type(scope): description`), issue conventions, label taxonomy, review checklist, mathematical-language renames |
| [`docs/MATHLIB_pr-review.md`](docs/MATHLIB_pr-review.md) | Review criteria: style, documentation, location, improvements, library integration |
| [`docs/pr_review_management.md`](docs/pr_review_management.md) | PR triage process, comment API mapping, merge decisions |
| [`docs/PROOF_INTEGRITY.md`](docs/PROOF_INTEGRITY.md) | Blockers (`sorry`, `axiom`, kernel bypasses, circular reasoning) and warnings (`maxHeartbeats`, debug artifacts) |
| [`docs/blueprint_style_guide.md`](docs/blueprint_style_guide.md) | LaTeX conventions, `\lean{}`/`\leanok` tags, notation table, `\uses` rules, blueprint build commands |
| [`docs/prose_style.md`](docs/prose_style.md) | Prose conventions: no Lean jargon in the leanblueprint, banned software-engineering terms, banned LLM writing patterns (applies to `.tex` AND Lean docstrings/comments) |
| [`docs/ci-automation.md`](docs/ci-automation.md) | CI workflows, auto-fix loops, iteration caps, commit message conventions |

### Quick Reference (from the docs above)

- **PR titles**: `type(scope): description` -- types: `feat`, `fix`, `refactor`,
  `doc`, `style`, `ci`, `chore`; scope is shortened module path without
  `TNLean/` prefix
- **Issue titles**: plain mathematical titles, not `type(scope): ...`; use
  `Tracking: <area>` for trackers and keep titles bracket-free
- **Naming**: Definitions `camelCase`, predicates `IsPrefix`, theorems `snake_case`, files `CamelCase.lean`
- **Proof integrity blockers**: `sorry`, `admit`, `native_decide`, `unsafeCast`, `axiom`, circular reasoning
- **Blueprint prose**: Pure mathematics only — no Lean identifiers in text, no software jargon (see banned terms list in blueprint style guide)
- **Paper references**: Cite theorem numbers in docstrings (e.g., "Wolf Thm 6.3", "arXiv:1606.00608 Appendix A")
- **Mathematical renames**: When renaming a declaration whose old name encodes misleading terminology (banned vocabulary in `docs/prose_style.md` §2), skip the `@[deprecated] alias` and state the reason in the PR body (see `docs/CONTRIBUTING.md` §Mathematical-language renames).

## Workflow

### Mathlib Scouting

When writing new proofs or closing sorrys, scout Mathlib first:
- Use `exact?`, `apply?`, `rw?`, `simp?` tactics
- Grep Mathlib source: `.lake/packages/mathlib/Mathlib/` for related definitions/theorems
- Reuse Mathlib lemmas rather than reproving from scratch
- Not needed for cosmetic fixes, docstrings, imports, or renaming

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

### Paper-realignment mode

When the formalization has drifted from the cited source and the work is
**realigning the Lean development to the paper** (replacing wrong hypotheses,
removing divergent structures, restating theorems to match the source), the
default `sorry`/`axiom` blockers from `docs/PROOF_INTEGRITY.md` are temporarily
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

The marker propagates to wrappers: any theorem whose proof transitively
calls an unfaithful one is itself unfaithful and must carry its own marker.
The marker is removed only when every transitively-cited dependency is
faithful.

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
