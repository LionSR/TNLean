# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

TNLean is a Lean 4 formalization of the **Fundamental Theorem of Matrix Product States**, **Quantum Wielandt theory**, and finite-dimensional **quantum-channel theory** (following Wolf's *Quantum Channels & Operations*). Built on Mathlib v4.28.0.

## Build Commands

```bash
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

- **Lean**: v4.28.0 (pinned in `lean-toolchain`)
- **Mathlib**: v4.28.0
- **checkdecls**: Blueprint declaration checker (PatrickMassot/checkdecls)
- **Gametheory**: Custom Brouwer fixed-point theorem library (LionSR/Brouwer)

### Lean Options (lakefile.toml)

- `relaxedAutoImplicit = false` — strict implicit arguments, no auto-implicit
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `maxSynthPendingDepth = 3` — typeclass synthesis depth limit

## Architecture

The source lives in `TNLean/` and is organized into **6 semantic layers** (see `TNLean.lean` for the full import graph):

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
| [`docs/style.md`](docs/style.md) | Code formatting, line length (100 chars), declarations, tactic style, whitespace, transparency |
| [`docs/naming.md`](docs/naming.md) | Capitalization rules, symbol-to-name dictionary, variable conventions |
| [`docs/doc.md`](docs/doc.md) | Module docstrings, definition docstrings, sectioning comments, BibTeX citations |
| [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) | PR title format (`type(scope): description`), issue conventions, label taxonomy, review checklist |
| [`docs/pr-review.md`](docs/pr-review.md) | Review criteria: style, documentation, location, improvements, library integration |
| [`docs/pr_review_management.md`](docs/pr_review_management.md) | PR triage process, comment API mapping, merge decisions |
| [`docs/PROOF_INTEGRITY.md`](docs/PROOF_INTEGRITY.md) | Blockers (`sorry`, `axiom`, kernel bypasses, circular reasoning) and warnings (`maxHeartbeats`, debug artifacts) |
| [`docs/blueprint_style_guide.md`](docs/blueprint_style_guide.md) | LaTeX conventions, `\lean{}`/`\leanok` tags, notation table, banned AI/software language |
| [`docs/ci-automation.md`](docs/ci-automation.md) | CI workflows, auto-fix loops, iteration caps, commit message conventions |

### Quick Reference (from the docs above)

- **PR titles**: `type(scope): description` — types: `feat`, `fix`, `refactor`, `docs`, `ci`, `chore`; scope is shortened module path without `TNLean/` prefix
- **Naming**: Definitions `camelCase`, predicates `IsPrefix`, theorems `snake_case`, files `CamelCase.lean`
- **Proof integrity blockers**: `sorry`, `admit`, `native_decide`, `unsafeCast`, `axiom`, circular reasoning
- **Blueprint prose**: Pure mathematics only — no Lean identifiers in text, no software jargon (see banned terms list in blueprint style guide)
- **Paper references**: Cite theorem numbers in docstrings (e.g., "Wolf Thm 6.3", "arXiv:1606.00608 Appendix A")

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
