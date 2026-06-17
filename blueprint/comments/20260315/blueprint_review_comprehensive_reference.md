
# Blueprint Review — Comprehensive Reference

This document integrates all cross-chapter reference material produced
during the review of Chapters 2–11 of the v2 blueprint:

- **Part I:** Review protocol (criteria, workflow, output structure)
- **Part II:** AI-style language patterns and corrections
- **Part III:** Cross-chapter notation audit
- **Part IV:** Formalization notes (type-level transitions, chapter by chapter)
- **Part V:** Orphaned statements and dependency graph

The per-chapter review files (`blueprint_chapterN_review.md`) contain the
detailed statement-by-statement analysis. This document provides the
cross-cutting material that applies across all chapters.

---

# Part I: Review Protocol

## Core Review Goal

The purpose of the review is to:

- Examine the blueprint chapter-by-chapter
- Identify mistakes, redundancies, inconsistencies, and unclear points
- Compare statements with the reference literature
- Produce a detailed adversarial audit of the document

Each chapter is reviewed separately; results are collected into Markdown
files using the same criteria throughout.

## Required Review Criteria

For every statement (definitions, lemmas, theorems, explanations):

**1. Consistency with known literature.** Check against [PGVWC07],
[CPGSV21], [CPGSV17], [SPGWC10], [Wol12], [EHK78], [Jac09]. Flag
incorrect statements, altered definitions, missing assumptions, stronger
claims than the references support, and deviations in terminology.

**2. Repetitive or conflicting statements.** Identify definitions that
appear multiple times (within or across chapters), similar lemmas in
multiple chapters, and different versions of the same statement.

**3. Missing clarifications or subtleties.** Flag statements that are
technically correct but unclear, missing assumptions, ambiguous, or
lacking necessary explanation (undefined notation, unclear scope, implicit
assumptions).

**4. Deviations from the literature.** Check for different techniques,
definitions, terminology, or logical structure. Determine whether
deviations are harmless, potentially misleading, or mathematically
problematic.

**5. Unused or missing definitions.** Detect definitions introduced but
never used, concepts used but never defined, and notation without
introduction.

**6. Structural or logical issues.** Logical dependency issues, circular
reasoning, misplaced statements, results appearing before necessary
definitions.

**7. Statement-by-statement review.** Every definition, lemma, theorem,
proposition, and explanatory claim is examined individually.

**8. AI-generated language.** Flag unnatural mathematical phrasing,
formalization jargon in prose, and suggest natural alternatives. (See
Part II for the accumulated findings.)

## Expected Output Structure

Each chapter review contains:

- Global chapter assessment (table)
- v1 → v2 changes
- Statement-by-statement analysis
- Cross-chapter consistency checks
- Literature alignment
- AI-language issues
- Formalization notes (type-level transitions)
- Cleanup checklist
- Final assessment

## Workflow

1. Review one chapter at a time.
2. Wait for user confirmation before proceeding.
3. Collect results into Markdown files.
4. All chapters use the same criteria.

---

# Part II: AI-Style Language Patterns

The blueprint is AI-generated. The following patterns have been detected
across Chapters 2–11. The distinction separates language that should be
rewritten from naming conventions acceptable for formalization.

## Language That Should Be Rewritten

### Organizational terms not used in mathematical writing

| Term | Where | Replacement |
|---|---|---|
| "Assembly" | §3.4, §7.6, §8.1, §8.8, Ch11 title | "proof of the main theorem," "combining the results" |
| "Pipeline" | v1 §8.7 (improved in v2 to "Steps toward...") | "construction of the canonical form" |
| "Handoff" | v1 Thm 8.30 (removed in v2) | — |
| "Bridge" | §7.10.1, §8.4.1 | "connection," "link," or name by content |
| "assembled Fundamental Theorem results" | Ch11 preamble | "proves the Fundamental Theorem" |
| "common-block-structure specialization" | Ch11 preamble | "assumes common block structure" |
| "collected here" | Ch10 preamble | "This chapter also contains..." |

### Formalization jargon in mathematical prose

| Phrase | Where | Replacement |
|---|---|---|
| "stored as an extra field" | Thm 8.29 proof | "included as an additional hypothesis" |
| "the self-overlap condition is derived rather than stored" | Thm 8.29 | "follows from the other hypotheses" |
| "re-exports Theorem 8.15" | v1 Thm 8.28 (removed in v2) | — |
| "sorry-free components" | v1 §8.7 (removed in v2) | — |
| "the module MPS/CanonicalFormExistence1606.lean assembles..." | v1 §8.7 (removed in v2) | — |
| "Forget the extra BNT-separation field" | Thm 11.3 proof | "Since both families share the CF data, the BNT separation is not needed" |
| "take explicit coefficient-convergence input" | Ch11 preamble | "assume coefficient convergence" |
| "Assume one is given coefficient arrays" | Thm 11.1 | "Suppose there exist coefficient arrays" |
| "equipped with CF-BNT families" | Thm 11.1 | "in canonical form with BNT separation" |
| "the hypotheses are assumed directly rather than derived from..." | Thm 10.8 proof | (Remove; state the proof, not meta-commentary) |
| "the irreducible-TP variant uses the same matching argument with..." | Thm 10.8 proof | (State the variant as a theorem or omit) |
| "CF-BNT predicate" | Ch10 throughout | "canonical form with BNT separation" |

### Unexpanded abbreviations

| Abbreviation | First use | Expansion needed |
|---|---|---|
| "CFII data" | Ch8 | "Canonical Form II data in the sense of [CPGSV17, Appendix A]" |
| "CF-BNT" | Ch10 | "canonical form with basis of normal tensors separation" |
| "BNT" | Ch10 title | "basis of normal tensors" (NOT "basis normal tensor") |
| "DS gauge" | v1 throughout | v2 replaces with "TP normalization" (resolved) |

### Slightly unnatural mathematical phrasing

| Phrase | Where | Better phrasing |
|---|---|---|
| "word evaluation respects concatenation" | Ch2 | "word evaluation is multiplicative" |
| "entry norms bounded by 1" | Ch4 | "matrix entries bounded in absolute value" |
| "the overlap-orthonormal hypotheses are assumed directly" | Thm 10.8 | (Remove meta-commentary) |

## Naming Conventions Acceptable for Formalization

The following are nonstandard as mathematical terminology but serve as
useful identifiers in a Lean formalization blueprint. They do not need
to be changed:

- "Wielandt analysis" (Definition 7.20)
- "Block-injective canonical form" (Definition 2.21)
- "Fixed-point projection" (Definition 4.31)
- "Trace pairing map" (Definition 3.3)
- "Cumulative vector span" (Definition 7.16)
- "Normal canonical form predicate" (Definition 8.28)

## General Principle

The blueprint should read as a mathematical document that happens to be
targeted at formalization, not as documentation for a codebase. Proof
sketches should use standard mathematical language. References to Lean
module names, tactic names, or data-structure concepts should be confined
to parenthetical remarks or footnotes.

---

# Part III: Cross-Chapter Notation Audit

## Notation Consistent Throughout

| Symbol | Defined | Meaning |
|---|---|---|
| A^i | Def 2.1 | Physical-index matrix, i ∈ {0,...,d−1} |
| A^w | Def 2.2 | Word evaluation, w = (i₁,...,i_L) |
| V^{(N)}(A) | Def 2.4 | MPV ket at system size N |
| V^{(N)}(A)_σ | Def 2.4 | MPV coefficient, σ ∈ {0,...,d−1}^N |
| 𝒱(A) | Def 2.4 | MPV family |
| μ_k | Def 2.23 | Scaling factor for block k |
| D_k | Def 2.23 | Bond dimension of block k |
| ⊕_k μ_k A_k | Def 2.23 / 8.1 | Block-diagonal tensor |
| ℰ_A | Ch4 | Transfer map ∑ A_i (·) A_i† |
| F_{AB} | Def 6.1 | Mixed transfer ∑ A_i (·) B_i† |
| O_{AB}(N) | Def 2.31 | Bilinear MPV overlap |
| ⟨V(A)|V(B)⟩ | Def 2.30 | Sesquilinear MPV inner product |
| S_n(A) | Def 7.1 | Word span at length n |
| T_n(A) | Def 7.2 | Cumulative span up to length n |

## Notation Inconsistencies

### N-1. Block count: g vs r

| Chapter | Symbol | Context |
|---|---|---|
| Ch9 (Def 9.8, Thm 9.15) | r | Algebraic: rank of product algebra |
| Ch10 (Def 10.1) | g | BNT: number of ground-state blocks |
| Ch10 (Thm 10.7–10.8) | g_A, g_B | BNT permutation |
| Ch11 (Thm 11.1–11.2) | r_A, r_B | Assembly |
| Ch11 (Thm 11.3) | r | Equal-MPV case |

**Problem:** g (MPS literature) and r (algebra) collide in Chapters 10–11.
Theorem 11.1 uses r_A where Theorem 10.7 uses g_A for the same quantity.

**Recommendation:** Standardize on g for MPS chapters (10–11). Keep r in
the purely algebraic Chapter 9. Theorem 9.15 bridges the two.

### N-2. Coefficient notation: c_j vs c_N vs a_{N,j}

| Symbol | Where | Meaning |
|---|---|---|
| c_j | Def 10.1 | BNT coefficient (N-independent notation) |
| a_{N,j} | Thm 10.7, 11.1 | Coefficient array for A-side |
| b_{N,k} | Thm 10.7, 11.1 | Coefficient array for B-side |
| c_N | Thm 10.7, 11.1 | Proportionality sequence |
| c_w(A) | Def 2.4 | Trace coefficient tr(A^w) |

**Problem:** c is overloaded. Def 10.1's c_j should be N-dependent
(a_{N,j} = μ_j^N from Theorem 2.24). The c_N proportionality sequence
clashes with the c_j block coefficients.

**Recommendation:** Replace c_j in Def 10.1 with a_{N,j}, or rephrase
condition 2 as "lies in the span of" without naming coefficients.

### N-3. Permutation symbol: σ overload

| Context | Symbol | Meaning |
|---|---|---|
| Def 2.4, throughout | σ | Spin configuration (i₁,...,i_N) |
| Thm 9.1, 10.7, 10.8 | σ | Block permutation |
| Thm 11.1, 11.2 | π | Block permutation |

**Problem:** σ denotes both the spin configuration and the block
permutation in the same equation (Theorem 10.7).

**Recommendation:** Use π for permutations in Chapters 9–11. Use σ only
for spin configurations.

### N-4. Minor issues

- **c_w(A)** (Def 2.4): Possibly unused after Chapter 3, Lemma 3.2.
- **G_{jk}(N)** (Thm 10.5 proof): Conflates the bilinear overlap O_{A_j A_k}
  with the sesquilinear inner product needed for Gram matrix arguments.
  Lean code requires the conjugation step (Lemma 2.32).
- **Definition 8.1 duplicates Definition 2.23** (block-diagonal tensor).
  Should be a cross-reference.
- **Definition 8.14 duplicates Definition 4.23** (irreducible tensor).
  Should be a cross-reference.

---

# Part IV: Formalization Notes (Type-Level Transitions)

## General Principle

The Lean type system forces every morphism to carry its algebraic structure
explicitly. The blueprint routinely makes type-level transitions silently.
Each chapter should include a brief "formalization notes" remark identifying
the key transitions. This section collects them all.

## Chapter 2: Matrix Product Vectors

**2-F1. Tensor as function type.**
Lean type: `Fin d → Matrix (Fin D) (Fin D) ℂ`. Blueprint suppresses the
physical index. (Def 2.1.)

**2-F2. Same-MPV: two predicates.**
Equal-dimension (Def 2.8) and different-dimension (Def 2.9) are different
Lean propositions. (Defs 2.8–2.9.)

**2-F3. Block-diagonal tensor as dependent type.**
Block k lives in `Matrix (Fin (D k)) (Fin (D k)) ℂ`, varying with k.
Assembly into total bond dimension requires explicit block-diagonal
construction. (Def 2.23 / 8.1.)

**2-F4. Overlap: two bilinear forms.**
Inner product (sesquilinear, Def 2.30) vs overlap (bilinear, Def 2.31)
have different Lean signatures. (Defs 2.30–2.31.)

## Chapter 3: Single-Block Fundamental Theorem

**3-F1. The linear extension type chain.**
Six transitions in Theorem 3.11's proof: ℂ-linear → multiplicative →
nonzero → bijective → unital (algebra hom) → inner automorphism
(Skolem–Noether). Each is a separate Lean theorem. (Thm 3.11.)

**3-F2. Surjectivity from simplicity.**
Three sub-steps: kernel is two-sided ideal → simplicity forces kernel = {0}
→ injective + finite-dimensional = surjective. (Thm 3.8.)

## Chapter 4: Quantum Channels and Positive Maps

**4-F1. Map hierarchy.**
Positive → CP → TP → channel (CP+TP); also unital (dual to TP). Each is
a separate Lean predicate. (Defs 4.1–4.5.)

**4-F2. Transfer map predicates.**
ℰ_A is CP by construction; TP iff ∑(A^i)†A^i = 𝟙; unital iff
∑A^i(A^i)† = 𝟙. "Normalized" in the blueprint means TP. (Defs 4.14–4.15.)

**4-F3. Adjoint duality: TP ↔ unital of adjoint.**
Needs an explicit Lean lemma. (After Def 4.2.)

**4-F4. Kadison–Schwarz requires CP.**
KS inequality (Thm 4.17) holds for CP maps. Blueprint says "by KS"
without noting CP is the hypothesis. (Thm 4.17, Ch6 uses.)

**4-F5. Adjoint-fixed-point route (new in v2).**
§4.7.2 (Lemma 4.44, Thm 4.45): preferred Lean route for peripheral
spectrum arguments, replacing DS gauge. (§4.7.2.)

## Chapter 5: Perron–Frobenius Theory

**5-F1. Three results, three hypotheses.**
PSD existence: requires TP. PD upgrade: requires irreducibility.
Uniqueness: requires irreducibility. Blueprint should note minimal
hypotheses. (Thms 5.2, 5.3/5.5, 5.8.)

**5-F2. Injective → irreducible coercion.**
When PD upgrade is applied to injective tensors, Lean first coerces via
Theorem 4.24. (Thm 5.2 applied to injective tensors.)

## Chapter 6: Spectral Gap and Block Separation

**6-F1. Mixed transfer: different type from self-transfer.**
F_{AB} maps between M_{D_A} and M_{D_B} (rectangular); ℰ_A maps M_D → M_D.
Different Lean types. (Defs 6.1–6.2.)

**6-F2. TP normalization required.**
Spectral gap theorems require TP. Sometimes implicit. (§6.3–6.6.)

## Chapter 7: Wielandt Bound

**7-F1. Word span as subspace vs algebra.**
S_n(A) and T_n(A) are subspaces. Normality T_N = M_D is a vector-space
equality. The algebra generation is an additional step. (Def 7.1, Thm 7.12.)

**7-F2. Blocking: type change.**
L-blocked tensor has physical dimension d^L. Changes the Lean type from
`Fin d → ...` to `Fin (d^L) → ...`. (Thm 7.33.)

## Chapter 8: Canonical Form Reduction

**8-F1. Two routes, two predicate families.**
Block-injective: `IsInjective` + TP + self-overlap convergence.
Normal-canonical: `IsIrreducible` + TP + `IsPrimitive`.
Bridge requires explicit coercion steps. (Defs 8.14, 8.28; Thms 8.24, 8.26.)

**8-F2. Adjoint-fixed-point route in Theorem 8.26.**
Six-step Lean chain: TP → adjoint unital → irreducibility transfers →
PD fixed point → Lemma 4.44 → roots of unity → blocking gives primitivity.
(Thm 8.26.)

**8-F3. Burnside's theorem as external dependency.**
Nontrivial algebraic result (Thm 8.21). Check Mathlib status. (Thm 8.21.)

## Chapter 9: Block Permutation and Separation

**9-F1. Ring → algebra two-level structure.**
Block ideal permutation (Thm 9.1) at ring level (`RingEquiv`). Dimension
preservation (Thm 9.2) and Skolem–Noether (Thm 9.3) require algebra
equivalence (`AlgEquiv`). Verified against Lean code. (§9.1.)

**9-F2. Linear → multiplicative → bijective → unital → automorphism.**
Same chain as 3-F1, applied per-block in Theorem 9.6. (§9.2.)

**9-F3. Proof citation in Lemma 9.12.**
Invokes "Theorem 8.23" but actual argument uses contrapositive of
Theorem 6.17. Lean proof term needs correct reference. (Lemma 9.12.)

## Chapter 10: Bases of Normal Tensors

**10-F1. BNT predicate as dependent structure.**
Packages: block count, bond dimensions, tensor families, total tensor,
normality proofs, coefficients, spanning/independence. Dependent typing
on D same as 2-F3. (Def 10.1.)

**10-F2. Coefficient arrays as structured type.**
Convergent sequences with nonzero limits: `Filter.Tendsto` + `Ne` proofs.
(Thm 10.7.)

**10-F3. Gram matrix invertibility.**
"G(N) → I implies G(N) eventually invertible" requires: `det` continuous,
`det(I) = 1 ≠ 0`, so `det(G(N)) ≠ 0` for large N. Separate Lean lemma.
(Thm 10.5.)

**10-F4. Overlap vs inner product: conjugation bridge.**
Gram matrix needs inner product (sesquilinear); overlap is bilinear.
Lean must pass through Lemma 2.32. (Thm 10.5.)

**10-F5. Newton–Girard: Mathlib dependency.**
May be available in Mathlib. Low priority (orphaned in v2). (Thms 10.11–10.12.)

## Chapter 11: Full Assembly

**11-F1. CF-BNT data as Lean structure.**
Dependent structure with proof-carrying fields for coefficient convergence
and nonzero limits. (Thms 11.1–11.2.)

**11-F2. Gauge equivalence vs gauge-phase equivalence.**
Different Lean predicates. Upgrade requires matching phases from weight
matching. (Thms 11.1–11.3.)

**11-F3. "Forget" as structure coercion.**
Dropping BNT-separation field = coercion from CF-BNT structure to CF
structure. Explicit Lean term needed. (Thm 11.3.)

---

# Part V: Orphaned Statements and Dependency Graph

## Orphan Status (Final, All Chapters Reviewed)

### Confirmed orphaned

1. **Theorems 10.11–10.12 (Newton–Girard, §10.4).** Never cited in v2.
   Used by v1's Theorem 10.13, not by v2's Theorem 11.3. Remain orphaned
   even if the bridging lemma (Ch11 review §4a) is added, since that
   lemma uses BNT linear independence rather than Newton–Girard.

2. **Theorem 10.9 (coefficient ratio decay, §10.3).** Indirectly needed
   to instantiate Theorem 10.7's abstract hypotheses from CF-BNT data,
   but this instantiation step is not stated as a theorem in v2.

### Not orphaned (earlier flags resolved)

3. **Theorem 9.11 (Vandermonde separation).** Used by Lemma 9.12 (block
   separation core). Confirmed during Chapter 11 review.

### Minor: possibly unused

4. **c_w(A) notation (Def 2.4).** Used in Ch3 Lemma 3.2. Possibly unused
   after Chapter 3.

### Recommendation

Add the bridging lemma (Ch11 review §4a) and an application lemma
instantiating Theorem 10.7's hypotheses from CF-BNT data. This closes
the two structural gaps and un-orphans Theorem 10.9. Theorems 10.11–10.12
should be either marked as auxiliary results or removed.

## Cross-Chapter Issues (Resolved and Open)

### Resolved in v2

- **DS gauge misconception.** Eliminated throughout Chapters 4–11 via the
  adjoint-fixed-point route (Ch4 §4.7.2), separate right/left canonical
  gauges (Ch5 §5.4), and separate gauging in proofs (Ch6 Thm 6.12).

- **MPV coefficient notation.** Explicit everywhere in v2.

- **Overlap conjugation conventions.** Verified correct (inner product:
  bar on first argument; overlap: bar on second).

- **v1's Theorem 4.37 (peripheral eigenvalues).** Replaced by corrected
  Theorems 4.38–4.39.

- **v1's Chapter 6 Theorem 6.12 proof.** Rewritten without DS gauge.

- **Chapter 9 DS gauge residue (item X-4).** Confirmed corrected in v2:
  Definition 9.8 uses TP normalization.

### Open (presentation, not mathematical)

- **Two characterizations of "normal" (item X-1).** Def 2.19 (algebraic:
  S_{L₀} = M_D) and Def 8.28 (spectral: irreducible + primitive) are
  equivalent by [SPGWC10, Proposition 3]. Blueprint should add a
  prominent remark stating the equivalence. Flagged in every review
  since Chapter 2.

- **Definition duplication.** Def 8.1 duplicates 2.23; Def 8.14
  duplicates 4.23. Should be cross-references.

- **"Basis of normal tensors" naming.** Chapter 10 title and Def 10.1
  say "Basis Normal Tensor" — should be "basis of normal tensors."

- **Notation: g vs r, c_j vs c_N, σ overload.** See Part III above.

## Full Blueprint Dependency Graph

| Source | Used by |
|---|---|
| Ch 2 (MPV definitions) | Ch 3, 6, 7, 8, 9, 10, 11 |
| Ch 3 (Single-block FT) | Ch 8, 9 |
| Ch 4 (Channels, KS inequality) | Ch 5, 6, 7, 8 |
| Ch 5 (Perron–Frobenius theory) | Ch 6, 7, 8 |
| Ch 6 (Spectral gap, block separation) | Ch 7, 8, 9, 10, 11 |
| Ch 7 (Wielandt bound) | Ch 8 |
| Ch 8 (Canonical form reduction) | Ch 9, 10, 11 |
| Ch 9 (Block permutation and separation) | Ch 10, 11 |
| Ch 10 (Bases of normal tensors) | Ch 11 |
| Ch 11 (Full assembly) | Terminal |

## Review Completion Status

| Chapter | Review file | Status |
|---|---|---|
| 2–6 | `blueprint_chapters2to6_review_consolidated.md` | Complete (merged from v1→v2 comparison and remaining-issues files) |
| 2 | `blueprint_chapter2_review.md` | Complete |
| 3 | `blueprint_chapter3_review.md` | Complete |
| 4 | `blueprint_chapter4_review.md` | Complete |
| 5 | `blueprint_chapter5_review.md` | Complete |
| 6 | `blueprint_chapter6_review.md` | Complete |
| 7 | `blueprint_chapter7_review.md` | Complete |
| 8 | `blueprint_chapter8_review.md` | Complete |
| 9 | `blueprint_chapter9_review.md` | Complete |
| 10 | `blueprint_chapter10_review.md` | Complete |
| 11 | `blueprint_chapter11_review.md` | Complete |
| Cross-chapter | `wielandt_comparison_with_paper.md` | Complete |
| This file | `blueprint_review_comprehensive_reference.md` | Complete |
