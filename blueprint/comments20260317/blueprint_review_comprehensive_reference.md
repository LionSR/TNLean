
# Blueprint Review — Comprehensive Reference

This document integrates all cross-chapter reference material produced
during the review of Chapters 2–11 of the v2 blueprint and the subsequent
v3 review of Chapters 2–12:

- **Part I:** Review protocol (criteria, workflow, output structure)
- **Part II:** AI-style language patterns and corrections
- **Part III:** Cross-chapter notation audit
- **Part IV:** Formalization notes (type-level transitions, chapter by chapter)
- **Part V:** Orphaned statements and dependency graph

The per-chapter review files (`blueprint_chapterN_review.md` for v2,
`blueprint_chapterN_v3_review.md` for v3) contain the detailed
statement-by-statement analysis. This document provides the cross-cutting
material that applies across all chapters.

**Last updated:** After completion of v3 Chapter 12 review (March 2026).

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

| Term | Where | Replacement | v3 Status |
|---|---|---|---|
| "Assembly" | §3.4, §7.6, §8.1, §8.8, Ch12 title | "proof of the main theorem," "combining the results" | **Ch12 title still "Full Assembly"** |
| "Pipeline" | v1 §8.7 (improved in v2 to "Steps toward...") | "construction of the canonical form" | Fixed in v2 |
| "Pipeline end-to-end" | v3 §12.1 title and body (×5 instances) | "reduction," "construction," "chain" | **NEW in v3. Severe.** |
| "upstream pipeline," "downstream" | v3 §12.1 body | "preceding results," "the Fundamental Theorem" | **NEW in v3. Severe.** |
| "packages" | v3 §12.1 body and Thm 12.1 proof | "combines," "applies" | **NEW in v3** |
| "automatic pipeline" | v3 §12.1 body | "the canonical form construction" | **NEW in v3** |
| "Handoff" | v1 Thm 8.30 (removed in v2) | — | Fixed in v2 |
| "Bridge" | §7.10.1, §8.4.1 | "connection," "link," or name by content | |
| "assembled Fundamental Theorem results" | v2 Ch11 preamble | "proves the Fundamental Theorem" | **Fixed in v3** |
| "common-block-structure specialization" | v3 Ch12 preamble, Rmk 12.7 | "assumes common block structure" | Partially fixed; persists in Rmk 12.7 |
| "collected here" | Ch10 preamble | "This chapter also contains..." | |

### Formalization jargon in mathematical prose

| Phrase | Where | Replacement | v3 Status |
|---|---|---|---|
| "stored as an extra field" | Thm 8.29 proof | "included as an additional hypothesis" | |
| "the self-overlap condition is derived rather than stored" | Thm 8.29 | "follows from the other hypotheses" | |
| "re-exports Theorem 8.15" | v1 Thm 8.28 (removed in v2) | — | Fixed in v2 |
| "sorry-free components" | v1 §8.7 (removed in v2) | — | Fixed in v2 |
| "the module MPS/CanonicalFormExistence1606.lean assembles..." | v1 §8.7 (removed in v2) | — | Fixed in v2 |
| "Forget the extra BNT-separation field" | v2 Thm 11.3 proof | "Since both families share the CF data, the BNT separation is not needed" | **Fixed in v3** (Thm 12.6) |
| "take explicit coefficient-convergence input" | v2 Ch11 preamble | "assume coefficient convergence" | **Fixed in v3** |
| "Assume one is given coefficient arrays" | v2 Thm 11.1 | "Suppose there exist coefficient arrays" | **Fixed in v3** (Thm 12.2) |
| "equipped with CF-BNT families" | v2 Thm 11.1 | "in canonical form with BNT separation" | **Fixed in v3** (Thm 12.2) |
| "the hypotheses are assumed directly rather than derived from..." | v2 Thm 10.8 proof | (Remove; state the proof, not meta-commentary) | **Fixed in v3** (Thm 11.9) |
| "the irreducible-TP variant uses the same matching argument with..." | v2 Thm 10.8 proof | (State the variant as a theorem or omit) | **Fixed in v3** |
| "CF-BNT predicate" | v2 Ch10 throughout | "canonical form with BNT separation" | **Mostly fixed in v3** |

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

| Chapter (v3 numbering) | Symbol | Context |
|---|---|---|
| Ch10 (Def 10.9, Thm 10.15) | r | Algebraic: rank of product algebra |
| Ch11 (Def 11.1) | g | BNT: number of ground-state blocks |
| Ch11 (Thm 11.7) | g_A, g_B | BNT permutation |
| Ch12 (Thm 12.2, 12.4, 12.5, 12.6) | g_A, g_B, g | Assembly |

**v3 status:** v2's r_A/r_B in the assembly chapter (now Ch 12) has been
replaced by g_A/g_B. **Fixed on the FT critical path.** The g/r boundary
now sits cleanly at the Ch 10 / Ch 11 interface, which is the natural
algebraic/MPS divide.

**Remaining:** Chapter 10 still uses r in the block-separation theorems
(inherited from the algebraic setting). This is acceptable — r belongs
to the algebraic context of product algebras.

### N-2. Coefficient notation: c_j vs c_N vs a_{N,j}

| Symbol | Where (v3) | Meaning |
|---|---|---|
| a_{N,j} | Thm 11.7, 12.2 | Coefficient array for A-side |
| b_{N,k} | Thm 11.7, 12.2 | Coefficient array for B-side |
| c_N | Thm 11.7, 12.2 | Proportionality sequence |
| c_w(A) | Def 2.4 | Trace coefficient tr(A^w) |

**v3 status:** v2's c_j in Def 10.1 (BNT coefficient) has been replaced
by a span condition in v3 Def 11.1. **Fixed.** The c overload between
block coefficients and the proportionality sequence no longer exists.

### N-3. Permutation symbol: σ overload

| Context | Symbol (v3) | Meaning |
|---|---|---|
| Def 2.4, throughout | σ | Spin configuration (i₁,...,i_N) |
| Thm 10.1 | σ | Block permutation (algebraic context) |
| Thm 11.7, 12.2, 12.4, 12.5 | π | Block permutation (MPS context) |

**v3 status:** v2's σ overload in Theorem 10.7 has been replaced by π
in v3 Theorem 11.7. **Fixed on the FT critical path.** The σ overload
persists only in Chapter 10's algebraic block-permutation theorem
(Thm 10.1), where it refers to a permutation in S_r — this is a different
context from the spin configuration and is less confusing.

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

## Chapter 11: Bases of Normal Tensors (v2 Ch 10)

**11-F1. BNT predicate as dependent structure.**
Packages: block count, bond dimensions, tensor families, total tensor,
normality proofs, coefficients, spanning/independence. Dependent typing
on D same as 2-F3. (Def 11.1, was v2 Def 10.1.)

**11-F2. Coefficient arrays as structured type.**
Convergent sequences with nonzero limits: `Filter.Tendsto` + `Ne` proofs.
(Thm 11.7, was v2 Thm 10.7.)

**11-F3. Gram matrix invertibility.**
"G(N) → I implies G(N) eventually invertible" requires: `det` continuous,
`det(I) = 1 ≠ 0`, so `det(G(N)) ≠ 0` for large N. Separate Lean lemma.
(Thm 11.5, was v2 Thm 10.5.)

**11-F4. Overlap vs inner product: conjugation bridge.**
Gram matrix needs inner product (sesquilinear); overlap is bilinear.
Lean must pass through Lemma 2.32. (Thm 11.5.)

**11-F5. Newton–Girard: Mathlib dependency.**
May be available in Mathlib. Low priority (orphaned; acknowledged by
Remark 11.14 in v3). (Thms 11.12–11.13.)

## Chapter 12: Proof of the Fundamental Theorem (v2 Ch 11)

**12-F1. Extracting N₀ from eventual linear independence.**
Theorem 12.5 proof uses "for all sufficiently large N" from Theorem 11.5.
In Lean, this is a `Filter.Eventually` statement. The proof extracts a
concrete N₀ and evaluates at N₀ and N₀+1 for weight matching. Standard:
`obtain ⟨N₀, hN₀⟩ := (h.eventually).exists`. (Thm 12.5.)

**12-F2. Gauge-phase equivalence → gauge equivalence upgrade.**
Theorems 12.2/12.4 conclude gauge-phase equivalence. Theorem 12.5
upgrades to gauge equivalence by absorbing the phase into the weight.
These are distinct Lean predicates. (Thms 12.2–12.5. Was v2 note 11-F2.)

**12-F3. Theorem 12.1 — forward dependency in Lean.**
Theorem 12.1's proof invokes Theorem 12.4 (which appears later in the
blueprint). In Lean, 12.1's declaration must come after 12.4's. The
formalization agent should reorder if needed. (Thm 12.1.)

**12-F4. Permutation composition in Theorem 12.5.**
The final step composes the block-diagonal gauge X = ⊕_j X_j with the
permutation matrix of π. In Lean, this requires the `BlockPermutation`
infrastructure (`sirui-lu.com/TNLean`). The permutation matrix and the
block-diagonal gauge live at different type levels. (Thm 12.5.)

**12-F5. Scope relative to the existence pipeline.**
Theorem 12.5 assumes CF-BNT data as input. Two gaps remain in the
existence pipeline (Remark 9.50): irreducibility of blocked blocks, and
pairwise distinct weight norms. These affect Level B (arbitrary tensor →
FT), not Level A (tensors in CF → FT). Theorem 12.5 is complete at
Level A. See `formalization_goal_analysis.md`. (Thm 12.5, Rmk 9.50.)

---

# Part V: Orphaned Statements and Dependency Graph

## Orphan Status (Updated for v3, All FT-Critical Chapters Reviewed)

### Confirmed orphaned

1. **Theorems 11.12–11.13 (Newton–Girard, v3 §11.4; was v2 10.11–10.12).**
   Never cited by any theorem in v3. Remark 11.14 in v3 explicitly
   acknowledges their orphan status and notes that the route to
   Theorem 12.5 uses BNT linear independence rather than Newton–Girard.

2. **Theorem 11.10 (coefficient ratio decay, v3 §11.3; was v2 10.9).**
   Indirectly needed to instantiate Theorem 11.7's abstract hypotheses
   from CF-BNT data. Remark 11.8 (v3) and Remark 12.3 (v3) address the
   coefficient-instantiation gap at the presentation level, showing that
   a_{N,j} = μ_j^N via Theorem 2.24. However, neither remark cites
   Theorem 11.10. **Confirmed orphaned relative to Chapter 12.**

### Not orphaned (earlier flags resolved)

3. **Theorem 9.11 → v3 renumbered.** The Vandermonde separation result
   is used by the block separation core (Lemma 10.14 in v3). Confirmed
   NOT orphaned.

### Minor: possibly unused

4. **c_w(A) notation (Def 2.4).** Used in Ch3 Lemma 3.2. Possibly unused
   after Chapter 3. Low priority.

### v3 resolution

The bridging lemma recommended in the v2 review (Ch11 §4a) has been
incorporated as Theorem 12.5. This closes the structural gap without
un-orphaning Newton–Girard (Theorems 11.12–11.13), since the bridging
argument uses BNT linear independence instead. Newton–Girard remains an
alternative route to weight matching but is not needed. Remark 11.14
documents this decision.

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

### Resolved in v3

- **Scope reduction in equal-MPV FT (item X-5).** v2's Theorem 11.3
  assumed common block structure. v3's Theorem 12.5 recovers the full
  [CPGSV21, Corollary IV.5] unconditionally via BNT linear independence.

- **Coefficient-instantiation gap.** v3 adds Remark 11.8 (Ch 11) and
  Remark 12.3 (Ch 12) explaining how CF-BNT data instantiate the abstract
  coefficient hypotheses.

- **Notation: g vs r in assembly chapter.** v3 Ch 12 uses g_A/g_B
  throughout, consistent with Ch 11. Fixed.

- **Notation: σ overload in BNT permutation theorem.** v3 Theorem 11.7
  uses π for the permutation. Fixed.

- **Notation: c_j in BNT definition.** v3 Def 11.1 replaces c_j with a
  span condition. Fixed.

- **"Basis Normal Tensor" naming.** v3 Def 11.1 and Ch 11 title corrected
  to "Basis of Normal Tensors." Fixed (though Ch 11 title overcorrected
  to plural "Bases").

- **"Normal" terminology (item X-1).** v3 Def 9.29 now correctly states
  the equivalence with Def 2.19 via [SPGWC10, Prop. 3]. Partially
  resolved — Remark 11.6 still presents the two notions as distinct
  (see Ch 11 v3 review, item 11-S5).

### Open (presentation, not mathematical)

- **"Normal" terminology: Remark 11.6 contradiction.** Remark 11.6 in v3
  presents algebraic normality and normal-canonical-form normality as "two
  distinct senses," contradicting the equivalence stated in Def 9.29. See
  Ch 11 v3 review, item 11-S5.

- **Definition duplication.** Def 9.1 (v3) cross-references Def 2.23
  (fixed). Def 9.14 (v3) cross-references Def 4.12 (fixed). Earlier
  duplications in v2 Chapters 8–9 resolved.

- **Chapter 12 title "Full Assembly."** Flagged as AI language. Should be
  "Proof of the Fundamental Theorem" or "The Fundamental Theorem of MPS."

- **§12.1 AI language.** "Pipeline end-to-end," "upstream pipeline,"
  "downstream," "packages," "automatic pipeline." Most concentrated AI
  language in the blueprint. See Ch 12 v3 review, item 12-AI1.

- **Theorem 12.1 non-degeneracy hypothesis.** Role unclear. See Ch 12 v3
  review, item 12-S1.

## Full Blueprint Dependency Graph (v3 numbering)

| Source | Used by |
|---|---|
| Ch 2 (MPV definitions) | Ch 3, 7, 8, 9, 10, 11, 12 |
| Ch 3 (Single-block FT) | Ch 9, 10 |
| Ch 4 (Channels, positive maps) | Ch 5, 6, 7, 8, 9 |
| Ch 5 (Schwarz / KS inequality) | Ch 7, 8, 9 |
| Ch 6 (Perron–Frobenius theory) | Ch 7, 8, 9 |
| Ch 7 (Spectral gap, block separation) | Ch 8, 9, 10, 11, 12 |
| Ch 8 (Wielandt bound) | Ch 9 |
| Ch 9 (Canonical form reduction) | Ch 10, 11, 12 |
| Ch 10 (Block permutation and separation) | Ch 11, 12 |
| Ch 11 (Bases of normal tensors) | Ch 12 |
| Ch 12 (Proof of the Fundamental Theorem) | Terminal (FT critical path) |
| Ch 13 (Quantum dynamical semigroups) | Not on FT critical path |

## Review Completion Status

### v2 reviews (Chapters 2–11)

| Chapter (v2) | Review file | Status |
|---|---|---|
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
| 2–6 consolidated | `blueprint_chapters2to6_review_consolidated.md` | Complete |
| Cross-chapter | `wielandt_comparison_with_paper.md` | Complete |
| This file | `blueprint_review_comprehensive_reference.md` | Complete |

### v3 reviews (Chapters 2–12)

| Chapter (v3) | Review file | Status |
|---|---|---|
| 2 | `blueprint_chapter2_v3_review.md` | Complete |
| 3 | `blueprint_chapter3_v3_review.md` | Complete |
| 4 | `blueprint_chapter4_v3_review.md` | Complete |
| 5 | `blueprint_chapter5_v3_review.md` | Complete |
| 6 | `blueprint_chapter6_v3_review.md` | Complete |
| 7 | `blueprint_chapter7_v3_review.md` | Complete |
| 8 | `blueprint_chapter8_v3_review.md` | Complete |
| 9 | `blueprint_chapter9_v3_review.md` | Complete |
| 10 | `blueprint_chapter10_v3_review.md` | Complete |
| 11 | `blueprint_chapter11_v3_review.md` | Complete |
| 12 | `blueprint_chapter12_v3_review.md` | Complete |
| 13 | Not yet started | Pending (not on FT critical path) |

### Supporting documents

| Document | Status |
|---|---|
| `full_ft_verification.md` | Complete (bridging argument, now internalized as Thm 12.5) |
| `formalization_goal_analysis.md` | Complete (Level A/B analysis, existence pipeline gaps) |
| `v3_review_standing_instructions.md` | Complete (updated March 2026) |
