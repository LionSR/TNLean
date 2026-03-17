
# Blueprint Review — Chapter 7 (Spectral Gap and Block Separation), v2 → v3

This document reviews Chapter 7 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter6_review.md`, `blueprint_chapters2to6_review_consolidated.md`,
`blueprint_review_comprehensive_reference.md`).

---

## Chapter numbering map

v3 Chapter 7 = v2 Chapter 6 (Spectral Gap and Block Separation). The
chapter is renumbered +1 due to the new Chapter 5 (Schwarz Inequalities)
inserted in v3.

| v2 | v3 | Content | Change |
|---|---|---|---|
| Def 6.1 | Def 7.1 | Mixed transfer operator | Renumbered only |
| Def 6.2 | Def 7.2 | Rectangular mixed transfer | Renumbered only |
| Remark 6.3 | Remark 7.3 | Self-transfer identity | Renumbered only |
| Thm 6.4 | Thm 7.4 | Iterated mixed transfer | Renumbered; internal ref updated |
| Thm 6.5 | Thm 7.5 | Matrix trace at identity | Renumbered; internal ref updated (6.7→7.7) |
| Lemma 6.6 | Lemma 7.6 | Trace expansion over matrix units | Renumbered only |
| Thm 6.7 | Thm 7.7 | Overlap = transfer trace | Renumbered; internal refs updated (6.6→7.6, 6.4→7.4) |
| Thm 6.8 | Thm 7.8 | Rectangular overlap = transfer trace | Renumbered; internal ref updated (6.7→7.7) |
| Lemma 6.9 | Lemma 7.9 | Word trace as entrywise inner product | Renumbered only |
| Thm 6.10 | Thm 7.10 | Eigenvalue bound | Renumbered only |
| Thm 6.11 | Thm 7.11 | Spectral radius bound | Renumbered; internal ref updated (6.10→7.10) |
| Thm 6.12 | Thm 7.12 | ρ ≥ 1 ⇒ gauge-phase equiv | Renumbered; cross-refs updated (see below) |
| Thm 6.13 | Thm 7.13 | Strict spectral gap | Renumbered; internal refs updated (6.11→7.11, 6.12→7.12) |
| Thm 6.14 | Thm 7.14 | Rectangular spectral gap | Renumbered; internal ref updated (6.10→7.10) |
| Thm 6.15 | Thm 7.15 | Rectangular overlap decay | Renumbered; internal refs updated (6.14→7.14, 6.8→7.8) |
| Thm 6.16 | Thm 7.16 | Transfer powers → 0 | Renumbered; internal ref updated (6.13→7.13) |
| Thm 6.17 | Thm 7.17 | Overlap decay | Renumbered; internal refs updated (6.7→7.7, 6.6→7.6, 6.16→7.16) |
| Remark 6.18 | Remark 7.18 | Cross-correlation decay | Renumbered; internal ref updated (6.16→7.16) |
| Remark 6.19 | Remark 7.19 | Self-correlation persists | Renumbered; ref updated (5.9→6.9) |
| Thm 6.20 | Thm 7.20 | Complementary gap ⇒ Tr→1 | Renumbered; refs updated (4.31→4.20, 4.32→4.21) |
| Thm 6.21 | Thm 7.21 | Self-overlap convergence | Renumbered; internal refs updated (6.7→7.7, 6.20→7.20) |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. Follows [PGVWC07] throughout. No deviations from v2. |
| Internal consistency | Good. All internal references updated for v3 numbering. |
| v2 → v3 changes | Renumbering only (+1). Zero substantive text changes. |
| AI language | Clean. No issues detected in this chapter. |
| Formalization readiness | Same as v2. Two compressed proofs carried over (7.12, 7.14). |
| Open items from prior review | All v1→v2 corrections confirmed intact. Two moderate items (6-B, 6-C) unchanged. |
| FT critical path | **Yes.** Theorems 7.12, 7.15, 7.17, 7.21 are load-bearing for Chapters 9–12. |

---

# v2 → v3 Changes

## Result of text diff

The chapter is **verbatim identical** to v2 Chapter 6 modulo:

1. Chapter/section/theorem numbers incremented by 1 (6.x → 7.x).
2. External cross-references updated to v3 numbering.
3. PDF page numbers.

There are **zero** new statements, **zero** removed statements, and
**zero** substantive text changes.

## External cross-reference updates (all verified against v3 PDF)

| v2 reference | v3 reference | Content | Verified |
|---|---|---|---|
| Theorem 5.9 | Theorem 6.9 | Quantum Perron–Frobenius | ✓ (p. 29) |
| Theorem 5.10 | Theorem 6.10 | Right-canonical gauge | ✓ (p. 29) |
| Theorem 4.20 | Theorem 5.9 | KS equality ⇒ Kraus commutation | ✓ (p. 23) |
| Theorem 4.21 | Theorem 5.10 | KS equality for peripheral eigenvectors | ✓ (p. 23) |
| Definition 4.31 | Definition 4.20 | Fixed-point projection | ✓ (p. 16) |
| Theorem 4.32 | Theorem 4.21 | Power decomposition | ✓ (p. 16) |
| Theorem 3.9 | Theorem 3.9 | Skolem–Noether | ✓ (unchanged, p. 12) |
| Definition 2.2 | Definition 2.2 | Word evaluation | ✓ (unchanged, p. 6) |
| Definition 2.13 | Definition 2.13 | Gauge-phase equivalence | ✓ (unchanged, p. 7) |
| Definition 2.31 | Definition 2.31 | MPV overlap | ✓ (unchanged, p. 10) |

The nontrivial updates are:
- Theorems 4.20/4.21 → 5.9/5.10: KS material moved from v2 Ch 4 to v3 Ch 5.
- Definition 4.31/Theorem 4.32 → Definition 4.20/Theorem 4.21: Ch 4 renumbered after KS extraction.
- Theorems 5.9/5.10 → 6.9/6.10: Perron–Frobenius chapter shifted +1.

## Forward references (citations from later chapters into Chapter 7)

The following v3 Chapter 7 statements are cited downstream:

| Statement | Cited in | Context |
|---|---|---|
| Thm 7.10 | Ch 9 (p. 54) | Eigenvalue bound applied to blocked transfer map |
| Thm 7.12 | Ch 9 (p. 56, ×2) | Spectral rigidity reused for irreducible tensors |
| Thm 7.15 | Ch 11 (p. 65), Ch 11 (p. 66) | Rectangular overlap decay in BNT separation |
| Thm 7.17 | Ch 10 (p. 63), Ch 11 (p. 65, 67) | Overlap decay: contrapositive forces gauge-phase equiv |
| Thm 7.21 | Ch 9 (p. 54) | Self-overlap convergence from spectral gap |
| Thm 7.7 | Ch 10 (p. 62) | Overlap = transfer trace identity |

All forward references verified correct.

---

# Prior Review Items — Status Check

## From `blueprint_chapter6_review.md` (v1 review)

| Item | v1 Issue | v2 Fix | v3 Status |
|---|---|---|---|
| Thm 6.12 unsafe DS normalization | Critical: proof assumed doubly stochastic gauge | Rewritten with separate gauging | ✓ Intact in v3 as Thm 7.12. Crucial sentence preserved verbatim. |
| Thm 6.20 vacuous | Hypothesis tr(F^N(I))=0 impossible for D≥1 | Removed entirely | ✓ Still absent in v3. |
| Thms 6.18/6.19 trivial | Promoted to standalone theorems unnecessarily | Demoted to Remarks | ✓ Still Remarks 7.18/7.19 in v3. |
| Thm 6.3 trivial | F_AA = ℰ_A as theorem | Demoted to Remark | ✓ Still Remark 7.3 in v3. |
| Trace notation ambiguity | Mixed operator/matrix trace without distinction | Thm 6.5 disambiguation note added | ✓ Preserved verbatim in Thm 7.5. |
| Thm 6.10 proof: DS gauge | Used DS gauge | Rewritten with Cauchy–Schwarz + TP | ✓ Intact in v3 as Thm 7.10. |
| Normalization scope statement | Missing | Chapter preamble added | ✓ Preserved verbatim in v3 Ch 7 preamble. |

## From `blueprint_chapters2to6_review_consolidated.md`

**6-A. Definitions 7.1/7.2 still separate.**
Square and rectangular mixed transfer definitions remain as two separate
definitions. Acceptable for formalization (different Lean type signatures:
`M_D(ℂ) → M_D(ℂ)` vs `M_{D₁×D₂}(ℂ) → M_{D₁×D₂}(ℂ)`).
— *Minor. Acceptable for formalization. Unchanged from v2.*

**6-B. Theorem 7.12 proof: block-embedding KS argument still compressed.**
The proof of the spectral rigidity theorem remains a single paragraph.
For Lean formalization, the following intermediate steps should ideally be
separate lemmas:
1. Construction of the block Kraus family from A'_i and B'_i.
2. Gauging of the eigenvector X accordingly.
3. KS equality for the block family applied to the off-diagonal embedding.
4. Extraction of the intertwining identity from the Kraus commutation relation.
5. Invertibility of the intertwiner from injectivity.
— *Moderate (formalization readiness). Unchanged from v2.*

**6-C. Theorem 7.14 proof: rectangular case still compressed.**
The proof says "apply the same block-embedding Kadison–Schwarz argument
as in the square case." Since the rectangular case is not standard, the
adaptation deserves more detail. In particular, the step showing that a
modulus-one eigenvector X : M_{D₁×D₂}(ℂ) must be injective (as a linear
map ℂ^{D₂} → ℂ^{D₁}) should be more explicit.
— *Moderate (non-standard argument needs expansion). Unchanged from v2.*

## From `blueprint_review_comprehensive_reference.md`

**Part III (Notation):** No notation issues specific to this chapter.
The σ overload (spin config vs block permutation) does not arise in
Chapter 7 — σ appears here only as a spin configuration index, which is
correct.

**Part IV (Formalization notes):**
- 6-F1 (mixed transfer: different type from self-transfer): Still
  relevant. Definitions 7.1 and 7.2 correctly separate the types.
- 6-F2 (TP normalization required): Still relevant. The chapter preamble
  explicitly states where TP normalization begins (§7.3).

**Part V (Orphans):** No Chapter 7 statements appear in the orphan list.
All statements in this chapter are used downstream.

---

# Statement-by-Statement Analysis

Since the chapter is verbatim identical to v2 (modulo renumbering), the
statement-by-statement analysis from `blueprint_chapter6_review.md`
carries over with updated theorem numbers. The key points are:

**Definitions 7.1–7.2:** Correct. Standard mixed transfer operator.
Separate definitions acceptable for Lean type reasons.

**Remark 7.3:** Correct trivial observation. Appropriately a remark.

**Theorem 7.4:** Correct. Induction proof is standard.

**Theorem 7.5:** Correct. Trace disambiguation note is present and clear.

**Lemma 7.6:** Correct. Standard operator-trace expansion.

**Theorem 7.7:** Correct and central. Overlap ↔ transfer trace identity.

**Theorem 7.8:** Correct. Rectangular analogue of 7.7.

**Lemma 7.9:** Correct. Entrywise inner product interpretation.

**Theorem 7.10 (Eigenvalue bound):** Correct. Uses only TP normalization
and Cauchy–Schwarz. No PF theory needed. Proof is clear.

**Theorem 7.11 (Spectral radius bound):** Correct. Immediate corollary
of 7.10.

**Theorem 7.12 (Spectral rigidity):** Statement correct. Proof outline
correct (separate gauging, block KS argument, Skolem–Noether). The DS
gauge fix from v2 is intact. **Proof remains compressed** (item 6-B).
This is the most important theorem in the chapter for the FT proof chain.

**Theorem 7.13 (Strict spectral gap):** Correct. Contrapositive of 7.12
combined with 7.11.

**Theorem 7.14 (Rectangular spectral gap):** Statement correct. Proof
outline correct (ker(X) invariance, dimension contradiction). **Proof
remains compressed** (item 6-C).

**Theorem 7.15 (Rectangular overlap decay):** Correct. Direct from 7.14
and 7.8.

**Theorem 7.16 (Transfer powers → 0):** Correct. Gelfand formula
application.

**Theorem 7.17 (Overlap decay):** Correct. Load-bearing result used
extensively in Chapters 10–12.

**Remark 7.18 (Cross-correlation decay):** Correct. Scalar-trace
consequence of 7.16.

**Remark 7.19 (Self-correlation persists):** Correct. Fixed-point
property.

**Theorem 7.20 (Complementary gap ⇒ Tr → 1):** Correct. Uses power
decomposition (Thm 4.21) and Gelfand formula. The Tr(P) = 1 computation
is explicit. Cross-references to Def 4.20 and Thm 4.21 verified correct.

**Theorem 7.21 (Self-overlap convergence):** Correct. Direct from 7.7
and 7.20. Used downstream in Ch 9 (p. 54) for primitive overlap.

---

# Cross-Chapter Consistency

**DS gauge:** The chapter correctly avoids the DS gauge throughout. The
crucial sentence in Theorem 7.12's proof ("one gauges the individual
transfer maps to unital form; one does not require the mixed transfer map
itself to be simultaneously unital and trace-preserving") is preserved
verbatim from v2.

**KS machinery references:** Now correctly point to Chapter 5 (v3), which
is where the Kadison–Schwarz and multiplicative-domain material lives
after the restructuring. Theorems 5.9 and 5.10 are the correct targets.

**Perron–Frobenius references:** Now correctly point to Chapter 6 (v3).
Theorems 6.9 and 6.10 are the correct targets.

**Chapter 4 references:** Definition 4.20 (fixed-point projection) and
Theorem 4.21 (power decomposition) are correctly updated from the v2
numbering (4.31/4.32), reflecting the renumbering after KS extraction.

---

# Literature Alignment

The chapter follows [PGVWC07] for the spectral gap argument. The key
correspondence:

- The mixed transfer operator and overlap-as-trace identity are standard
  in [PGVWC07].
- The eigenvalue bound via Cauchy–Schwarz (Thm 7.10) is standard.
- The spectral rigidity argument (Thm 7.12) via block-embedding KS is
  the standard approach from [PGVWC07], correctly adapted to avoid the
  DS gauge issue.
- The rectangular case (Thm 7.14) is less standard but follows the same
  logic with the ker(X) dimension argument.

No deviations from the literature detected.

---

# AI-Language Audit

No AI-language issues detected in this chapter. The prose reads as
standard mathematical writing throughout. The chapter avoids all patterns
catalogued in Part II of the comprehensive reference:

- No "assembly," "pipeline," "bridge," "handoff" language.
- No formalization jargon ("stored as," "re-exports," "sorry-free").
- No unexpanded abbreviations.
- Section titles are descriptive and standard.

---

# Formalization Notes

**7-F1. Mixed transfer operator types (from 6-F1).**
Definitions 7.1 and 7.2 have different Lean types:
- 7.1: `M_D(ℂ) →ₗ M_D(ℂ)` (square endomorphism)
- 7.2: `M_{D₁×D₂}(ℂ) →ₗ M_{D₁×D₂}(ℂ)` (rectangular endomorphism)

The rectangular type is not a specialization of the square type in Lean.
Keeping both definitions is correct.

**7-F2. TP normalization scope (from 6-F2).**
§§7.1–7.2 are purely algebraic (no normalization). §7.3 onward assumes
TP normalization. The preamble explicitly states this boundary.

**7-F3. Theorem 7.12 proof chain.**
The proof of Theorem 7.12 involves the following type-level transitions:
1. QPF fixed points (Thm 6.9): ℰ_A has PSD fixed point → PD upgrade.
2. Right-canonical gauge (Thm 6.10): similarity → unital Kraus family.
3. Block Kraus family: `Fin 2D → M_{2D}(ℂ)` with off-diagonal embedding.
4. KS peripheral equality (Thm 5.10): equality condition in KS inequality.
5. Kraus commutation (Thm 5.9): eigenvector commutes with Kraus operators.
6. Skolem–Noether (Thm 3.9): automorphism is inner.

Each step is a separate Lean theorem. The blueprint compresses all six
into one paragraph.

**7-F4. Gelfand formula usage.**
Theorems 7.16 and 7.20 invoke the Gelfand formula (ρ(T) = lim ‖T^n‖^{1/n})
to convert spectral radius < 1 into operator norm convergence. This should
be available in Mathlib as `NNNorm.tendsto_nhds_zero_of_spectralRadius_lt_one`
or similar. Worth checking Mathlib status.

---

# Cleanup Checklist

## Must fix

(None. No mathematical errors and no broken references.)

## Should fix

**7-S1.** Expand Theorem 7.12 proof into separate lemmas for the five
steps of the block-embedding KS argument (item 6-B, carried from v2).
This is the main formalization bottleneck in the chapter.

**7-S2.** Expand Theorem 7.14 proof to make the rectangular ker(X)
argument explicit (item 6-C, carried from v2). The step showing that
ker(X) invariance under all B'_i forces injectivity of X should be
spelled out.

## Low priority

**7-L1.** Definitions 7.1/7.2 could in principle be unified into a single
definition with D₁ = D₂ as a special case. Acceptable as-is for Lean
(item 6-A).

## Acceptable as-is

- Remark 7.3 (self-transfer): trivial but harmless as a remark.
- Theorem 7.11 (spectral radius bound): immediate from 7.10 but useful
  as a named target for later citations.
- Remarks 7.18/7.19: correctly demoted from v1 theorems.

---

# Final Assessment

v3 Chapter 7 is a **pure renumbering** of v2 Chapter 6 with correctly
updated cross-references. No substantive changes were made. All v1→v2
corrections (DS gauge fix, vacuous theorem removal, trace disambiguation,
trivial theorem demotion) remain intact.

The chapter is mathematically correct and well-structured. The two
moderate open items (compressed proofs in Theorems 7.12 and 7.14) are
unchanged from v2 and remain the main formalization readiness concerns.

**Priority for formalization agent:** Expand Theorem 7.12 proof (the
spectral rigidity argument) into the five intermediate lemmas listed in
item 7-S1. This theorem is the most cited result from this chapter in
the FT proof chain.
