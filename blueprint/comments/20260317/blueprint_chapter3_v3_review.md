
# Blueprint Review — Chapter 3 (Single-Block Fundamental Theorem), v2 → v3

This document reviews Chapter 3 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter3_review.md`, `blueprint_chapters2to6_review_consolidated.md`,
`blueprint_review_comprehensive_reference.md`).

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. Standard algebraic proof of the injective FT. |
| Internal consistency | Good. No contradictions. |
| v2 → v3 changes | **None.** Chapter 3 is verbatim identical between v2 and v3. |
| AI language | One item: §3.4 title "Assembly." |
| Formalization readiness | Good. All statements have Lean declarations on the web blueprint. |
| Open items from prior review | Minor items unaddressed (acceptable). |

---

# v2 → v3 Changes

**Chapter 3 is completely unchanged between v2 and v3.** Verified by
full-text diff: zero differences.

Chapter 3 is self-contained: it references only Chapter 2 definitions
(Def 2.4 for MPV coefficients, via Lemma 3.2) and has no forward
references to later chapters. Therefore the renumbering of later chapters
in v3 does not affect it.

---

# Review Items: Prior Status Check

## From blueprint_chapter3_review.md (original review)

The original review was written against v1 and identified several issues,
most of which were already resolved in v2. The review file references v1
numbering (e.g., "Lemma 3.3" for the length-2 trace identity, "Lemma 3.6"
for the generic range-inclusion lemma), which were removed or restructured
in v2. Below I track the v2/v3 status of each.

| # | Item (v1 numbering) | Status in v2/v3 |
|---|---|---|
| 1 | Remove redundant Lemma 3.3 (length-2 trace identity) | ✅ Removed in v2. |
| 2 | Label trace-pairing maps as auxiliary | ✅ Chapter preamble does this since v2. |
| 3 | Merge generic Lemma 3.6 (range inclusion → injectivity) | ✅ Absorbed into Thm 3.6 proof in v2. |
| 4 | Demote Theorem 3.7 (nonvanishing trace) to remark | ❌ Still a standalone theorem (now Thm 3.5). |
| 5 | Make "nonzero" explicit in simplicity theorem | ✅ Thm 3.8 says "nonzero" since v2. |
| 6 | Define the generated algebra explicitly | ❌ Not defined. The v3 text does not introduce 𝒜(A) = span{A^w}. |
| 7 | Merge §3.4 into §3.3 | ❌ §3.4 remains separate. Acceptable: Thm 3.11 is a clean final statement. |

## From consolidated review (remaining open items)

| # | Item | Status in v3 |
|---|---|---|
| 3-A | Thm 3.5 still standalone (stylistic) | ❌ Unchanged. Acceptable for Lean (named lemma in the assembly proof). |

## From comprehensive reference

| # | Item | Status in v3 |
|---|---|---|
| Part II | "Assembly" as §3.4 title | ❌ Unchanged. AI-language item. |
| 3-F1 | Linear extension type chain (6 Lean transitions) | Unchanged. No new issues. |
| 3-F2 | Surjectivity from simplicity (3 sub-steps) | Unchanged. No new issues. |

---

# Statement-by-Statement Analysis

All statements unchanged from v2. The v2 review confirmed them as correct.

## Theorem 3.1 (Nondegeneracy of the trace pairing)

Correct. Standard result: tr(MN) = 0 for all N ⟹ M = 0. Proof via
matrix units is clean.

## Lemma 3.2 (Same MPV implies trace agreement)

Correct. Same MPV ⟹ tr(A^w) = tr(B^w) for all words w. This is the
only place in the entire v3 blueprint where c_w(A) is used (confirming
the Ch 2 analysis).

## Definition 3.3 (Trace pairing map)

Correct. Φ_A(M)_i = tr(M·A^i). The chapter preamble explicitly labels
this as an "auxiliary device," addressing the original review concern.

## Theorem 3.4 (Injectivity of the trace pairing map)

Correct. Injective tensor ⟹ ker Φ_A = {0}. Clean proof via
Theorem 3.1.

## Theorem 3.5 (Nonvanishing trace on injective tensors)

Correct. If D ≥ 1, A injective, A and B same MPV, B^i = 0 for all i,
then contradiction. Used in Theorem 3.11 to establish T ≠ 0.

The original review recommended demoting this to a remark. It remains a
standalone theorem. For Lean, this is acceptable: it's a named lemma
invoked explicitly in the proof of Theorem 3.11.

**Subtlety for Lean (not previously flagged):** The hypothesis D ≥ 1 is
necessary (if D = 0, M_D(ℂ) is trivial and tr(𝟙) = 0). The blueprint
states this explicitly. Good.

## Theorem 3.6 (Existence and uniqueness of the linear extension)

Correct. The proof constructs T = g ∘ Φ_A where g is a left inverse of
Φ_B. The range-inclusion argument (v1's standalone Lemma 3.6) is now
properly inlined.

**Precision check:** The proof says "A left inverse g of Φ_B gives
T := g ∘ Φ_A." This requires ker Φ_B = {0}, which is established in the
same proof paragraph via rank-nullity. The logic is: ker Φ_A = {0}
(Thm 3.4) → dim(range(Φ_A)) = D² → range(Φ_A) ⊆ range(Φ_B) (from trace
agreement on length-2 words) → dim(range(Φ_B)) ≥ D² → ker Φ_B = {0}. ✅

**Note for formalization agent:** The "left inverse g" is not constructed
explicitly; its existence follows from ker Φ_B = {0} (injective linear map
on a finite-dimensional space has a left inverse). In Lean, this is
`LinearMap.lTensor` or explicit section construction.

## Theorem 3.7 (Multiplicativity of the linear extension)

Correct. Three-step proof:
1. Φ_B ∘ T = Φ_A (from trace agreement on length-2 words)
2. T(A^i A^j) = B^i B^j (from trace agreement on length-3 words + injectivity of Φ_B)
3. Bilinear extension to all of M_D(ℂ)

**Precision check on Step 3:** The proof says "For fixed j, the maps
M ↦ T(M · A^j) and M ↦ T(M) · B^j agree on the spanning set {A^i},
hence on all of M_D(ℂ)." This uses that {A^i} span M_D(ℂ) (injectivity
of A). Then "applying this once more with j replaced by a general matrix"
uses that {A^j} also span M_D(ℂ). Both uses of spanning are correct. ✅

## Theorem 3.8 (Simplicity of M_D(ℂ))

Correct. Nonzero multiplicative ℂ-linear endomorphism of M_D(ℂ) is
bijective. "Nonzero" is explicitly stated (fixed in v2). Proof via
simplicity (no nontrivial two-sided ideals) + finite-dimensionality.

## Theorem 3.9 (Skolem-Noether)

Correct. Every ℂ-algebra automorphism of M_D(ℂ) is inner. Standard
result in the theory of central simple algebras.

**Note for formalization agent (3-F1):** In Lean, this is the endpoint
of the six-step type chain: ℂ-linear → multiplicative → nonzero →
bijective → unital (Lemma 3.10) → inner automorphism (Skolem-Noether).
Each step is a separate Lean theorem.

## Lemma 3.10 (Promotion to algebra homomorphism)

Correct. Multiplicative + surjective ⟹ T(𝟙) = 𝟙. The proof is clean:
pick X with T(X) = 𝟙, then T(𝟙) = T(X)·T(𝟙) = T(X·𝟙) = T(X) = 𝟙.

## Theorem 3.11 (Single-block Fundamental Theorem)

Correct. This is the main result of the chapter. Statement: injective A,
same bond dimension B, same MPV ⟹ gauge equivalent. Proof chains
Thms 3.6 → 3.7 → 3.5 → 3.8 → 3.10 → 3.9.

The proof is concise and well-structured. Each step is clearly attributed
to its theorem number.

---

# Cross-Chapter Consistency

## References from Chapter 3

| Reference | Target | Status |
|---|---|---|
| Lemma 3.2 → Definition 2.4 | MPV coefficient c_w(A) | ✅ Correct |

No other cross-chapter references. Chapter 3 is self-contained.

## References to Chapter 3 from later chapters

Chapter 3's Theorem 3.11 is the single-block FT. It is used in:
- Chapter 9 (§9.5, Proportional single-block theorem) — to be verified
- Chapter 12 (Full Assembly) — to be verified

These will be checked when we review those chapters.

---

# Literature Alignment

The proof strategy (trace pairing → linear extension → multiplicativity →
simplicity → Skolem-Noether) is the standard algebraic route for the
injective case. This matches [PGVWC07] and [CPGSV21].

No deviations from the literature.

---

# AI-Language Audit

## From comprehensive reference Part II

| Pattern | Location | Status in v3 | Recommended fix |
|---|---|---|---|
| "Assembly" | §3.4 title | ❌ Unchanged | → "Proof of the single-block theorem" or simply remove the section title and fold into §3.3. |

## Additional items in Chapter 3

| Phrase | Location | Issue | Recommended fix |
|---|---|---|---|
| "auxiliary devices attached to the chosen generating families" | Chapter preamble | Slightly unusual but acceptable — correctly labels the maps as non-canonical. | No change needed (addresses original review concern). |
| "they serve only to construct the linear map that is later shown to be a gauge transform" | Chapter preamble | Acceptable expository sentence. | No change needed. |

Chapter 3 has very little AI-language. The §3.4 "Assembly" title is the
only item that should be changed.

---

# Formalization Notes

From the comprehensive reference Part IV, §Chapter 3. No changes in v3.

| # | Note | Status |
|---|---|---|
| 3-F1 | Six-step type chain in Thm 3.11: ℂ-linear → multiplicative → nonzero → bijective → unital → inner automorphism | Unchanged. Each step is a separate Lean theorem. |
| 3-F2 | Surjectivity from simplicity: ker = two-sided ideal → simplicity → ker = {0} → injective → (finite-dim) surjective | Unchanged. Three sub-steps in Lean. |

No new formalization issues introduced in v3.

---

# Cleanup Checklist for Chapter 3

## Must fix (AI language)

1. **§3.4 title:** "Assembly" → "Proof of the single-block theorem."

## Low priority (stylistic, acceptable for Lean)

2. **Theorem 3.5 as standalone theorem:** Could be a lemma or remark,
   but as a named Lean lemma it is fine.

3. **Generated algebra not defined:** The algebra 𝒜(A) = span{A^w}
   is never explicitly introduced. The proofs work without it (they
   use "the {A^i} span M_D(ℂ)" directly from the injectivity
   hypothesis). For a mathematical document this is slightly informal;
   for the Lean formalization, the spanning property is used directly
   without naming the algebra, so this is fine.

---

# Final Assessment

Chapter 3 is mathematically sound and completely unchanged from v2. The
proof of the single-block fundamental theorem is clean, correct, and
well-structured. All original review issues were resolved in v2 except
minor stylistic items (Thm 3.5 promotion, §3.4 title).

The only actionable item is renaming §3.4 from "Assembly" to something
a mathematician would actually write, such as "Proof of the single-block
theorem."

**Chapter 3 is mathematically sound. The only remaining issue is the
§3.4 section title.**
