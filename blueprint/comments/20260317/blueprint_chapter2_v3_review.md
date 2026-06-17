
# Blueprint Review — Chapter 2 (Matrix Product Vectors), v2 → v3

This document reviews Chapter 2 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter2_review.md`, `blueprint_chapters2to6_review_consolidated.md`,
`blueprint_review_comprehensive_reference.md`).

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. Remark 2.20 now properly states the equivalence with [SPGWC10, Prop 3]. |
| Internal consistency | Good. No contradictions within the chapter. |
| v2 → v3 changes | Minimal. Only Remark 2.20 substantively changed. |
| AI language | Several items remain from v2, catalogued below. |
| Formalization readiness | Good. Lean declarations confirmed on web blueprint. |
| Open items from prior review | One major item (X-1) addressed; minor items mostly unaddressed. |

---

# v2 → v3 Changes

## Substantive changes

**1. Remark 2.20 rewritten (normality equivalence).** This is the only
substantive change in Chapter 2.

v2 text: "In the block-injective route developed here, 'normal' means
eventual block injectivity. The NT notion in [CPGSV21] is spectral: it is
phrased in terms of irreducibility and the peripheral spectrum of the
transfer map. The bridge to that viewpoint is supplied later by
Theorem 8.26, Theorem 7.45, and Theorem 7.52."

v3 text: "The algebraic characterization of normality in Definition 2.19 —
eventual full Kraus rank, equivalently eventual block injectivity — is
equivalent to the spectral characterization used in [CPGSV21,
Definition IV.1]: after TP normalization, the transfer map ℰ_A is a
primitive channel, equivalently irreducible with trivial peripheral
spectrum. This equivalence is proved in [SPGWC10, Proposition 3]. Within
this blueprint, the directions of the equivalence are supplied by
Theorem 8.49, Theorem 8.59, and Theorem 9.27. In particular, every
subsequent use of 'normal' in this blueprint refers to this single notion;
Definition 9.29 employs the spectral formulation, but it describes the same
class of tensors."

Assessment: This directly addresses the cross-chapter item X-1 (two
characterizations of "normal") that was flagged throughout the review
process. The fix is mathematically correct:

- The [SPGWC10, Proposition 3] citation is correct.
- The three forward references have been verified (see §Forward Reference
  Verification below).
- The sentence about Definition 9.29 is new and helpful: it pre-empts
  confusion when the reader encounters a spectral-looking definition later.

**Remaining concern:** The consolidated review (item X-1) recommended
renaming Def 2.19 to "eventually injective tensor" to reserve "normal" for
the [CPGSV17/CPGSV21] spectral sense. This was not done. The improved
Remark 2.20 is a good mitigation — it makes the equivalence explicit and
cites the proof — but the terminological tension persists: someone reading
only Definition 2.19 might not realize "normal" carries a spectral
connotation in the literature. The remark makes this acceptable but worth
noting for the formalization agent.

## Non-substantive changes

**2. Chapter 1 Introduction.** Chapter references updated to match v3
numbering (e.g., "Chapters 5 and 6" → "Chapters 6 and 7"). No content
change.

## Unchanged

Everything else in Chapter 2 is verbatim identical between v2 and v3:
Definitions 2.1–2.19, 2.21–2.31, Lemmas 2.3, 2.12, 2.15, 2.26, 2.27,
2.32, Theorems 2.16, 2.24, 2.28, Remarks 2.6, 2.10, 2.14, 2.22.

---

# Forward Reference Verification

All forward references from Chapter 2 have been verified directly against
the v3 PDF text.

## Remark 2.20 references

**Theorem 8.49 (§8.10.2).** "Primitive with PosDef fixed point implies
irreducible tensor." Statement: If A is a primitive MPS tensor with PSD
fixed point ρ and ρ is positive definite, then A is an irreducible tensor.
Cites [SPGWC10, Proposition 3].

Role in the equivalence: provides the direction primitive → irreducible.
This is one direction of the "normal" equivalence chain. ✅ Verified.

**Theorem 8.59 (§8.10.3).** "Irreducible tensor plus aperiodicity implies
normality." Statement: If A is an irreducible tensor, D > 0, and 𝟙 ∈ S₁(A),
then A is normal. Uses Burnside (forward reference to Theorems 9.20–9.21),
then Theorem 8.58.

Role in the equivalence: provides the direction irreducible + aperiodic →
normal (in the algebraic sense of Def 2.19). ✅ Verified.

Note: Theorem 8.59 has a forward dependency on Theorems 9.20–9.21
(Burnside bridge) in Chapter 9. The blueprint explicitly acknowledges this
as a "presentation-level forward dependency" with acyclic mathematical
dependency. This is acceptable but should be tracked by the formalization
agent.

**Theorem 9.27 (§9.6).** "Blocking yields a peripheral-spectrum primitive
transfer map." Statement: If A is irreducible with TP normalization and
D > 0, then there exists a blocking length p > 0 such that ℰ_{A[p]} is
primitive (peripheral spectrum = {1}).

Role in the equivalence: provides the direction irreducible → primitive
(after blocking). This completes the cycle: normal (algebraic) →
irreducible → primitive (after blocking) → normal (spectral). ✅ Verified.

**Definition 9.29 (§9.7).** "Normal canonical form predicate." Lists six
conditions: each block irreducible, TP normalized, primitive transfer map,
strictly decreasing moduli, nonzero scaling, positive bond dimensions. The
definition text explicitly states: "As noted in the remark after
Definition 2.19, this is equivalent to the eventual block-injectivity
formulation of Definition 2.19; see [SPGWC10, Proposition 3]."

Role: this is the spectral formulation of "normal" that Remark 2.20 says
describes the same class of tensors as Def 2.19. The back-reference in
Def 9.29 to Remark 2.20 confirms bidirectional consistency. ✅ Verified.

## Remark 2.22 reference

**"The paper-faithful NT/BNT/CFII route is developed later in Chapter 9."**

Verified: Chapter 9 contains the CFII construction in Theorems 9.33–9.34.
Theorem 9.33 ("CFII data for irreducible TP blocks") explicitly references
[CPGSV17, Appendix A]. Chapter numbering is correct. ✅ Verified.

## Other forward references

**Remark 2.6 → Chapter 4.** "The abstract positive-map framework appears in
Chapter 4." Chapter 4 is titled "Quantum Channels and Positive Maps."
✅ Consistent.

---

# Review Items: Prior Status Check

## From blueprint_chapter2_review.md (original review)

| # | Item | Status in v3 | Detail |
|---|---|---|---|
| 1 | Explicitly define V^{(N)}(A)_σ | ✅ | In Def 2.4 since v2. |
| 2 | Remove c_w(A) if unused | ❌ | Still in Def 2.4. Now verified: used exactly once, in Lemma 3.2 proof. See analysis below. |
| 3 | Merge Defs 2.8/2.9 | ❌ | Not merged. Two separate Lean types (SameMPV, SameMPV₂). Justified. |
| 4 | Simplify Lemma 2.3 proof | ✅ | Done in v2. |
| 5 | Merge Lemma 2.24 into 2.25 | ✅ | Restructured in v2 (now 2.26/2.27). |
| 6 | Clarify Def 2.19 (normal) | ✅ | Remark 2.20 rewritten in v3. |
| 7 | Rename "canonical form" | Partial | "Block-injective CF" since v2. Remark 2.22 distinguishes from NT-block CF. |
| 8 | Remove redundant Def 2.23 | ❌ | Still present. Constructor vs data package — justified for Lean. |
| 9 | Move positivity to Ch 4 | ✅ | Remark 2.6 since v2. |
| 10 | Prefer MPV terminology | ✅ | Consistent since v2. Def 2.1 title "MPS tensor" is standard for the object itself. |
| 11 | Block-index notation | ✅ | Uses tuples since v2. |
| 12 | Clarify overlap | ✅ | §2.6 clean since v2. |

## From consolidated review (remaining open items)

| # | Item | Status in v3 | Detail |
|---|---|---|---|
| 2-A | c_w(A) possibly unused after Ch 3 | ✅ Resolved | Now verified: c_w(A) is used exactly once in the entire v3 document, in the proof of Lemma 3.2 (Chapter 3). No chapter beyond Chapter 3 uses it. |
| 2-B | Defs 2.8/2.9 split | Acceptable | Two Lean types (SameMPV, SameMPV₂). |
| 2-C | Def 2.23 vs 2.21 redundancy | Acceptable | Constructor vs data (Lean). |

## From comprehensive reference (cross-chapter items)

| # | Item | Status in v3 | Detail |
|---|---|---|---|
| X-1 | Two characterizations of "normal" | ✅ Addressed | Remark 2.20 rewritten with explicit equivalence statement and [SPGWC10] citation. Not fully resolved (terminology not renamed). |
| X-2 | Def 8.1 duplicates Def 2.23 | Pending | Will check when reviewing Chapter 8. |
| N-4 | c_w(A) possibly unused | ✅ Resolved | Used once in Lemma 3.2, nowhere else. |

---

# c_w(A) Usage Analysis (Item 2-A / N-4, Now Resolved)

The notation c_w(A) := tr(A^w) is introduced in Definition 2.4. A search
of the full v3 PDF text reveals exactly two occurrences:

1. **Definition 2.4 (Chapter 2):** Introduction of the notation.
2. **Lemma 3.2 proof (Chapter 3):** "Definition 2.4 gives the corresponding
   MPV coefficient as the trace coefficient c_w(A) = tr(A^w)."

No other chapter uses c_w(A). Every subsequent reference to trace
coefficients writes tr(A^w) directly.

**Recommendation:** The notation is harmless but adds no value beyond
Chapter 3. Two options:

(a) Remove c_w(A) from Def 2.4 and write tr(A^w) directly in the Lemma 3.2
proof (which already explains the meaning inline). This is the cleaner
option.

(b) Keep it as a minor convenience for Chapter 3. Acceptable if the
formalization agent finds it useful as a Lean definition.

This is a low-priority stylistic item. It does not affect correctness.

---

# Statement-by-Statement Analysis

All statements are unchanged from v2, which was previously verified as
correct. Below I note items that are relevant for the v3 audit or the
formalization agent.

## Definition 2.1 (MPS tensor)

Correct. Title says "MPS tensor" while the chapter works with MPV families.
Acceptable: "MPS tensor" is the standard name for the object; "MPV" refers
to the vectors it generates. The Lean declaration is `MPSTensor`.

## Definition 2.2 (Word evaluation)

Correct. Convention A^∅ = 𝟙_D is explicitly stated. Lean declaration:
`MPSTensor.evalWord`.

## Lemma 2.3 (Word evaluation respects concatenation)

Correct. Proof is appropriately brief ("Immediate from the definition of
A^w"). Lean declaration: `MPSTensor.evalWord_append`.

**AI-language issue in title.** See §AI-Language Audit.

## Definition 2.4 (Matrix product vector)

Correct. Defines both the ket form and the coefficient function
V^{(N)}(A)_σ := tr(A^{i₁}⋯A^{i_N}) explicitly. Also introduces c_w(A)
(see §c_w(A) Usage Analysis). Lean declaration: `MPSTensor.mpv`.

## Definition 2.5 (Transfer map)

Correct. Standard Kraus-form definition ℰ_A(X) = ∑ A^i X (A^i)†. Lean
declaration: `MPSTensor.transferMap`.

## Remark 2.6 (Positivity of transfer map)

Correct. States positivity as an immediate observation with forward
reference to Chapter 4. Appropriate for a remark rather than a lemma.

## Definition 2.7 (Gauge equivalence)

Correct. B^i = X A^i X^{-1} for X ∈ GL_D(ℂ). Lean declaration:
`MPSTensor.GaugeEquiv`.

## Definition 2.8 (Same MPV — equal bond dimension)

Correct. V^{(N)}(A) = V^{(N)}(B) for all N ≥ 1. Lean declaration:
`MPSTensor.SameMPV`.

## Definition 2.9 (Same MPV — different bond dimensions)

Correct. Same condition, allowing D₁ ≠ D₂. Lean declaration:
`MPSTensor.SameMPV₂`.

## Remark 2.10

Correct. Justifies keeping both Defs 2.8 and 2.9. The Lean formalization
uses both (different type signatures).

## Definition 2.11 (Proportional MPV)

Correct. V^{(N)}(A) = c_N V^{(N)}(B) for some c_N ∈ ℂ. Lean declaration:
`MPSTensor.ProportionalMPV₂`.

**Subtlety for Lean:** The definition allows c_N = 0 for some N. This is
mathematically fine (proportional includes the zero vector case), but the
formalization agent should be aware that "proportional" does not imply
"nonzero proportionality constant."

## Lemma 2.12 (Word evaluation under scaling)

Correct. (ζA)^w = ζ^{|w|} A^w. Straightforward induction. Lean
declaration: `MPSTensor.evalWord_smul`.

## Definition 2.13 (Gauge-phase equivalence)

Correct. B^i = ζ X A^i X^{-1} for X ∈ GL_D(ℂ), ζ ∈ ℂ\{0}. Lean
declaration: `MPSTensor.GaugePhaseEquiv`.

## Remark 2.14

Correct. Notes that after spectral-radius normalization, ζ can be
restricted to a phase. The general form is kept for later canonical-form
statements.

## Lemma 2.15 (Word evaluation under conjugation)

Correct. B^w = X A^w X^{-1}. Lean declaration:
`MPSTensor.evalWord_gauge`.

## Theorem 2.16 (Gauge invariance of MPVs)

Correct. Gauge equivalent ⇒ same MPV family, by cyclicity of trace.
Lean declaration: `MPSTensor.GaugeEquiv.sameMPV`.

## Definition 2.17 (Injectivity)

Correct. span{A^i} = M_D(ℂ). Lean declaration:
`MPSTensor.IsInjective`.

**Note for formalization agent:** This is 1-block injectivity (Def 2.18
with L=1). The implication is stated explicitly in Def 2.18.

## Definition 2.18 (L-block injectivity)

Correct. span{A^{i₁}⋯A^{i_L}} = M_D(ℂ). Lean declaration:
`MPSTensor.IsNBlkInjective`.

## Definition 2.19 (Normal tensor)

Correct. ∃L₀ such that A is L₀-block injective. Lean declaration:
`MPSTensor.IsNormal`.

This is the algebraic definition. The spectral equivalence is stated in
Remark 2.20, verified above. The [CPGSV21] citation is correct.

## Remark 2.20 (Normality equivalence)

**Rewritten in v3.** See §v2→v3 Changes above for full analysis. The new
text is correct and well-sourced.

**One precision issue:** The remark says "eventual full Kraus rank,
equivalently eventual block injectivity." Strictly speaking, "full Kraus
rank" means rank(ℰ_A) = D² after enough iterations, which is the same as
block injectivity (the word-product matrices span M_D). The equivalence is
immediate but the phrase "Kraus rank" is not defined in the blueprint. For
a Lean formalization, this is not a problem (the formal definition is
Def 2.19), but a reader might wonder where "Kraus rank" was introduced.

**Recommendation:** Either define "Kraus rank" or replace "eventual full
Kraus rank" with "eventual full matrix span" or similar self-contained
phrasing.

## Definition 2.21 (Block-injective canonical form)

Correct. Block-diagonal tensor with injective blocks and scaling factors.
Lean declaration: `MPSTensor.CanonicalForm`.

**Phrase "In this blueprint" appears.** See §AI-Language Audit.

## Remark 2.22

Correct. Distinguishes block-injective CF from the NT-block CF of
[CPGSV21]. Forward reference to Chapter 9 verified (CFII in Thms 9.33–34).

**Phrases "In this blueprint" and "block-injective package" appear.** See
§AI-Language Audit.

## Definition 2.23 (Block-diagonal tensor from blocks)

Correct. Same construction as Def 2.21 but presented as a constructor.
Lean declaration: `MPSTensor.toTensorFromBlocks`.

Mathematically redundant with Def 2.21 (both describe A^i = ⊕_k μ_k A_k^i).
Justified in Lean: Def 2.21 is a predicate (CanonicalForm), Def 2.23 is a
constructor (toTensorFromBlocks).

## Theorem 2.24 (MPV decomposition)

Correct. V^{(N)}(A) = ∑_k μ_k^N V^{(N)}(A_k). Uses Lemma 2.12 and
block-diagonal trace. Lean declaration:
`MPSTensor.mpv_toTensorFromBlocks_eq_sum`.

## Definition 2.25 (Blocked tensor)

Correct. (A[L])^{(i₁,...,i_L)} = A^{i₁}⋯A^{i_L}. Uses tuple indexing
(not flattened integers, as recommended in the original review).

## Lemma 2.26 (Blocked word evaluation)

Correct. (A[L])^w = A^{w̃} where w̃ is the concatenation.

## Lemma 2.27 (Blocking preserves MPV coefficients)

Correct. V^{(N)}(A[L])_σ = V^{(NL)}(A)_{σ̃}.

## Theorem 2.28 (Blocking preserves same MPV)

Correct. Same MPV ⇒ same MPV after blocking.

## Definition 2.29 (MPV as Hilbert-space vector)

Correct. Identifies V^{(N)}(A) as an element of ℂ^{d^N}.

## Definition 2.30 (MPV inner product)

Correct. Sesquilinear, conjugate-linear in first argument. Consistent with
physics convention.

## Definition 2.31 (MPV overlap)

Correct. Bilinear (no conjugation). O_{AB}(N) = ∑_σ V_σ(A) V_σ(B).

**Minor:** Text says "bilinear physics-oriented overlap." The phrase
"physics-oriented" is imprecise. What matters is that this is bilinear
(both arguments unconjugated), used in the transfer-matrix formalism.

## Lemma 2.32 (Overlap equals conjugate inner product)

Correct. O_{AB}(N) = ⟨V(A)|V(B)⟩̄. The conjugation bridge between the
sesquilinear inner product and the bilinear overlap.

**Formalization note (2-F4):** This lemma is the Lean bridge between the
two bilinear forms. Required whenever a sesquilinear result (e.g., Gram
matrix invertibility) is applied to the bilinear overlap.

---

# Literature Alignment

No issues. Chapter 2 definitions are standard and correctly attributed:

- [CPGSV21] for the "normal" terminology (Def 2.19)
- [SPGWC10, Proposition 3] for the equivalence (Remark 2.20)
- [PGVWC07] and [CPGSV21] for the canonical form (Def 2.21)

The only literature-sensitive point — the meaning of "normal" — is now
properly addressed.

---

# AI-Language Audit

## Items from comprehensive reference Part II

| Pattern | Location | Status in v3 | Recommended fix |
|---|---|---|---|
| "word evaluation respects concatenation" | Lemma 2.3 title | ❌ Unchanged | → "Multiplicativity of word evaluation" |
| "In this blueprint" | Def 2.21 | ❌ Unchanged | → "Here" or remove |
| "In this blueprint" / "block-injective package" | Remark 2.22 | ❌ Unchanged | → "Here" / → "block-injective form" |

## New AI-language items in v3

| Phrase | Location | Issue | Recommended fix |
|---|---|---|---|
| "Word evaluation under scaling" | Lemma 2.12 title | "Under X" is an unusual lemma-naming pattern in mathematics. | → "Scaling of word evaluation" or "Word evaluation of a rescaled tensor" |
| "Word evaluation under conjugation" | Lemma 2.15 title | Same pattern. | → "Gauge covariance of word evaluation" or "Conjugation equivariance of word evaluation" |
| "Within this blueprint" | Remark 2.20 (new) | Same self-reference pattern as "in this blueprint." | → "In what follows" or remove |
| "bilinear physics-oriented overlap" | Def 2.31 | "Physics-oriented" is vague. | → "bilinear overlap (without complex conjugation)" |
| "eventual full Kraus rank" | Remark 2.20 (new) | "Kraus rank" not defined in the blueprint. | → "eventual full matrix span" (self-contained) or define "Kraus rank" |

## Acceptable naming conventions (no change needed)

- "MPS tensor" (Def 2.1) — standard
- "Block-injective canonical form" (Def 2.21) — useful identifier
- "Transfer map" (Def 2.5) — standard
- "Gauge-phase equivalence" (Def 2.13) — clear compound term

---

# Formalization Notes

From the comprehensive reference Part IV, §Chapter 2. No changes in v3.

| # | Note | Status |
|---|---|---|
| 2-F1 | Tensor as `Fin d → Matrix (Fin D) (Fin D) ℂ` | Unchanged. |
| 2-F2 | Same-MPV: two predicates (`SameMPV` vs `SameMPV₂`) | Unchanged. |
| 2-F3 | Block-diagonal tensor as dependent type | Unchanged. |
| 2-F4 | Overlap (bilinear) vs inner product (sesquilinear): Lemma 2.32 bridge | Unchanged. |

No new formalization issues introduced in v3.

---

# Cleanup Checklist for Chapter 2

## Must fix (AI language)

1. **Lemma 2.3 title:** "Word evaluation respects concatenation" →
   "Multiplicativity of word evaluation."

2. **"In this blueprint" / "Within this blueprint":** Replace in Def 2.21,
   Remark 2.22, and Remark 2.20 with "here" or "in what follows."

3. **Remark 2.22:** "block-injective package" → "block-injective form."

## Should fix (clarity)

4. **Lemma 2.12 title:** "Word evaluation under scaling" → rephrase (e.g.,
   "Scaling of word evaluation").

5. **Lemma 2.15 title:** "Word evaluation under conjugation" → rephrase
   (e.g., "Gauge covariance of word evaluation").

6. **Def 2.31:** "bilinear physics-oriented overlap" → "bilinear overlap
   (without complex conjugation)."

7. **Remark 2.20:** "eventual full Kraus rank" → "eventual full matrix
   span" (unless "Kraus rank" is defined elsewhere).

## Low priority (stylistic)

8. **c_w(A) in Def 2.4:** Used only once (Lemma 3.2 proof). Consider
   removing or downgrading to an inline remark.

## Acceptable as-is (justified for formalization)

9. Defs 2.8/2.9 split (two Lean types).
10. Def 2.23 alongside Def 2.21 (constructor vs data package).

---

# Final Assessment

Chapter 2 is mathematically sound and essentially unchanged from v2. The
one substantive change — Remark 2.20 on the equivalence of the algebraic
and spectral definitions of "normal" — is correct and addresses the most
important cross-chapter issue (X-1) from the prior review. All forward
references have been verified against the v3 PDF.

The remaining open items are: AI-language cleanup (7 phrases), one
undefined term ("Kraus rank" in Remark 2.20), and one low-priority
stylistic choice (c_w(A) notation). None affect mathematical correctness
or formalizability.

**Chapter 2 is ready for formalization modulo the language cleanup.**
