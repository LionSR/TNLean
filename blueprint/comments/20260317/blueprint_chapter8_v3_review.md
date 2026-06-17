
# Blueprint Review — Chapter 8 (Wielandt Bound), v2 → v3

This document reviews Chapter 8 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter7_review.md`, `wielandt_comparison_with_paper.md`,
`blueprint_review_comprehensive_reference.md`).

---

## Chapter numbering map

v3 Chapter 8 = v2 Chapter 7 (Wielandt Bound). The chapter is renumbered
+1 due to the new Chapter 5 (Schwarz Inequalities) inserted in v3.

v3 has 61 numbered statements (8.1–8.61) vs v2's 54 (7.1–7.54). The
7 new statements are: Thms 8.14–8.16 (sharp bounds), Thm 8.28 (general
Wielandt inequality), Thms 8.50–8.52 (primitivity bridge without
aperiodicity).

| v2 | v3 | Content | Change |
|---|---|---|---|
| Def 7.1 | Def 8.1 | Word span | Renumbered; **citation fixed** |
| Def 7.2 | Def 8.2 | Cumulative span | Renumbered |
| Lemma 7.3 | Lemma 8.3 | Monotonicity | Renumbered |
| Lemma 7.4 | Lemma 8.4 | Dimension bound | Renumbered |
| Thm 7.5 | Thm 8.5 | Stabilisation | Renumbered |
| Thm 7.6 | Thm 8.6 | Dimension growth | Renumbered |
| Lemma 7.7 | Lemma 8.7 | Word span = block injectivity | Renumbered |
| Def 7.8 | Def 8.8 | Fitting decomposition | Renumbered |
| Thm 7.9 | Thm 8.9 | Fitting exists | Renumbered |
| Thm 7.10 | Thm 8.10 | Nilpotent power bound | Renumbered |
| Thm 7.11 | Thm 8.11 | Cumulative span reaches M_D | Renumbered |
| Thm 7.12 | Thm 8.12 | T_{D²} = M_D | Renumbered |
| Thm 7.13 | Thm 8.13 | Nonzero trace product | **D ≥ 1 caveat added** |
| — | Thm 8.14 | Sharp cumulative span bound (D²−d'+1) | **New** |
| — | Thm 8.15 | Sharp nonzero trace product | **New** |
| — | Thm 8.16 | Sharp trace product (positive length) | **New** |
| Thm 7.14 | Thm 8.17 | Nonzero trace ⟹ eigenvector | **Proof expanded** |
| Thm 7.15 | Thm 8.18 | Eigenvalue extraction | Renumbered |
| Def 7.16 | Def 8.19 | Cumulative vector span | Renumbered |
| Thm 7.17 | Thm 8.20 | Vector span stabilisation | Renumbered |
| Lemma 7.18 | Lemma 8.21 | Vector span from matrix span | Renumbered |
| Thm 7.19 | Thm 8.22 | Eigenvector spreading | Renumbered |
| Def 7.20 | Def 8.23 | Wielandt analysis | Renumbered |
| Thm 7.21 | Thm 8.24 | Wielandt analysis exists | Renumbered |
| Thm 7.22 | Thm 8.25 | Wielandt chain | Renumbered |
| Thm 7.23 | Thm 8.26 | Wielandt bound | **Citation clarified** |
| Remark 7.24 | Remark 8.27 | Blocking-length estimates | **Expanded** |
| — | Thm 8.28 | Wielandt's inequality (general bound) | **New** |
| Def 7.25 | Def 8.29 | Fixed-length vector span | Renumbered |
| Lemma 7.26 | Lemma 8.30 | Word span products | Renumbered |
| Lemma 7.27 | Lemma 8.31 | Eigenvector padding | Renumbered |
| Thm 7.28 | Thm 8.32 | Assembly step | Renumbered |
| Lemma 7.29 | Lemma 8.33 | Blocking transfer | Renumbered |
| Remark 7.30 | Remark 8.34 | Relation with Lemma 2(b) | **Refs updated** |
| Thm 7.31 | Thm 8.35 | Blocking preserves normality | **Proof rewritten** |
| Lemma 7.32 | Lemma 8.36 | Chunking | Renumbered |
| Thm 7.33 | Thm 8.37 | Word eigenvector → blocked | Renumbered |
| Thm 7.34 | Thm 8.38 | Wielandt blocked assembly | Renumbered |
| Thm 7.35 | Thm 8.39 | Rank-one extraction | **Proof rewritten** |
| Thm 7.36 | Thm 8.40 | Fixed-length saturation | Renumbered |
| Remark 7.37 | Remark 8.41 | Blocking route | Renumbered |
| Def 7.38 | Def 8.42 | Primitive MPS tensor | **Clarification added** |
| Thm 7.39 | Thm 8.43 | Primitive overlap convergence | Renumbered; ref updated (6.21→7.21) |
| Thm 7.40 | Thm 8.44 | Nonzero word products | Renumbered |
| Thm 7.41 | Thm 8.45 | Iterated transfer nonvanishing | Renumbered |
| Thm 7.42 | Thm 8.46 | Fixed-point uniqueness | Renumbered |
| Thm 7.43 | Thm 8.47 | Complement powers → 0 | Renumbered |
| Remark 7.44 | Remark 8.48 | PSD vs PD | **Expanded with Prop 3 ref** |
| Thm 7.45 | Thm 8.49 | Primitive + PD ⟹ irreducible | Renumbered |
| — | Thm 8.50 | Primitive + PD ⟹ irreducible transfer | **New** |
| — | Thm 8.51 | Primitive + PD ⟹ strongly irreducible | **New** |
| — | Thm 8.52 | Primitive + PD ⟹ normal (no aperiodicity) | **New** |
| Remark 7.46 | Remark 8.53 | Aperiodicity condition | Renumbered |
| Remark 7.47 | Remark 8.54 | Counterexample | Renumbered |
| Thm 7.48 | Thm 8.55 | Word span monotonicity | Renumbered |
| Thm 7.49 | Thm 8.56 | T_n = S_n under aperiodicity | Renumbered |
| Thm 7.50 | Thm 8.57 | T_N = M_D + aperiodicity ⟹ normal | Renumbered |
| Thm 7.51 | Thm 8.58 | algSpan + aperiodicity ⟹ normal | Renumbered |
| Thm 7.52 | Thm 8.59 | Irreducible + aperiodicity ⟹ normal | **Refs updated; note added** |
| Thm 7.53 | Thm 8.60 | Prim + PD + aperiodicity ⟹ normal | Renumbered |
| Remark 7.54 | Remark 8.61 | Normal-canonical route | Renumbered; chapter refs updated |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Improved. Sharp D²−d'+1 bounds now proved (matching [SPGWC10, Lemma 1]). |
| Internal consistency | Good. All internal references updated. |
| v2 → v3 changes | Substantial: 7 new statements, 4 proofs rewritten/expanded, citation fixes. |
| AI language | "Assembly" in §8.6 title persists. Otherwise clean. |
| Formalization readiness | Improved. Key proof gaps from v2 addressed. One new issue (Thm 8.16 proof). |
| Open items from prior review | Mostly addressed. See §Prior Review Items below. |
| FT critical path | **Yes.** Thm 8.40 (fixed-length saturation) and Thm 8.52 (primitivity→normality) are load-bearing. |

---

# v2 → v3 Changes — Substantive

## 1. Sharp Wielandt bounds (NEW: Thms 8.14–8.16, 8.28)

v2 proved only the D² bound throughout. v3 now proves the paper's sharp
D²−d'+1 bound from [SPGWC10, Lemma 1]:

- **Theorem 8.14** (sharp cumulative span bound): T_{D²−d'+1}(A) = M_D(ℂ),
  where d' = krausRank(A). Proof is the standard dimension-growth argument
  starting from dim T_1 = d' instead of dim T_0 = 1.

- **Theorem 8.15** (sharp nonzero trace product): ∃w with |w| ≤ D²−d'+1
  and tr(A^w) ≠ 0.

- **Theorem 8.16** (sharp trace product at positive length): For D ≥ 2,
  ∃w with 1 ≤ |w| ≤ D²−d'+1 and tr(A^w) ≠ 0. Uses a "positive-level
  cumulative span" V_n excluding length-0 words.

- **Theorem 8.28** (Wielandt's inequality — general bound):
  ι(A) ≤ (D²−d'+1)·D², matching [SPGWC10, Theorem 1, case (1)].

**Assessment:** The statements are correct and faithfully reproduce the
paper's bounds. However, **Theorem 8.16's proof has a textual error**
(see item 8-N1 below).

## 2. Theorem 8.13: D ≥ 1 caveat added

v2's Theorem 7.13 used tr(𝟙) = D ≠ 0 without noting D ≥ 1.
v3 adds: "For the trace argument below, the nontrivial case is D ≥ 1;
when D = 0 the normality hypothesis is vacuous." This addresses the
cleanup item from the v2 review.

## 3. Theorem 8.17 (eigenvector extraction): proof expanded

v2's proof said "the Fitting decomposition ensures the corresponding
generalized eigenspace is nontrivial, yielding an eigenvector." The v2
review flagged the gap between generalized eigenvector and genuine
eigenvector.

v3 now explicitly states: "On that generalized eigenspace, M − μ𝟙 is
nilpotent, so its kernel is nontrivial. Any nonzero vector in ker(M − μ𝟙)
is therefore a genuine eigenvector with eigenvalue μ."

This directly addresses cleanup item 3 from the v2 review.

## 4. Theorem 8.35 (blocking preserves normality): proof corrected

v2's proof said "padding by repeated single-letter words," which the v2
review identified as misleading. The v2 review proposed the correct
argument: S_N = M_D ⟹ 𝟙 ∈ S_N ⟹ S_N ⊆ S_{kN} by iterated
multiplication.

v3 now uses **exactly this corrected argument**: "𝟙 ∈ S_N(A). For any
M ∈ S_N(A), write 𝟙 = Σ c_r A^{w_r}. Then M = M·𝟙 ∈ S_N·S_N ⊆ S_{2N}.
Iterating gives S_N ⊆ S_{kN}."

This directly addresses cleanup item 5 from the v2 review.

## 5. Theorem 8.39 (rank-one extraction): proof rewritten

v2's Theorem 7.35 claimed φψ^T ∈ S_{2D}(B) via P(vu^T)Q, but the v2
review showed the m = 2D bound was unjustified (the middle factor vu^T is
not in any word span).

v3 adopts **Fix 1** from the v2 review: the proof now says "Since A is
normal and N_0 ≥ 1, the blocked tensor B is normal by Theorem 8.35.
Therefore there exists M with S_M(B) = M_D(ℂ). In particular
φψ^T ∈ S_M(B). Taking m = M proves (3)."

The existential is correct by normality. The specific bound m = 2D is
dropped entirely. This is the minimal fix (Fix 1) rather than the
recommended Fix 2 (rectangular span argument), but it is mathematically
valid. The final Wielandt bound in Theorem 8.40 depends on m but makes
no claim about its value.

**Assessment:** This resolves the most important issue from the v2 review.
The theorem statement and proof are now correct. The proof is less sharp
than the paper's (no explicit bound on m), but the qualitative conclusion
is all that's needed for the FT proof chain.

## 6. New §8.10.3: Primitivity bridge without aperiodicity (Thms 8.50–8.52)

This is the most significant new content in the chapter:

- **Theorem 8.50:** Primitive + PD fixed point ⟹ irreducible transfer map.
  Uses fixed-point uniqueness (Thm 8.46) + Wolf's criterion.

- **Theorem 8.51:** Primitive + PD ⟹ strongly irreducible (irreducible +
  PD fixed point + peripheral spectrum = {1}).

- **Theorem 8.52:** Primitive + PD ⟹ normal. Uses (c)⇒(b) of [SPGWC10,
  Proposition 3].

**Assessment:** This is a clean and correct argument chain. It fills the
gap flagged in the v2 review (Remark 7.44 / 8.48): the aperiodicity-based
route (§8.11) requires the additional hypothesis 𝟙 ∈ S_1(A), but the new
§8.10.3 bypasses this entirely for the case ρ > 0.

However, **Theorem 8.52's proof invokes (c)⇒(b) of [SPGWC10,
Proposition 3] as an external fact.** This direction of Proposition 3
asserts that strong irreducibility implies eventually full Kraus rank. The
proof in the paper uses ergodic-theoretic arguments (the quantum Wielandt
inequality itself, plus convergence of E^n to the fixed-point projection,
applied to show all matrix units lie in some S_N). For formalization, this
external invocation needs to be either:
(a) proved as a separate theorem in the blueprint, or
(b) replaced by the internal chain via the Burnside bridge and
aperiodicity results.

The current proof does not spell out (c)⇒(b). The parenthetical says
"strong irreducibility implies ⟨A⟩_n = M_D for large n, which is exactly
normality" — but this conflates algSpan (the algebra generated by all
words) with S_n (word span at a single length). Strong irreducibility
gives algSpan = M_D via Burnside, but getting S_n = M_D for a specific n
additionally requires aperiodicity (which strong irreducibility does
provide, since peripheral spectrum = {1} implies 𝟙 ∈ S_1).

**This needs clarification for Lean**: the proof should make the
intermediate step explicit — strong irreducibility ⟹ irreducible + {1}
peripheral ⟹ irreducible + aperiodic ⟹ Burnside + Thm 8.58 ⟹ normal.
Alternatively, note that the aperiodicity follows from {1} being the only
peripheral eigenvalue.

## 7. Definition 8.42: clarification added

v2's Definition 7.38 just said "primitive MPS tensor" with PSD fixed point.
v3 adds: "This is weaker than the paper's notion, which requires ρ > 0;
see Remark 8.48. The stronger positive-definite hypothesis is imposed
separately in Theorems 8.49 and 8.60."

This addresses cleanup item 8 from the v2 review.

## 8. Theorem 8.26 / Remark 8.27: citation sharpened

v2's Theorem 7.23 said "This is [SPGWC10, Theorem 1]." v3 now says "This
is the cumulative-span part of [SPGWC10, Theorem 1]. The paper's theorem
is stronger: via Lemma 2(b) it upgrades this to a fixed-length conclusion
S_N(A) = M_D(ℂ), proved below in Theorem 8.40."

Remark 8.27 now references the sharp bound and Theorem 8.28.

This addresses cleanup item 4 from the v2 review.

## 9. Definition 8.1: citation fixed

v2 said "[SPGWC10, Eq. (1)]." v3 says "[SPGWC10, §II]."

This addresses cleanup item 1 from the v2 review.

## 10. Remark 8.48 / Theorem 8.59: expanded

Remark 8.48 now includes the explicit sentence linking back to
[SPGWC10, Proposition 3]. Theorem 8.59 adds: "For the Burnside step,
we appeal forward to Theorems 9.20 and 9.21 in Chapter 9; this is a
presentation-level forward dependency, but the mathematical dependency
is acyclic." This directly addresses the forward-dependency concern from
cleanup item 7 of the v2 review (the circular dependency is acknowledged
even if not structurally resolved).

---

# v2 → v3 Changes — Non-substantive

Retained content (all sections) is verbatim identical to v2 modulo:
1. Theorem/definition numbers incremented by 1 (7.x → 8.x) for
   statements that did not shift due to new insertions.
2. External cross-references updated to v3 numbering.
3. Page numbers.

---

# New Issue

## 8-N1. Theorem 8.16 proof: garbled claim about 𝟙 ∉ V

**Severity: Must fix (textual error in proof).**

The proof of Theorem 8.16 defines V_n = span{A^w : 1 ≤ |w| ≤ n} and
correctly shows V_{D²−d'+1} = M_D(ℂ). The intended conclusion is:

> Since V_{D²−d'+1} = M_D(ℂ), the identity 𝟙 lies in V_{D²−d'+1},
> i.e., 𝟙 is a linear combination of positive-length word products.
> Since tr(𝟙) = D ≠ 0, at least one of those words has nonzero trace.

But the actual text says:

> "Since V_{D²−d'+1} = M_D(ℂ) and D ≥ 2 implies
> 𝟙 ∉ V_{D²−d'+1} (dimension of M_D(ℂ) is D² ≥ 4, but span{𝟙} has
> dimension 1), at least one generator has nonzero trace."

This is **wrong as written**: the claim 𝟙 ∉ V_{D²−d'+1} contradicts
V_{D²−d'+1} = M_D(ℂ) (which contains 𝟙). The parenthetical about
dimensions is a non sequitur. The conclusion is nevertheless correct —
the argument should say 𝟙 ∈ V_{D²−d'+1}, and since V_n only contains
positive-length word products, 𝟙 must be a linear combination of such
products, at least one of which has nonzero trace.

**Recommended fix:** Replace the sentence with: "Since
V_{D²−d'+1} = M_D(ℂ), the identity 𝟙 lies in V_{D²−d'+1} and is
therefore a linear combination of word products of positive length.
At least one such product has nonzero trace (since tr(𝟙) = D ≥ 2 ≠ 0)."

## 8-N2. Theorem 8.28 proof: unjustified claim S_{D²}(B) = M_D(ℂ)

**Severity: Must fix (unjustified bound in proof).**

The proof of Theorem 8.28 claims "S_{D²}(B) = M_D(ℂ)" in both the
invertible and non-invertible cases. However, the blueprint's own
theorems do not support this claim:

- Theorem 8.12 gives T_{D²}(B) = M_D(ℂ) (cumulative, not fixed-length).
- Theorem 8.40 gives ∃N: S_N(B) = M_D(ℂ) (existential, no explicit
  bound on N).
- Theorem 8.39 (rank-one extraction) uses the existential via normality
  (Fix 1), so it provides no bound on the rank-one index m.

The paper [SPGWC10, Theorem 1] establishes the D² bound by tracking
indices through the full Lemma 2(a+b) argument. Specifically:
- Case 2 (invertible): q ≤ D²−k+1 ≤ D². This works because an
  invertible Kraus operator allows the dimension-growth argument to give
  S_{D²−k+1}(B) = M_D directly.
- Case 1 (non-invertible): The paper applies Lemma 2(b) to the blocked
  tensor and gets |φ⟩⟨ψ| ∈ S_{(D²−D+1)n} and |χ⟩⟨ψ| ∈ S_{nD²}.

The blueprint's Theorem 8.39 (which uses Fix 1) dropped the explicit
index tracking, so the S_{D²}(B) claim in Theorem 8.28's proof is no
longer supported by the available lemmas. In the non-invertible case,
the blueprint can only conclude S_N(B) = M_D for some uncontrolled N,
which would give ι(A) ≤ N·n rather than D²·n.

**Impact:** If N > D², the final bound ι(A) ≤ (D²−d'+1)·D² would be
unjustified. The theorem statement may still be correct (the paper proves
it), but the blueprint's proof as written does not establish it.

**Recommended fix:** Either:
(a) Restore explicit index tracking in Theorem 8.39 by adopting Fix 2
    (the paper's rectangular span argument), which gives explicit bounds.
(b) Weaken Theorem 8.28 to state ι(A) < ∞ (a finite bound exists)
    without the specific (D²−d'+1)·D² value, deferring the sharp bound.
(c) In the invertible case (a), use the fact that an invertible B^{j0}
    gives S_{D²−k_B+1}(B) = M_D directly (case 2 of the paper); in the
    non-invertible case (b), invoke the paper's bound as an external fact.

Note: This issue is a *consequence* of adopting Fix 1 (existential) for
Theorem 8.39 instead of Fix 2 (rectangular span with tracking). Fix 1
suffices for the qualitative Theorem 8.40 (∃N: S_N = M_D) but not for
the quantitative Theorem 8.28.

---

# Prior Review Items — Status Check

## From `blueprint_chapter7_review.md` (v2 review)

| # | v2 Issue | v3 Status |
|---|---|---|
| 1 | Def 7.1 citation "[SPGWC10, Eq. (1)]" wrong | ✓ **Fixed.** Now "[SPGWC10, §II]." |
| 2 | Thm 7.13: D ≥ 1 hypothesis missing | ✓ **Fixed.** Caveat added. |
| 3 | Thm 7.14 proof: generalized vs genuine eigenvector | ✓ **Fixed.** Proof expanded in Thm 8.17. |
| 4 | Thm 7.23 citation conflates cumulative vs fixed-length | ✓ **Fixed.** Clarified in Thm 8.26 + Remark 8.27. |
| 5 | Thm 7.31 proof: "padding by single-letter words" misleading | ✓ **Fixed.** Proof rewritten in Thm 8.35. |
| 6 | **Thm 7.35 proof: m = 2D bound unjustified** | ✓ **Fixed (minimal).** Proof in Thm 8.39 now uses existential via normality. |
| 7 | Thm 7.52: forward dependency on Ch 8 Burnside | **Partially addressed.** Forward dependency acknowledged in Thm 8.59 text. Not structurally resolved (Burnside still in Ch 9). |
| 8 | Def 7.38: consider requiring ρ > 0 | ✓ **Addressed.** Def 8.42 clarifies PSD vs PD; Thm 8.52 imposes PD separately. |
| 9 | Add equivalence remark for "normal" (X-1) | **Partially addressed.** Remark 8.48 references [SPGWC10, Proposition 3]. Full equivalence remark not yet added near Def 2.19. |

## From `blueprint_review_comprehensive_reference.md`

**Part II (AI language):** "Assembly" persists as §8.6 section title.
This was already flagged; unchanged.

**Part III (Notation):** No new notation issues in this chapter.

**Part IV (Formalization notes):**
- 7-F1 (word span as subspace vs algebra): Still relevant. S_n and T_n
  are subspaces; the algebra generation is Burnside (now Ch 9).
- 7-F2 (blocking type change): Still relevant. Blocking changes physical
  dimension from Fin d to Fin (d^L).

**Part V (Orphans):** No Chapter 8 statements flagged as orphaned.

---

# Statement-by-Statement Analysis — New Statements

(Retained statements are analyzed in the v2 review with updated numbers;
only new or significantly changed statements are reviewed here.)

## Theorem 8.14 (Sharp cumulative span bound)

Statement: T_{D²−d'+1}(A) = M_D(ℂ) where d' = dim S_1(A) = krausRank(A).

**Correct.** This is exactly [SPGWC10, Lemma 1]. The proof starts from
dim T_1 = d' (not dim T_0 = 1) and counts at most D²−d' strict growth
steps.

Note: The proof says "Starting from T_1(A) = S_1(A) with dimension d'."
Strictly, T_1 = S_0 + S_1 = span{𝟙} + S_1, so dim T_1 could be d'+1 if
𝟙 ∉ S_1. The paper's R_1 has dimension d (= dim S_1), not including 𝟙.
However, the bound still holds: dim T_1 ≥ d' means at most D²−d' strict
growth steps from T_1 to T_{D²−d'+1}, so T_{D²−d'+1} = M_D. The claim
"T_1(A) = S_1(A)" should be corrected to "dim T_1(A) ≥ d'" (see 8-S3).

## Theorem 8.15 (Sharp nonzero trace product)

**Correct.** Immediate from 8.14.

## Theorem 8.16 (Positive-length sharp trace product)

Statement: Correct and needed for Theorem 8.28 (blocking requires
positive-length words). The proof idea (positive-level cumulative span)
is sound.

**Proof has textual error** (item 8-N1 above).

## Theorem 8.28 (Wielandt's inequality — general bound)

Statement: ι(A) ≤ (D²−d'+1)·D². Matches [SPGWC10, Theorem 1, case (1)].

**Proof has an unjustified claim** (item 8-N2). The claim S_{D²}(B) = M_D
in both cases is not supported by the blueprint's Theorem 8.39, which
uses the existential (no explicit bound on m). In the invertible case,
the bound can be recovered from the paper's case 2 argument (invertible
Kraus operator ⟹ direct dimension growth). In the non-invertible case,
the blueprint lacks the index tracking that the paper's Lemma 2(b) proof
provides.

— *Must fix (see 8-N2).*

## Theorem 8.50 (Primitive + PD ⟹ irreducible transfer)

**Correct.** Immediate from fixed-point uniqueness + Wolf's criterion.

## Theorem 8.51 (Primitive + PD ⟹ strongly irreducible)

**Correct.** Combines 8.50 with the spectral-gap condition.

Note: The proof says "peripheral-spectrum primitivity from the spectral-gap
hypothesis (Theorem 8.43)." This is slightly imprecise: Theorem 8.43 gives
O_{AA}(N) → 1, not directly the peripheral spectrum condition. The
peripheral spectrum = {1} follows from the spectral gap ρ(ℰ_A − P) < 1
plus Thm 8.46 (unique fixed point), which together imply no peripheral
eigenvalues other than 1. The argument is correct but the intermediate
step could be named.

## Theorem 8.52 (Primitive + PD ⟹ normal, without aperiodicity)

**Statement correct.** This is the key new result in the chapter.

**Proof invokes external result** — see assessment in §v2→v3 Changes
item 6 above. The (c)⇒(b) direction of [SPGWC10, Proposition 3] is not
proved in the blueprint. For formalization, this needs either an explicit
proof or a note that the external direction is accepted as an axiom.

The internal route would be: strong irreducibility ⟹ peripheral
spectrum = {1} ⟹ 𝟙 ∈ S_1(A) (aperiodicity follows from channel
properties when spectrum is {1}; this needs a separate argument) ⟹
irreducible + aperiodic ⟹ normal by Thm 8.59. But this route requires
the aperiodicity inference, which is currently not stated as a theorem.

— *Moderate (external dependency needs explicit handling for Lean).*

---

# Cross-Chapter Consistency

**Forward references verified:**

| v3 reference | Target | Verified |
|---|---|---|
| Theorem 7.21 | Self-overlap convergence (Ch 7) | ✓ (p. 38) |
| Definition 2.19 | Normal tensor (Ch 2) | ✓ (p. 8) |
| Theorem 9.20 | Irreducible tensor ⟹ irreducible action (Ch 9) | ✓ (p. 53) |
| Theorem 9.21 | Burnside for Kraus algebras (Ch 9) | ✓ (p. 53) |
| Lemma 6.3 | Wolf [Wol12, Lemma 6.3(b)] — literature citation | N/A |

**Downstream citations of Chapter 8:** Theorem 8.52 is cited in
Chapter 9 (p. 59, Theorem 9.48: TP-primitive irreducible tensor is
normal). This is the key forward use of the new primitivity bridge.

**DS gauge:** Fully eliminated. Definition 8.42 uses TP normalization
throughout.

**Burnside forward dependency:** Still present (Thm 8.59 cites
Thms 9.20–9.21). Now explicitly acknowledged in the text as a
"presentation-level forward dependency." The mathematical dependency
remains acyclic.

---

# Literature Alignment

## Changes improving alignment with [SPGWC10]

1. Sharp D²−d'+1 bounds (Thms 8.14–8.16) now match Lemma 1 exactly.
2. General Wielandt bound (Thm 8.28) matches Theorem 1, case (1).
3. Citation for Def 8.1 corrected to §II.
4. Citation for Thm 8.26 clarified (cumulative vs fixed-length).
5. Primitivity bridge (§8.10.3) aligns with Proposition 3.

## Remaining deviations (carried from v2)

1. **Fitting decomposition instead of Jordan normal form:** Unchanged.
   Pragmatic Lean choice; provides same structural information.
2. **Weaker quantitative bounds in some places:** The D² bound (Thm 8.26)
   is kept alongside the sharp bound (Thm 8.14); both are now present.
3. **Lemma 2(b) proof via blocking + normality:** The paper's rectangular
   span argument is not used. The proof instead uses the existential via
   normality of the blocked tensor. This is mathematically valid but gives
   no explicit bound on m.

---

# AI-Language Audit

**§8.6 title "Assembly":** Still present. Should be "Proof of the
Wielandt bound" or "Wielandt bound — cumulative span."

No other AI-language issues detected in the new content. The new
theorems and proofs read as standard mathematical writing.

---

# Formalization Notes

**8-F1. Word span as subspace vs algebra (from 7-F1).**
Still relevant. S_n and T_n are subspaces in Lean. The algebra generation
(algSpan) is a separate object used in Thms 8.58–8.59 via Burnside.

**8-F2. Blocking type change (from 7-F2).**
Still relevant. A^{[L]} has physical dimension d^L. Lean type changes from
`Fin d → ...` to `Fin (d^L) → ...`.

**8-F3. Theorem 8.28: case split formalization.**
The invertible/non-invertible case split needs two separate Lean proof
branches. The invertible case is simpler (no Lemma 2(b) needed); the
non-invertible case uses the full Wielandt chain.

**8-F4. Theorem 8.52: external dependency.**
(c)⇒(b) of [SPGWC10, Proposition 3] is invoked but not proved. For Lean,
this needs to be either proved or axiomatized. See discussion under
Theorem 8.52 above.

---

# Cleanup Checklist

## Must fix

**8-N1.** Theorem 8.16 proof: replace the garbled "𝟙 ∉ V_{D²−d'+1}"
with the correct statement "𝟙 ∈ V_{D²−d'+1}" and the correct reasoning
(𝟙 is a linear combination of positive-length words, at least one of
which has nonzero trace since tr(𝟙) = D ≥ 2 ≠ 0).

**8-N2.** Theorem 8.28 proof: the claim S_{D²}(B) = M_D(ℂ) in both
cases (a) and (b) is unjustified given that Theorem 8.39 uses the
existential (no explicit bound on the rank-one index m). Either restore
explicit index tracking (Fix 2 for Theorem 8.39) or weaken the bound,
or handle the two cases asymmetrically (case (a) follows from the
invertibility argument; case (b) needs the paper's Lemma 2(b) tracking).

## Should fix

**8-S2.** Theorem 8.52 proof: clarify that (c)⇒(b) of [SPGWC10,
Proposition 3] is used as an external fact, or provide the internal proof
chain: strongly irreducible ⟹ {1} peripheral spectrum ⟹ aperiodic
(since channel with only peripheral eigenvalue 1 has 𝟙 ∈ S_1) ⟹
irreducible + aperiodic ⟹ normal by Thm 8.59.

**8-S3.** Theorem 8.14 proof: clarify that T_1 = S_0 + S_1 has dimension
at least d' (not exactly d'), so the growth bound is ≤ D²−d' steps.

**8-S4.** §8.6 title: rename "Assembly" to "Wielandt bound — cumulative
span" or "Proof of the cumulative Wielandt bound."

## Low priority

**8-L1.** Theorem 8.51 proof: make explicit that "peripheral-spectrum
primitivity from Theorem 8.43" means peripheral spectrum = {1} follows
from the spectral gap ρ(ℰ_A − P) < 1.

## Acceptable as-is

- Theorem 8.39 proof uses existential (Fix 1) rather than rectangular span
  (Fix 2). The existential is valid and sufficient for the FT chain.
- Definition 8.42 keeps PSD (weaker than paper's PD). The distinction is
  properly documented in Remark 8.48 and Theorems 8.49/8.60.
- Burnside forward dependency (Thm 8.59 → Thms 9.20–9.21). Acknowledged
  in text; mathematically acyclic.

---

# Final Assessment

v3 Chapter 8 addresses the majority of the issues raised in the v2
review. The most important fix is the rank-one extraction proof (Theorem
8.39), which no longer claims the unjustified m = 2D bound. The new sharp
bounds (Thms 8.14–8.16, 8.28) and the primitivity bridge without
aperiodicity (§8.10.3) are significant additions that bring the chapter
closer to [SPGWC10].

The main new issues are: (1) the textual error in Theorem 8.16's proof
(item 8-N1), which is a straightforward fix; and (2) the unjustified
S_{D²}(B) = M_D claim in Theorem 8.28's proof (item 8-N2), which is a
consequence of adopting the existential (Fix 1) in Theorem 8.39 without
restoring the index tracking needed for the quantitative bound. This
latter issue requires either restoring the paper's rectangular span
argument or weakening the theorem.

**Priority for the formalization agent:**
1. Fix Theorem 8.16 proof text (8-N1).
2. Resolve Theorem 8.28 proof gap (8-N2) — this is the most important
   open issue in the chapter.
3. Clarify the (c)⇒(b) dependency in Theorem 8.52 (8-S2).
4. Correct "T_1 = S_1" to "dim T_1 ≥ d'" in Theorem 8.14 proof (8-S3).
