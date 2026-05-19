# CPSV16 paper BNT multiplicity audit

## Executive summary

The proposed `IsBNTCanonicalForm` is a real improvement over the one-copy surface, and it correctly admits the motivating `C ⊕ (-C)` and `C ⊕ e^{iθ}C` examples.  However, it is still too restrictive to be the full CPSV16/CPSV21 BNT surface.  Two independent restrictions are not in the papers: strict modulus decrease between distinct BNT basis elements, and equal modulus for all copies over a fixed BNT basis element.  CPSV16 allows distinct normal basis tensors with equal coefficient modulus, and it also allows gauge-phase-equivalent copies over one basis tensor whose coefficients have different moduli.  The safe correction is to make the primary BNT predicate store the BNT basis and the raw `SectorWeightData` weights, with normality, eventual LI, and cast-compatible basis distinctness; any equal-modulus `spectralLevel`/`phaseWeight` layer should be optional, not part of the core predicate.

## Source anchors

* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:217-246`: canonical form uses arbitrary complex weights `μ_k`; the only global normalization stated there is `|μ_k| ≤ 1` and at least one weight of modulus one.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:271-301`: BNT is a minimal basis of normal tensors; the two-layer display has `μ_{j,q}` in `M_j` and the MPV coefficient `∑_q μ_{j,q}^N`.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:1121-1132`: the LI corollary is the Gram-matrix input used for BNT vectors.
* CPSV16 `Papers/1606.00608/MPDO-22-12-17-2.tex:1181-1188`: the theorem proof applies LI to rule out the all-decay alternative, and the equal-MPV corollary recovers per-sector multiplicities from `∑_q μ_{j,q}^N = ∑_q (ν_{j,q} e^{iφ_j})^N`.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1815-1837`: normal tensors are primitive after blocking; canonical form is `⊕_k μ_k A_k`.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1846-1884`: BNT and the two-layer BNT decomposition use raw entries `μ_{j,q}` and coefficient `∑_q μ_{j,q}^N`.
* CPSV21 `Papers/2011.12127/TN-Review-main.tex:1905-1908`: the unital gauge is optional, and the non-periodic theorem is separated from the periodic generalization.
* `TNLean/MPS/SharedInfra/SectorDecomposition.lean:29-43`: `SectorWeightData` already stores multiplicities and raw nonzero weights.
* `TNLean/MPS/SharedInfra/SectorDecomposition.lean:137-199`: `P.toTensor` already expands as `∑_j ∑_q (P.weight j q)^N V_N(P.basis j)` and then as `∑_j P.coeff N j V_N(P.basis j)`.
* `TNLean/MPS/BNT/Construction.lean:68-74`: `BlocksNotGaugePhaseEquiv` has the cast-compatible shape needed when basis dimensions differ.
* `TNLean/MPS/BNT/Construction.lean:446-467`: cross-overlap decay splits into same-dimension `GaugePhaseEquiv` and different-dimension cases.
* `TNLean/MPS/BNT/Basic.lean:172-178` and `:195-213`: coefficient extraction and combined-family LI are already surface-agnostic engines.
* `TNLean/MPS/FundamentalTheorem/SectorWeightComparison.lean:112-117`: `geom_sum_eventually_zero` is the right algebraic tool for proving power sums of nonzero weights are not eventually zero.

## Q1. Repeated `phaseWeight j q` within a sector

**Verdict:** correct to allow repeats; adding within-sector phase distinctness would be a design flaw.

**Reference / counter-check:** CPSV16 line 292 says `M_j` is diagonal with entries `μ_{j,q}` and line 301 uses the sum `∑_q μ_{j,q}^N`; no distinctness of diagonal entries is stated.  CPSV16 lines 1184-1188 recover multiplicities from equality of power sums, which only makes sense as a multiset statement with repeated entries allowed.

**Recommendation:** do not add a `Nodup` or pairwise-distinct field for `phaseWeight j`.  `C ⊕ C` with weights `(1, 1)` is a legitimate multiplicity-two sector and has coefficient `2`, not a single scalar power `μ^N`.  It is redundant only if the theorem works modulo arbitrary length-independent scalar factors, and the equal-MPV corollary does not.

## Q2. Coincident phase weights across different sectors

**Verdict:** cross-sector equality of the unit factors is harmless; the problem is the proposed strict modulus condition, not phase coincidence.

**Reference / counter-check:** CPSV16/CPSV21 do not define a cross-sector phase list at all; they store raw `μ_{j,q}`.  If one chooses an auxiliary factorization `μ_{j,q}=λ_jω_{j,q}`, then `ω` is not canonical because one can multiply `λ_j` by a unit scalar and divide all `ω_{j,q}` by it.

**Recommendation:** add no cross-sector distinctness condition on `phaseWeight`.  More importantly, do not infer BNT grouping from equality or inequality of these unit factors.  BNT grouping is controlled by gauge-phase equivalence of basis tensors, not by equality of auxiliary phases.

## Q3. One sector with two copies versus two sectors with one copy each

**Verdict:** the intended distinction is mostly captured by `basis_distinct`, but the `X_{j,q}` data is absent and should be treated deliberately.

**Reference / counter-check:** CPSV16 lines 264-279 say gauge-phase-equivalent normal tensors are represented by one BNT element; lines 287-301 show the suppressed copies as `μ_{j,q} X_{j,q} A_j^i X_{j,q}^{-1}`.  Since the finite MPV is invariant under conjugation by `X_{j,q}` and the scalar phase contributes a power, the MPV-level `SectorDecomposition` can absorb the copy into the scalar weight.

**Recommendation:** for MPV comparison and CPSV16 §II Step 1, no `X_{j,q}` field is needed.  For a later tensor-level global conjugacy statement, add separate realization data recording the actual copy gauges, or state the theorem only for `P.toTensor`, which uses repeated representatives without the conjugating matrices.  Keep the cast-compatible `basis_distinct` shape from `BlocksNotGaugePhaseEquiv`.

## Q4. Consistency of `weight_factor` with CPSV notation

**Verdict:** counter-example exists.  The factorization is valid only for an equal-modulus subcase; it is not the full CPSV16 BNT coefficient.

**Reference / counter-example:** CPSV16 lines 287-301 and CPSV21 lines 1864-1884 use raw entries `μ_{j,q}`.  They do not require `|μ_{j,q}|` to be constant in `q`.  Let `C` be one normal tensor and consider `C ⊕ (1/2) C`.  The BNT basis has one element `C` and coefficient `1^N + (1/2)^N`.  The proposed structure cannot encode this as one sector because there is no common `λ` with both quotients unit modulus.  It also cannot encode it as two sectors if `basis_distinct` is enforced, because the two basis tensors are gauge-phase equivalent.

**Recommendation:** remove `spectralLevel`, `phaseWeight`, `phaseWeight_norm_one`, and `weight_factor` from the primary paper BNT predicate.  If equal-modulus sectors are useful for a later estimate, introduce a separate optional predicate, for example `HasEqualModulusWeightLayer P`, and never present it as the core CPSV BNT hypothesis.

## Q5. Dominant normalization `‖spectralLevel 0‖ = 1`

**Verdict:** acceptable as an optional normalized subcase; too rigid as a core paper BNT field.

**Reference / counter-check:** CPSV16 line 246 permits a global normalization `|μ_k| ≤ 1` with at least one coefficient of modulus one.  It does not single out one BNT basis element by a strictly decreasing spectral level, and it does not require every BNT sector to have a common modulus.

**Recommendation:** if normalization is required, put it on raw weights: `∀ j q, ‖P.weight j q‖ ≤ 1` plus existence of some `(j,q)` with norm one, or leave it as a theorem-side hypothesis.  In paired proportional problems, separate normalization is harmless because the proportional scalar absorbs the global factor.  In exact equal-MPV statements, normalization changes equality into a length-dependent proportionality unless the two dominant radii have already been shown equal.

## Q6. Per-block normality fields

**Verdict:** missing constraints / naming risk.  The listed fields are useful for the current overlap lemmas, but they are not a CPSV single normality predicate.

**Reference / counter-check:** CPSV16 lines 233-234 define a normal tensor by irreducibility plus a unique peripheral eigenvalue after the chosen blocking convention.  CPSV21 lines 1815-1830 describe primitive transfer operators after blocking.  Existing Lean cross-overlap lemmas use irreducibility plus left-canonical normalization, while `IsBNT` elsewhere may need an `IsNormal` witness.

**Recommendation:** add `basis_dim_pos : ∀ j, 0 < P.basisDim j` and consider bundling the tensor hypotheses under a project predicate, e.g. `basis_normal : ∀ j, IsNormal (P.basis j)` or a primitive-transfer-map predicate, with projections to `basis_irreducible`, `basis_left_canonical`, and `basis_normalized_self_overlap`.  A right-canonical field is not needed for the cited LI and decay lemmas if self-overlap convergence is explicit.

## Q7. Completeness for CPSV16 §II Step 1

**Verdict:** missing algebraic API, and the equal-modulus layer is unnecessary for the source argument.

**Reference / counter-check:** `TNLean/MPS/BNT/Basic.lean:195-213` gives the combined-family LI once self-overlaps and all cross-overlaps have the right limits.  `TNLean/MPS/BNT/Basic.lean:172-178` then extracts coefficients from a relation.  To get a contradiction for a fixed sector, one must know the sector coefficient `P.coeff N j = ∑_q P.weight j q ^ N` is not eventually zero.

**Recommendation:** prove an API lemma for raw sector weights:

```lean
lemma not_eventually_coeff_eq_zero (P : SectorDecomposition d) (j : Fin P.basisCount) :
    ¬ (∀ᶠ N in Filter.atTop, P.coeff N j = 0)
```

using `P.copies_pos`, `P.weight_ne_zero`, and `geom_sum_eventually_zero`.  Also add `basis_dim_pos` so same/different dimension cross-overlap lemmas can be applied without typeclass friction.

## Q8. Interaction with the existing `_sameMPV₂_CFBNT` proof

**Verdict:** the old proof shape should not be trusted unchanged on multi-copy data.

**Reference / counter-check:** the old one-copy theorem isolates scalar powers.  Multi-copy coefficients can vanish infinitely often, e.g. `1 + (-1)^N`, and can mix different moduli inside one BNT basis element, e.g. `1 + (1/2)^N`.  CPSV16 lines 1184-1188 switch to power-sum comparison inside matched BNT sectors.

**Recommendation:** re-prove from the source route: sector-level nondecay by combined-family LI and exact coefficient comparison, then sector matching, then per-sector multiset recovery by Newton-Girard/power-sum lemmas.  Do not induct on flattened copies as if they were LI basis vectors; copies over the same BNT basis tensor are deliberately linearly dependent as MPV families.

## Q9. `C ⊕ (-C)` check

**Verdict:** correct; the proposed structure admits this example.

**Reference / counter-check:** with one basis sector, two copies, weights `(1, -1)`, choose `spectralLevel 0 = 1` and `phaseWeight = (1, -1)`.  The coefficient is `1 + (-1)^N`, exactly as in the recommendation note and CPSV16 line 301.  The companion Lean example in commit `b77532f1`, `SectorBNT/Examples.lean`, constructs this as `signFlipDecomp`.

**Recommendation:** keep this example.  It validates multiplicities with equal modulus, but it does not validate the stronger claim that all paper BNT multiplicities have equal modulus.

## Q10. Equal modulus across sectors

**Verdict:** counter-example exists if the basis tensors are distinct; the proposed strict order is too strong.

**Reference / counter-example:** take two normal tensors `C` and `D` that are not gauge-phase equivalent and set `A = C ⊕ D` with weights `(1,1)`.  This is a valid CPSV16 canonical/BNT decomposition: two BNT basis elements, each with one copy, and equal coefficient modulus.  The proposed structure requires `‖spectralLevel 0‖ > ‖spectralLevel 1‖` on `Fin 2`, but `weight_factor` and unit `phaseWeight` force both spectral norms to be `1`, a contradiction.

**Recommendation:** do not require `StrictAnti` for BNT basis elements.  If a sorted normalization is useful, use `Antitone` on raw weight moduli or no order field at all.  Equal-modulus copies of the same gauge-phase class must be grouped; equal-modulus weights on different BNT basis tensors must remain separate.

## Q11. Mixed multi-sector multi-copy case

**Verdict:** the displayed mixed case is represented only when the lower-modulus copy belongs to a genuinely different BNT basis tensor.  A same-basis lower-modulus copy is a counter-example to the equal-modulus factorization.

**Reference / counter-check:** if sector 0 has basis `C` and weights `(1,-1)`, while sector 1 has a non-gauge-equivalent basis `D` and weight `1/2`, the proposed fields can be filled with spectral norms `1` and `1/2`.  But `C ⊕ (-C) ⊕ (1/2)C` has one BNT basis element `C` with weights `(1,-1,1/2)` in CPSV16 line 301, and the proposed structure rejects it.

**Recommendation:** raw `P.weight` must be the primary coefficient data.  Equal-modulus grouping may be a derived subcase, not the definition of a BNT sector.

## Q12. Periodic versus non-periodic basis blocks

**Verdict:** the current self-overlap field intentionally selects the non-periodic, normalized setting; it does not cover the periodic generalization.

**Reference / counter-check:** CPSV21 lines 1815-1820 explain blocking to remove peripheral roots of unity and obtain primitive channels.  Lines 1905-1908 then note a periodic generalization.  The field `basis_normalized_self_overlap : Tendsto ... (nhds 1)` is compatible with the blocked primitive setting, but not with unblocked periodic oscillations.

**Recommendation:** either document the predicate as a non-periodic/after-blocking BNT surface, or generalize the field to store a nonzero limit:

```lean
basis_self_overlap_limit : ∀ j, ∃ ℓ : ℂ, ℓ ≠ 0 ∧
  Tendsto (fun N => mpvOverlap (P.basis j) (P.basis j) N) atTop (nhds ℓ)
```

The existing Gram-matrix LI theorem uses limit `1`, so the generalized version would need a diagonal-nonzero Gram limit lemma.

## Q13. Shape of `GaugePhaseEquiv` distinctness

**Verdict:** the simplified proposed field is not type-correct in heterogeneous dimensions; the cast-compatible shape is required.

**Reference / counter-check:** `BlocksNotGaugePhaseEquiv` in `TNLean/MPS/BNT/Construction.lean:68-74` quantifies over `h : dim j = dim k` and casts the left tensor.  The cross-overlap lemma at `:446-467` uses this shape and handles `dim j ≠ dim k` separately.

**Recommendation:** define

```lean
basis_distinct : ∀ j k : Fin P.basisCount, j ≠ k →
  ∀ h : P.basisDim j = P.basisDim k,
    ¬ GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis j)) (P.basis k)
```

or reuse a `BlocksNotGaugePhaseEquiv` abbreviation specialized to `P.basis`.  Also add `basis_dim_pos` for downstream lemmas that require `[∀ j, NeZero (P.basisDim j)]`.

## Counter-examples found

1. **Distinct BNT sectors with equal modulus:** `A = C ⊕ D`, where `C` and `D` are normal, not gauge-phase equivalent, and both weights are `1`.  CPSV allows this; the proposed `StrictAnti` rejects it.
2. **One BNT sector with unequal-modulus copies:** `A = C ⊕ (1/2)C`.  CPSV allows one BNT basis element with coefficient `1 + (1/2)^N`; the proposed `phaseWeight_norm_one + weight_factor` rejects it.
3. **One BNT sector with both oscillation and decay:** `A = C ⊕ (-C) ⊕ (1/2)C`.  CPSV allows coefficient `1 + (-1)^N + (1/2)^N`; the proposed structure can represent the first two copies but not the third without illegally splitting a gauge-phase-equivalent basis tensor into another BNT sector.
4. **Repeated equal phase is not a counter-example:** `A = C ⊕ C` should be admitted as multiplicity two.  It has coefficient `2`, and multiplicity is recovered as a multiset count.

## Recommended field-level amendments

Use `SectorWeightData` as the coefficient layer and make BNT minimality about basis tensors, not weight moduli.

```lean
structure IsBNTCanonicalForm (P : SectorDecomposition d) where
  basis_dim_pos : ∀ j : Fin P.basisCount, 0 < P.basisDim j
  basis_injective : ∀ j, IsInjective (P.basis j)
  basis_irreducible : ∀ j, IsIrreducibleTensor (P.basis j)
  basis_left_canonical : ∀ j, IsLeftCanonical (P.basis j)
  basis_normalized_self_overlap : ∀ j,
    Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      atTop (nhds (1 : ℂ))
  bnt_data : HasBNTSectorData P
  basis_distinct : ∀ j k : Fin P.basisCount, j ≠ k →
    ∀ h : P.basisDim j = P.basisDim k,
      ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j)) (P.basis k)
```

Then add API lemmas, not fields:

```lean
lemma coeff_not_eventually_zero
    (h : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    ¬ (∀ᶠ N in Filter.atTop, P.coeff N j = 0)
```

and, if needed for estimates, a separate optional predicate:

```lean
structure HasEqualModulusWeightLayer (P : SectorDecomposition d) where
  spectral_level : Fin P.basisCount → ℂ
  spectral_level_ne_zero : ∀ j, spectral_level j ≠ 0
  spectral_level_antitone : Antitone (fun j => ‖spectral_level j‖)
  spectral_level_dom_norm_one : ∀ h : 0 < P.basisCount,
    ‖spectral_level ⟨0, h⟩‖ = 1
  phase_weight : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ
  phase_weight_norm_one : ∀ j q, ‖phase_weight j q‖ = 1
  weight_factor : ∀ j q, P.weight j q = spectral_level j * phase_weight j q
```

This optional layer should not be imported by the CPSV16 §II Step 1 theorem unless an extra equal-modulus hypothesis is explicitly intended.

## Compatibility notes

* `SectorDecomposition` already has the right raw multiplicity representation.  The risk is adding extra spectral constraints on top of it.
* `basis_distinct` must use casts; otherwise different bond dimensions make the statement ill-typed.
* `HasBNTSectorData` is only eventual LI.  It does not imply normality, distinctness, or nonzero sector coefficients; those need fields or API lemmas.
* The existing finite geometric lemma can prove that a nonempty raw weight power sum with all weights nonzero is not eventually zero.  This is the exact algebraic fact needed for CPSV16 §II Step 1 when coefficient comparison isolates `c_N P.coeff N j`.
* The examples in `b77532f1` are still valuable smoke tests.  They should be kept after the core predicate is widened, because they check the equal-modulus subcase that originally exposed the one-copy bug.

## Bottom-line recommendation

Do not proceed with the proposed `spectralLevel`/`phaseWeight` fields as mandatory fields of the primary paper BNT predicate.  Amend the core predicate to accept arbitrary nonzero raw sector weights and equal-modulus or ordering data only as optional extra hypotheses.  This avoids the `C ⊕ D`, `C ⊕ (1/2)C`, and `C ⊕ (-C) ⊕ (1/2)C` counter-examples while preserving the intended fix for `C ⊕ (-C)`.
