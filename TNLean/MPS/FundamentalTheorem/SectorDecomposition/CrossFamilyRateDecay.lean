/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.UnitModulusPowerSum
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.IsBNTCanonicalFormSD
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.RateQuantifiedDecay
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection

/-!
# Rate-quantified cross-family BNT overlap decay on `SectorDecomposition`

**Status note (issue #1678).** This module is part of the rate-quantified
non-dominant per-block discharge stack.  Per issue #1678, this stack is
**no longer the active discharge route** for the proportional-MPV
non-decaying-overlap dispatcher: that dispatcher now exposes only the
weak combined-family existential and is closed directly via
`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap.CombinedLI`.  This
module is retained as a parametric conditional-discharge framework for
potential future incarnations of the proof.

This module introduces the `Prop`-level predicate
`HasCrossFamilyRateDecay`, the cross-family analogue of
`HasRateQuantifiedCrossOverlapDecay` from
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDecay.lean`.
Whereas `HasRateQuantifiedCrossOverlapDecay` quantifies the decay of
**within-family** cross-overlaps `mpvOverlap (P.basis j) (P.basis k) N`
for `j ≠ k` inside a single sector decomposition `P`, the
cross-family predicate quantifies the decay of
`mpvOverlap (P.basis j) (Q.basis k) N` between basis blocks of two
**different** sector decompositions `P` and `Q`.

## Why a separate predicate

The two-layer per-block-projection skeleton
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`
in `PerBlockProjection.lean` (line 363) carries an abstract
`hNoCancel` hypothesis on the assembled-to-block overlap
`c N · mpvOverlap Q.toTensor (Q.basis k₀) N`.  The renormalised
discharge analysed in
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`
replaces `hNoCancel` by two complementary analytic facts:

* a **non-decay** result on the renormalised Q-side
  `(λ_{Q,k₀}^N)⁻¹ · mpvOverlap Q.toTensor (Q.basis k₀) N`, proved in
  `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RenormalizedNonCancellation.lean`
  as `mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`; and
* a **decay-to-zero** result on the renormalised LHS expansion
  `(λ_{Q,k₀}^N)⁻¹ · mpvOverlap P.toTensor (Q.basis k₀) N`, proved in
  the present module as
  `mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero`.

The latter LHS bound expands `P.toTensor` along `P`'s basis blocks
and produces a sum indexed by `j : Fin P.basisCount` whose individual
summands `(λ_{Q,k₀}^N)⁻¹ · P.coeff N j · mpvOverlap (P.basis j) (Q.basis k₀) N`
involve the cross-family overlap `mpvOverlap (P.basis j) (Q.basis k₀) N`.
Just as in the Q-internal renormalised non-decay statement, the
qualitative decay rate from
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`
(in `TNLean/MPS/Overlap/CastDecay.lean`) is **not** quantitative enough
to force the renormalised summand to zero: the rate `η_{j,k}` must
satisfy the comparison `η_{j,k} · ‖λ_{P,j} / λ_{Q,k}‖ < 1` to dominate
the geometric blow-up of the renormalisation factor.

The predicate below packages this rate-quantified hypothesis at the
structural level, on the same footing as the within-family analogue
in `RateQuantifiedDecay.lean`.

## Why `lamP, lamQ` are explicit parameters

The same design rationale as for `HasRateQuantifiedCrossOverlapDecay`
applies.  `IsBNTCanonicalFormSD` packages the spectral level inside
an existential and exposes it through `Classical.choose`-based
accessors; the cross-family predicate must compare `η_{j,k}` against
the ratio `‖lamP j / lamQ k‖`, so it needs *specific* `lamP, lamQ`
families rather than abstract existentials.  Taking them as explicit
parameters keeps the predicate free of any commitment to
`Classical.choose`: a caller building on top of
`IsBNTCanonicalFormSD P` and `IsBNTCanonicalFormSD Q` instantiates
`lamP := hP.spectralLevel` and `lamQ := hQ.spectralLevel`; a caller
working with concrete weight families instantiates them directly.

## References

* CPSV16: Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product
  Density Operators: Renormalization Fixed Points and Boundary
  Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
  - §II Step~1, lines 1170--1192: the BNT cross-overlap argument
    implicitly assumes a rate fast enough to dominate any
    weight-ratio blow-up between the two sector decompositions.
* `audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md` —
  Question 4, Shape A: the precise statement of the predicate
  formalised here.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RenormalizedNonCancellation.lean`
  — the Q-side renormalised non-decay companion result.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDecay.lean`
  — the within-family analogue `HasRateQuantifiedCrossOverlapDecay`.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-- **Rate-quantified cross-family BNT overlap decay.**

Given two sector decompositions `P Q : SectorDecomposition d` and
spectral levels `lamP : Fin P.basisCount → ℂ`,
`lamQ : Fin Q.basisCount → ℂ`, the predicate
`HasCrossFamilyRateDecay P Q lamP lamQ` asserts the existence of
nonnegative constants `C j k` and rates `η j k ∈ [0, 1)` for every
ordered pair `(j, k) : Fin P.basisCount × Fin Q.basisCount`, such that

* `η j k · ‖lamP j / lamQ k‖ < 1` — the rate strictly beats the
  cross-family spectral weight ratio along the direction `j ⟶ k`; and
* `‖mpvOverlap (P.basis j) (Q.basis k) N‖ ≤ C j k · (η j k)^N` for every
  `N`.

Unlike the within-family predicate
`HasRateQuantifiedCrossOverlapDecay`, the indices `j` and `k` here
range over the basis blocks of two **different** sector decompositions,
so there is no diagonal `j = k` to carve out: the bound is asserted
uniformly for every pair.

The two spectral levels `lamP, lamQ` are taken as explicit parameters
rather than packaged existentials: callers instantiate them with
`hP.spectralLevel` and `hQ.spectralLevel` (from
`IsBNTCanonicalFormSD`) or with concrete rescaled weights, as the
context requires.  This mirrors the design of
`HasRateQuantifiedCrossOverlapDecay` (see its module docstring for
the full rationale).

Source: arXiv:1606.00608, §II Step~1, lines 1170--1192;
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`,
Question~4, Shape~A. -/
structure HasCrossFamilyRateDecay
    (P Q : SectorDecomposition d)
    (lamP : Fin P.basisCount → ℂ) (lamQ : Fin Q.basisCount → ℂ) : Prop where
  /-- There exist a constant family `C` and a rate family `η`, indexed
  by ordered pairs `(j, k) : Fin P.basisCount × Fin Q.basisCount`,
  satisfying the four-fold conjunction of nonnegativity, sub-unitality,
  weight-ratio compatibility, and a geometric cross-family overlap
  bound. -/
  exists_rate :
    ∃ (C η : Fin P.basisCount → Fin Q.basisCount → ℝ),
      (∀ j k, 0 ≤ C j k ∧ 0 ≤ η j k ∧ η j k < 1 ∧
              η j k * ‖lamP j / lamQ k‖ < 1) ∧
      (∀ j k N,
        ‖mpvOverlap (d := d) (P.basis j) (Q.basis k) N‖
          ≤ C j k * (η j k) ^ N)

namespace HasCrossFamilyRateDecay

variable {P Q : SectorDecomposition d}
  {lamP : Fin P.basisCount → ℂ} {lamQ : Fin Q.basisCount → ℂ}

/-- **Cross-family rate constant** `C j k` for the bound between
`P.basis j` and `Q.basis k`. -/
noncomputable def rateC (h : HasCrossFamilyRateDecay P Q lamP lamQ) :
    Fin P.basisCount → Fin Q.basisCount → ℝ :=
  h.exists_rate.choose

/-- **Cross-family geometric decay rate** `η j k ∈ [0, 1)` for the
overlap between `P.basis j` and `Q.basis k`.  Combined with
`rate_compatible` this rate strictly beats the spectral weight ratio
`‖lamP j / lamQ k‖`. -/
noncomputable def rateEta (h : HasCrossFamilyRateDecay P Q lamP lamQ) :
    Fin P.basisCount → Fin Q.basisCount → ℝ :=
  h.exists_rate.choose_spec.choose

/-- Both the rate constant and the rate itself are nonnegative for every
cross-family pair `(j, k)`. -/
theorem rate_nonneg (h : HasCrossFamilyRateDecay P Q lamP lamQ)
    (j : Fin P.basisCount) (k : Fin Q.basisCount) :
    0 ≤ h.rateC j k ∧ 0 ≤ h.rateEta j k :=
  ⟨(h.exists_rate.choose_spec.choose_spec.1 j k).1,
   (h.exists_rate.choose_spec.choose_spec.1 j k).2.1⟩

/-- The cross-family rate is strictly less than `1` for every pair
`(j, k)`. -/
theorem rate_lt_one (h : HasCrossFamilyRateDecay P Q lamP lamQ)
    (j : Fin P.basisCount) (k : Fin Q.basisCount) :
    h.rateEta j k < 1 :=
  (h.exists_rate.choose_spec.choose_spec.1 j k).2.2.1

/-- **Weight-ratio compatibility.**  The cross-family rate is strict
enough to beat the spectral weight ratio along the direction `j ⟶ k`:
`η j k · ‖lamP j / lamQ k‖ < 1`.  This is the critical inequality that
the renormalised LHS bound demands. -/
theorem rate_compatible (h : HasCrossFamilyRateDecay P Q lamP lamQ)
    (j : Fin P.basisCount) (k : Fin Q.basisCount) :
    h.rateEta j k * ‖lamP j / lamQ k‖ < 1 :=
  (h.exists_rate.choose_spec.choose_spec.1 j k).2.2.2

/-- **Geometric cross-family overlap bound.**  The overlap between
basis blocks of two different sector decompositions decays at least
as fast as `C j k · (η j k)^N`. -/
theorem overlap_bound (h : HasCrossFamilyRateDecay P Q lamP lamQ)
    (j : Fin P.basisCount) (k : Fin Q.basisCount) (N : ℕ) :
    ‖mpvOverlap (d := d) (P.basis j) (Q.basis k) N‖
      ≤ h.rateC j k * (h.rateEta j k) ^ N :=
  h.exists_rate.choose_spec.choose_spec.2 j k N

end HasCrossFamilyRateDecay

section RenormalisedLHSBound

/-- **Renormalised assembled-to-block cross-family overlap vanishes
on the two-layer surface.**

Companion to `mpvOverlap_toTensor_basis_renorm_not_tendsto_zero` in
`RenormalizedNonCancellation.lean`.  For sector decompositions `P` and
`Q` with the two-layer `IsBNTCanonicalFormSD` structure, the
rate-quantified cross-family overlap decay, and an arbitrary
`Q`-block index `k₀`, the renormalised assembled-tensor-to-block
overlap

`(λ_{Q,k₀} ^ N)⁻¹ * mpvOverlap P.toTensor (Q.basis k₀) N`

tends to zero as `N → ∞`.

Each term in the basis expansion of `P.toTensor` becomes, after
renormalisation,
`(λ_{Q,k₀} ^ N)⁻¹ * P.coeff N j * mpvOverlap (P.basis j) (Q.basis k₀) N`,
whose norm is dominated by
`copies_P j · C_{j,k₀} · (η_{j,k₀} · ‖λ_{P,j} / λ_{Q,k₀}‖)^N`.  The
base of this geometric factor is `< 1` by `rate_compatible`, so each
summand decays to zero, and the finite sum then tends to zero by
`tendsto_finset_sum`.

Source: arXiv:1606.00608, §II Step~1, lines 1170--1192 (renormalised
LHS decay against a non-dominant `Q`-block).
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`,
Question~3 (the LHS half of the renormalised discharge). -/
lemma mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hRate : HasCrossFamilyRateDecay P Q hP.spectralLevel hQ.spectralLevel)
    (k₀ : Fin Q.basisCount) :
    Tendsto
      (fun N => (hQ.spectralLevel k₀ ^ N)⁻¹
                  * mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
      atTop (nhds 0) := by
  classical
  -- Abbreviate the renormalisation parameter.
  set lam0 : ℂ := hQ.spectralLevel k₀ with hlam0_def
  have hlam0_ne : lam0 ≠ 0 := hQ.spectralLevel_ne_zero k₀
  have hlam0_norm_pos : 0 < ‖lam0‖ := norm_pos_iff.mpr hlam0_ne
  -- Expand `mpvOverlap P.toTensor (Q.basis k₀) N` along `P`'s basis.
  have hExpand : ∀ N : ℕ,
      mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = ∑ j : Fin P.basisCount,
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := P.basisCount) (dim := P.basisDim)
      P.toTensor P.basis (N := N)
      (fun j => P.coeff N j) ?_ (Q.basis k₀)
    intro σ
    exact P.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Each renormalised summand tends to zero by the cross-family rate.
  have hPerJ : ∀ j : Fin P.basisCount,
      Tendsto
        (fun N =>
          (lam0 ^ N)⁻¹ *
            (P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N))
        atTop (nhds 0) := by
    intro j
    have hC_nn : 0 ≤ hRate.rateC j k₀ := (hRate.rate_nonneg j k₀).1
    have hη_nn : 0 ≤ hRate.rateEta j k₀ := (hRate.rate_nonneg j k₀).2
    have hRC : hRate.rateEta j k₀ * ‖hP.spectralLevel j / lam0‖ < 1 :=
      hRate.rate_compatible j k₀
    have hOver_bd : ∀ N : ℕ,
        ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖
          ≤ hRate.rateC j k₀ * hRate.rateEta j k₀ ^ N :=
      fun N => hRate.overlap_bound j k₀ N
    have hCoeff_bd : ∀ N : ℕ,
        ‖P.coeff N j‖
          ≤ ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ) :=
      fun N => P.norm_coeff_le_spectral_pow_mul_copies hP N j
    -- Define the geometric base `base := ‖λ_{P,j} / λ_{Q,k₀}‖ · η j k₀`.
    set base : ℝ := ‖hP.spectralLevel j / lam0‖ * hRate.rateEta j k₀
      with hbase_def
    have hbase_nn : 0 ≤ base :=
      mul_nonneg (norm_nonneg _) hη_nn
    have hbase_lt_one : base < 1 := by
      have h := hRC; rw [mul_comm] at h
      exact h
    -- Define the geometric upper bound `B N := C · base^N`.
    set C : ℝ := (P.copies j : ℝ) * hRate.rateC j k₀ with hC_def
    have hC_nn' : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hC_nn
    set B : ℕ → ℝ := fun N => C * base ^ N with hB_def
    have hB_tendsto : Tendsto B atTop (nhds 0) := by
      have hgeom : Tendsto (fun N : ℕ => base ^ N) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nn hbase_lt_one
      have := hgeom.const_mul C
      simpa [B] using this
    -- Norm of the renormalised summand is bounded by `B N`.
    have hSum_bd : ∀ N : ℕ,
        ‖(lam0 ^ N)⁻¹ *
            (P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)‖
          ≤ B N := by
      intro N
      have hinv_norm : ‖(lam0 ^ N)⁻¹‖ = (‖lam0‖ ^ N)⁻¹ := by
        rw [norm_inv, norm_pow]
      have hinv_pos : 0 < (‖lam0‖ ^ N)⁻¹ := by
        have : 0 < ‖lam0‖ ^ N := pow_pos hlam0_norm_pos N
        exact inv_pos.mpr this
      have hOver_nn := norm_nonneg
        (mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
      have hLamN_nn : 0 ≤ ‖hP.spectralLevel j‖ ^ N :=
        pow_nonneg (norm_nonneg _) N
      have hCcopies_nn : 0 ≤ ‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ) :=
        mul_nonneg hLamN_nn (Nat.cast_nonneg _)
      have hηN_nn : 0 ≤ hRate.rateEta j k₀ ^ N := pow_nonneg hη_nn N
      calc ‖(lam0 ^ N)⁻¹ *
            (P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)‖
          = ‖(lam0 ^ N)⁻¹‖ *
              (‖P.coeff N j‖ *
                ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖) := by
                rw [norm_mul, norm_mul]
        _ = (‖lam0‖ ^ N)⁻¹ *
              (‖P.coeff N j‖ *
                ‖mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N‖) := by
                rw [hinv_norm]
        _ ≤ (‖lam0‖ ^ N)⁻¹ *
              ((‖hP.spectralLevel j‖ ^ N * (P.copies j : ℝ)) *
                (hRate.rateC j k₀ * hRate.rateEta j k₀ ^ N)) := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hinv_pos)
                exact mul_le_mul (hCoeff_bd N) (hOver_bd N) hOver_nn hCcopies_nn
        _ = (P.copies j : ℝ) * hRate.rateC j k₀ *
              ((‖hP.spectralLevel j‖ ^ N * (‖lam0‖ ^ N)⁻¹) *
                hRate.rateEta j k₀ ^ N) := by ring
        _ = C *
              ((‖hP.spectralLevel j‖ / ‖lam0‖) ^ N *
                hRate.rateEta j k₀ ^ N) := by
                rw [hC_def]
                congr 2
                rw [div_pow, div_eq_mul_inv]
        _ = C *
              ((‖hP.spectralLevel j‖ / ‖lam0‖) *
                  hRate.rateEta j k₀) ^ N := by
                rw [mul_pow]
        _ = C * base ^ N := by
                simp only [hbase_def]
                congr 2
                rw [norm_div]
        _ = B N := by rw [hB_def]
    exact squeeze_zero_norm hSum_bd hB_tendsto
  -- Sum the per-`j` limits.
  have hSum_tendsto : Tendsto
      (fun N => ∑ j : Fin P.basisCount,
          (lam0 ^ N)⁻¹ *
            (P.coeff N j * mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N))
      atTop (nhds 0) := by
    have hTo : Tendsto
        (fun N => ∑ j : Fin P.basisCount,
            (lam0 ^ N)⁻¹ *
              (P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N))
        atTop
        (nhds (∑ _j : Fin P.basisCount, (0 : ℂ))) := by
      refine tendsto_finset_sum Finset.univ ?_
      intro j _
      exact hPerJ j
    simpa using hTo
  -- Rewrite the goal via the expansion and the sum-pull-through.
  refine hSum_tendsto.congr ?_
  intro N
  rw [hExpand N, Finset.mul_sum]

end RenormalisedLHSBound

/-!
## Next composition step

The two complementary renormalised analytic facts now in place are:

* `mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`
  (in `RenormalizedNonCancellation.lean`) — the Q-side renormalised
  non-decay.
* `mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero` (above) — the
  LHS-side renormalised decay.

The next downstream consumer composes them into the single-sequence
non-cancellation lemma `hNoCancel_renorm_single_seq`, which in turn
feeds the full discharge theorem, named in prose
`fixed_right_..._twoLayer_rateQuantified` and in full
`fixed_right_all_overlaps_decay_false_of_`
`eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer_rateQuantified`.
Neither is implemented in this PR; they are deferred to subsequent
increments, with the corresponding spec recorded in
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`,
Question~5.
-/

end MPSTensor
