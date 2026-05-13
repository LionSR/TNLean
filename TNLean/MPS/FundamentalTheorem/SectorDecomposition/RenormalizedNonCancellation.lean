/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.UnitModulusPowerSum
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.RateQuantifiedDecay

/-!
# Renormalised non-cancellation on the two-layer `IsBNTCanonicalFormSD` surface

**Status note (issue #1678).** This module is part of the rate-quantified
non-dominant per-block discharge stack.  Per issue #1678, this stack is
**no longer the active discharge route** for the proportional-MPV
non-decaying-overlap dispatcher: that dispatcher now exposes only the
weak combined-family existential and is closed directly via
`TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap.CombinedLI`.  This
module is retained as a parametric conditional-discharge framework for
potential future incarnations of the proof.

The two-layer per-block-projection skeleton `fixed_*_sectorDecomp_twoLayer`
in `PerBlockProjection.lean` carries an abstract hypothesis `hNoCancel`
asserting that the scaled assembled-to-block overlap
`c N · mpvOverlap Q.toTensor (Q.basis k₀) N` does not tend to zero.
For a non-dominant `Q`-block `k₀` on the two-layer surface, both factors
decay individually (the scalar witness is bounded above, and the overlap
decays by the spectral-level dominance), so the product tends to zero
unconditionally.  The abstract hypothesis is therefore unsatisfiable,
and the skeleton is unusable in the non-dominant branch.

The discharge presented in this module replaces the load-bearing role of
`hNoCancel` by a **renormalised** analytic statement: multiply both
sides of the projected proportionality by `(λ_{Q,k₀} ^ N)⁻¹` before
extracting the non-cancellation.  The Q-side of the renormalised
identity satisfies a non-decay property powered by

* `unitModulus_power_sum_not_tendsto_zero` on the within-sector
  quotient weights `ν_{k₀,q} := Q.weight k₀ q / λ_{Q,k₀}`
  (`‖ν_{k₀,q}‖ = 1` by `IsBNTCanonicalFormSD.weight_factor`); and
* the rate-quantified Q-internal cross-overlap decay
  `HasRateQuantifiedCrossOverlapDecay`, where the rate `η_{k,k₀}`
  satisfies `η_{k,k₀} · ‖λ_{Q,k} / λ_{Q,k₀}‖ < 1` and therefore beats
  the geometric blow-up from non-dominant ratios `‖λ_{Q,k} / λ_{Q,k₀}‖`
  that would otherwise dominate the renormalised cross-overlap sum.

## Main statement

`mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`: the renormalised
Q-side, `(λ_{Q,k₀} ^ N)⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N`, does
**not** tend to zero, under the two-layer canonical form structure,
the rate-quantified Q-internal cross-overlap decay, and a nonzero
self-overlap limit on the fixed `k₀`-block.

This statement is the analytic centerpiece of the renormalised
non-cancellation: it plays the role formerly intended for
`mpvOverlap_toTensor_basis_not_tendsto_zero`
(`HNoCancelDischarge.lean:87`) in the one-layer setting, but on the
two-layer surface where the dominant normalisation `‖λ_{Q,0}‖ = 1`
forces individual decay of the un-renormalised overlap.

## References

* CPSV16: Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product
  Density Operators*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
  Theorem `thm1`, lines 1170--1192.
* `audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md` —
  validation analysis confirming the renormalisation is required for
  non-dominant `k₀`.
* `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` — predecessor
  memo identifying the rate-quantification gap.
* `docs/paper-gaps/cpsv16_bnt_rate_quantification.tex` — paper-gap note
  for the cross-overlap rate hypothesis.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section RenormalisedNonCancellation

/-- **Renormalised assembled-to-block overlap does not vanish on the
two-layer surface.**

For a sector decomposition `Q` with the two-layer `IsBNTCanonicalFormSD`
structure, the rate-quantified Q-internal cross-overlap decay, an
arbitrary block index `k₀`, and a nonzero self-overlap limit at `k₀`,
the renormalised assembled-tensor-to-block overlap

`(λ_{Q,k₀} ^ N)⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N`

does not tend to zero as `N → ∞`.

The renormalisation factor `(λ_{Q,k₀} ^ N)⁻¹` makes the diagonal
contribution `(λ_{Q,k₀} ^ N)⁻¹ * Q.coeff N k₀ · self-overlap`
collapse to `(∑ q, ν_{k₀,q}^N) · self-overlap`, where
`ν_{k₀,q} := Q.weight k₀ q / λ_{Q,k₀}` are the unit-modulus quotient
weights (`weight_factor`).  The unit-modulus power sum
`∑ q, ν_{k₀,q}^N` does not tend to zero
(`unitModulus_power_sum_not_tendsto_zero`), so the diagonal cannot
vanish.  The off-diagonal contribution is forced to zero by the rate
hypothesis: for `k ≠ k₀`, the geometric factor `(λ_{Q,k} / λ_{Q,k₀})^N`
is dominated by the rate `(η_{k,k₀})^N · ‖λ_{Q,k}/λ_{Q,k₀}‖^N` whose
base `η_{k,k₀} · ‖λ_{Q,k}/λ_{Q,k₀}‖ < 1` by `rate_compatible`.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192 (renormalised
Q-side non-cancellation for non-dominant `k₀`). -/
lemma mpvOverlap_toTensor_basis_renorm_not_tendsto_zero
    (Q : SectorDecomposition d)
    (hQ : IsBNTCanonicalFormSD Q)
    (hQRate : HasRateQuantifiedCrossOverlapDecay Q hQ.spectralLevel)
    (k₀ : Fin Q.basisCount)
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ)) :
    ¬ Tendsto
        (fun N => (hQ.spectralLevel k₀ ^ N)⁻¹
                    * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0) := by
  classical
  intro hT
  -- Abbreviate the dominant-block parameter.
  set lam0 : ℂ := hQ.spectralLevel k₀ with hlam0_def
  have hlam0_ne : lam0 ≠ 0 := hQ.spectralLevel_ne_zero k₀
  have hlam0_pow_ne : ∀ N : ℕ, (lam0 ^ N) ≠ 0 := fun N => pow_ne_zero N hlam0_ne
  have hlam0_norm_pos : 0 < ‖lam0‖ := norm_pos_iff.mpr hlam0_ne
  -- Step 1: Expand `mpvOverlap Q.toTensor (Q.basis k₀) N` as a sum over
  -- basis blocks of `Q`.
  have hExpand : ∀ N : ℕ,
      mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
        = ∑ k : Fin Q.basisCount,
            Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := Q.basisCount) (dim := Q.basisDim)
      Q.toTensor Q.basis (N := N)
      (fun k => Q.coeff N k) ?_ (Q.basis k₀)
    intro σ
    exact Q.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Step 2: For each k ≠ k₀, the renormalised summand tends to zero.
  -- ‖summand k N‖ ≤ (copies k · C k k₀) · (‖λ_k / λ_{k₀}‖ · η k k₀)^N → 0.
  have hOffDiag : ∀ k : Fin Q.basisCount, k ≠ k₀ →
      Tendsto
        (fun N =>
          (lam0 ^ N)⁻¹ * (Q.coeff N k *
            mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N))
        atTop (nhds 0) := by
    intro k hk
    -- Unpack rate-quantified data.
    have hC_nn : 0 ≤ hQRate.rateC k k₀ := (hQRate.rate_nonneg hk).1
    have hη_nn : 0 ≤ hQRate.rateEta k k₀ := (hQRate.rate_nonneg hk).2
    have hRC : hQRate.rateEta k k₀ * ‖hQ.spectralLevel k / lam0‖ < 1 :=
      hQRate.rate_compatible hk
    have hOver_bd : ∀ N : ℕ,
        ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N‖
          ≤ hQRate.rateC k k₀ * hQRate.rateEta k k₀ ^ N :=
      fun N => hQRate.overlap_bound hk N
    have hCoeff_bd : ∀ N : ℕ,
        ‖Q.coeff N k‖
          ≤ ‖hQ.spectralLevel k‖ ^ N * (Q.copies k : ℝ) :=
      fun N => Q.norm_coeff_le_spectral_pow_mul_copies hQ N k
    -- Bound base `base := ‖λ_k / λ_{k₀}‖ · η k k₀`.
    set base : ℝ := ‖hQ.spectralLevel k / lam0‖ * hQRate.rateEta k k₀ with hbase_def
    have hbase_nn : 0 ≤ base := by
      have h1 : 0 ≤ ‖hQ.spectralLevel k / lam0‖ := norm_nonneg _
      exact mul_nonneg h1 hη_nn
    have hbase_lt_one : base < 1 := by
      have h := hRC; rw [mul_comm] at h
      exact h
    -- Upper bound function: `B N := (copies k · C) · base^N`.
    set C : ℝ := (Q.copies k : ℝ) * hQRate.rateC k k₀ with hC_def
    have hC_nn' : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hC_nn
    set B : ℕ → ℝ := fun N => C * base ^ N with hB_def
    have hB_tendsto : Tendsto B atTop (nhds 0) := by
      have hgeom : Tendsto (fun N : ℕ => base ^ N) atTop (nhds 0) := by
        refine tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nn ?_
        exact hbase_lt_one
      have := hgeom.const_mul C
      simpa [B] using this
    -- Norm bound on the summand.
    have hSum_bd : ∀ N : ℕ,
        ‖(lam0 ^ N)⁻¹ * (Q.coeff N k *
            mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)‖
          ≤ B N := by
      intro N
      have hinv_norm : ‖(lam0 ^ N)⁻¹‖ = (‖lam0‖ ^ N)⁻¹ := by
        rw [norm_inv, norm_pow]
      have hinv_pos : 0 < (‖lam0‖ ^ N)⁻¹ := by
        have : 0 < ‖lam0‖ ^ N := pow_pos hlam0_norm_pos N
        exact inv_pos.mpr this
      -- ‖λ_k‖ ^ N · (copies k) · (C k k₀ · η^N) · (‖lam0‖^N)⁻¹
      --   = (copies k · C k k₀) · ((‖λ_k‖ / ‖lam0‖)^N · η^N)
      --   = C · base^N.
      have hOver_nn := norm_nonneg (mpvOverlap (d := d)
        (Q.basis k) (Q.basis k₀) N)
      have hCoeff_nn := norm_nonneg (Q.coeff N k)
      have hLamN_nn : 0 ≤ ‖hQ.spectralLevel k‖ ^ N := pow_nonneg (norm_nonneg _) N
      have hCcopies_nn : 0 ≤ ‖hQ.spectralLevel k‖ ^ N * (Q.copies k : ℝ) :=
        mul_nonneg hLamN_nn (Nat.cast_nonneg _)
      have hηN_nn : 0 ≤ hQRate.rateEta k k₀ ^ N := pow_nonneg hη_nn N
      have hCη_nn : 0 ≤ hQRate.rateC k k₀ * hQRate.rateEta k k₀ ^ N :=
        mul_nonneg hC_nn hηN_nn
      calc ‖(lam0 ^ N)⁻¹ * (Q.coeff N k *
            mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)‖
          = ‖(lam0 ^ N)⁻¹‖ *
              (‖Q.coeff N k‖ *
                ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N‖) := by
                rw [norm_mul, norm_mul]
        _ = (‖lam0‖ ^ N)⁻¹ *
              (‖Q.coeff N k‖ *
                ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N‖) := by
                rw [hinv_norm]
        _ ≤ (‖lam0‖ ^ N)⁻¹ *
              ((‖hQ.spectralLevel k‖ ^ N * (Q.copies k : ℝ)) *
                (hQRate.rateC k k₀ * hQRate.rateEta k k₀ ^ N)) := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hinv_pos)
                exact mul_le_mul (hCoeff_bd N) (hOver_bd N) hOver_nn hCcopies_nn
        _ = (Q.copies k : ℝ) * hQRate.rateC k k₀ *
              ((‖hQ.spectralLevel k‖ ^ N * (‖lam0‖ ^ N)⁻¹) *
                hQRate.rateEta k k₀ ^ N) := by ring
        _ = C *
              ((‖hQ.spectralLevel k‖ / ‖lam0‖) ^ N * hQRate.rateEta k k₀ ^ N) := by
                rw [hC_def]
                congr 2
                rw [div_pow, div_eq_mul_inv]
        _ = C *
              ((‖hQ.spectralLevel k‖ / ‖lam0‖) * hQRate.rateEta k k₀) ^ N := by
                rw [mul_pow]
        _ = C * base ^ N := by
                simp only [hbase_def]
                congr 2
                rw [norm_div]
        _ = B N := by rw [hB_def]
    -- Squeeze: |summand N| ≤ B N → 0.
    refine squeeze_zero_norm hSum_bd hB_tendsto
  -- Step 3: Total off-diagonal contribution tends to zero.
  have hOffDiagSum : Tendsto
      (fun N => ∑ k ∈ (Finset.univ.erase k₀),
          (lam0 ^ N)⁻¹ *
            (Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N))
      atTop (nhds 0) := by
    have hTo : Tendsto
        (fun N => ∑ k ∈ (Finset.univ.erase k₀),
            (lam0 ^ N)⁻¹ *
              (Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N))
        atTop
        (nhds (∑ _k ∈ (Finset.univ.erase k₀ : Finset (Fin Q.basisCount)),
                (0 : ℂ))) := by
      refine tendsto_finset_sum (Finset.univ.erase k₀) ?_
      intro k hk
      exact hOffDiag k (Finset.ne_of_mem_erase hk)
    simpa using hTo
  -- Step 4: From `T N → 0`, the diagonal renormalised term tends to zero.
  have hDiag_tendsto : Tendsto
      (fun N =>
        (lam0 ^ N)⁻¹ * (Q.coeff N k₀ *
          mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N))
      atTop (nhds 0) := by
    -- diagonal = T - (off-diagonal sum)
    have hRew : ∀ N : ℕ,
        (lam0 ^ N)⁻¹ * (Q.coeff N k₀ *
            mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          = (lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            - ∑ k ∈ (Finset.univ.erase k₀),
                (lam0 ^ N)⁻¹ *
                  (Q.coeff N k *
                    mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N) := by
      intro N
      have hcomb :
          (lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            = (lam0 ^ N)⁻¹ * (Q.coeff N k₀ *
                mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
              + ∑ k ∈ (Finset.univ.erase k₀),
                  (lam0 ^ N)⁻¹ *
                    (Q.coeff N k *
                      mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N) := by
        rw [hExpand N, Finset.mul_sum]
        exact (Finset.add_sum_erase _ _ (Finset.mem_univ k₀)).symm
      exact eq_sub_of_add_eq hcomb.symm
    have hSub := hT.sub hOffDiagSum
    have hZero' : (0 : ℂ) - 0 = 0 := by ring
    rw [hZero'] at hSub
    refine hSub.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (hRew N).symm
  -- Step 5: Divide by the self-overlap (eventually nonzero) to deduce
  -- `(lam0 ^ N)⁻¹ * Q.coeff N k₀ → 0`.
  have hCoeff_tendsto : Tendsto
      (fun N => (lam0 ^ N)⁻¹ * Q.coeff N k₀) atTop (nhds 0) := by
    have hQuot : Tendsto
        (fun N =>
          ((lam0 ^ N)⁻¹ * (Q.coeff N k₀ *
              mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N))
            / mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
        atTop (nhds (0 / ℓ)) :=
      hDiag_tendsto.div hQ_self_limit hℓ_ne
    have hRewQuot : ∀ᶠ N in atTop,
        ((lam0 ^ N)⁻¹ * (Q.coeff N k₀ *
            mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N))
            / mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N
          = (lam0 ^ N)⁻¹ * Q.coeff N k₀ := by
      have hself_ne : ∀ᶠ N in atTop,
          mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N ≠ 0 :=
        hQ_self_limit.eventually_ne hℓ_ne
      filter_upwards [hself_ne] with N hN
      field_simp
    have := hQuot.congr' hRewQuot
    simpa using this
  -- Step 6: `(lam0 ^ N)⁻¹ * Q.coeff N k₀ = ∑ q, (Q.weight k₀ q / lam0)^N`,
  -- a unit-modulus power sum.  Contradicts non-decay.
  have hQuotient_form : ∀ N : ℕ,
      (lam0 ^ N)⁻¹ * Q.coeff N k₀
        = ∑ q : Fin (Q.copies k₀), (Q.weight k₀ q / lam0) ^ N := by
    intro N
    -- Q.coeff N k₀ = ∑ q, (Q.weight k₀ q)^N.
    have hCoeff_eq : Q.coeff N k₀
        = ∑ q : Fin (Q.copies k₀), (Q.weight k₀ q) ^ N := rfl
    rw [hCoeff_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [div_pow]
    field_simp [hlam0_pow_ne N]
  -- The power sum tends to zero.
  have hPowSum_tendsto : Tendsto
      (fun N => ∑ q : Fin (Q.copies k₀), (Q.weight k₀ q / lam0) ^ N)
      atTop (nhds 0) := by
    refine hCoeff_tendsto.congr ?_
    intro N
    exact hQuotient_form N
  -- Contradict `unitModulus_power_sum_not_tendsto_zero` on the
  -- within-sector quotient `q ↦ Q.weight k₀ q / lam0`.
  refine UnitModulusPowerSum.unitModulus_power_sum_not_tendsto_zero
    (r := Q.copies k₀) (Q.copies_pos k₀)
    (fun q : Fin (Q.copies k₀) => Q.weight k₀ q / lam0) ?_ hPowSum_tendsto
  intro q
  -- ‖Q.weight k₀ q / lam0‖ = 1 by `IsBNTCanonicalFormSD.weight_factor`.
  change ‖Q.sectors.weight k₀ q / hQ.spectralLevel k₀‖ = 1
  exact hQ.weight_factor k₀ q

end RenormalisedNonCancellation

end MPSTensor
