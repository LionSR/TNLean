/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.RenormalizedNonCancellation
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.CrossFamilyRateDecay

/-!
# Rate-quantified discharge of the two-layer per-block projection

This module composes the two renormalised analytic facts proved
upstream into the full two-layer per-block-projection contradiction for
a non-dominant `Q`-block `k₀` on the `IsBNTCanonicalFormSD` surface:

* `mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`
  (`RenormalizedNonCancellation.lean`) — the Q-side renormalised
  non-decay.
* `mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero`
  (`CrossFamilyRateDecay.lean`) — the renormalised LHS decay along
  cross-family overlaps.

The downstream consumers are the abstract `hNoCancel` of the
two-layer skeleton `fixed_right_..._sectorDecomp_twoLayer` and its
mirror `_left` (in `PerBlockProjection.lean`).  The audit memo
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`
established that the abstract `hNoCancel` is vacuously false on the
non-dominant branch, so the discharge cannot proceed through the
abstract skeleton.  Instead, the present module substitutes the
renormalised analytic ingredients directly, yielding a discharge
that is sound on the non-dominant branch.

## Main statements

* `hNoCancel_renorm_single_seq`: the single-sequence renormalised
  non-cancellation, given the two rate-quantified hypotheses, the
  nonzero self-overlap limit, a single scalar witness `c` with a
  positive norm lower bound, and the per-length proportionality.

* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_`
  `sectorDecomp_twoLayer_rateQuantified`: the full two-layer right-block
  discharge — extracts the scalar witness from
  `EventuallyNonzeroProportionalMPV₂` and chains through
  `hNoCancel_renorm_single_seq`.

* `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_`
  `sectorDecomp_twoLayer_rateQuantified`: the symmetric left-block
  discharge — reduces to the right-block version via the family-swap
  pattern (`EventuallyNonzeroProportionalMPV₂.symm`).

## References

* Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Theorem `thm1`,
  lines 1170--1192.
* `audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`,
  Question~5.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section RateQuantifiedDischarge

/-- **Single-sequence renormalised non-cancellation on the two-layer
surface.**

For sector decompositions `P, Q` carrying the two-layer
`IsBNTCanonicalFormSD` structure, the rate-quantified Q-internal
cross-overlap decay, the rate-quantified cross-family overlap decay,
a fixed `Q`-block index `k₀` with a nonzero self-overlap limit, and a
single scalar witness `c : ℕ → ℂ` of the eventual proportionality
with a positive norm lower bound, the configuration is contradictory.

The proof renormalises the projected proportionality identity by
`(λ_{Q,k₀} ^ N)⁻¹`.  The renormalised LHS tends to zero by
`mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero`, and the projected
identity rewrites it as `c N * T N` where
`T N := (λ_{Q,k₀} ^ N)⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N`.
The norm lower bound on `c N` then yields `‖T N‖ → 0`, contradicting
`mpvOverlap_toTensor_basis_renorm_not_tendsto_zero`.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192 (the
non-dominant `k₀` branch). -/
lemma hNoCancel_renorm_single_seq
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hQRate : HasRateQuantifiedCrossOverlapDecay Q hQ.spectralLevel)
    (hCrossRate : HasCrossFamilyRateDecay P Q hP.spectralLevel hQ.spectralLevel)
    (k₀ : Fin Q.basisCount)
    (hQ_self_limit : ∃ ℓ : ℂ, ℓ ≠ 0 ∧
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (c : ℕ → ℂ)
    (hc_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖)
    (hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
        mpv P.toTensor σ = c N * mpv Q.toTensor σ) :
    False := by
  classical
  obtain ⟨ℓ, hℓ_ne, hQ_self⟩ := hQ_self_limit
  obtain ⟨δ, hδpos, hδ⟩ := hc_lower
  set lam0 : ℂ := hQ.spectralLevel k₀ with hlam0_def
  -- The renormalised LHS overlap tends to zero by the cross-family bound.
  have hLHS_renorm :
      Tendsto
        (fun N => (lam0 ^ N)⁻¹ * mpvOverlap (d := d) P.toTensor (Q.basis k₀) N)
        atTop (nhds 0) :=
    mpvOverlap_toTensor_basis_renorm_LHS_tendsto_zero P Q hP hQ hCrossRate k₀
  -- The projected proportionality identity holds eventually.
  have hProj : ∀ᶠ N in atTop,
      (lam0 ^ N)⁻¹ * mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
        = c N
            * ((lam0 ^ N)⁻¹
                * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N) := by
    refine hc_eq.mono ?_
    intro N hN
    have hOvEq :
        mpvOverlap (d := d) P.toTensor (Q.basis k₀) N
          = c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N :=
      mpvOverlap_eq_mul_of_mpv_eq_mul (d := d) P.toTensor Q.toTensor
        (c N) hN (Q.basis k₀)
    rw [hOvEq]
    ring
  -- Hence `c N * T N → 0`, where
  -- `T N = (lam0 ^ N)⁻¹ * mpvOverlap Q.toTensor (Q.basis k₀) N`.
  have hcT : Tendsto
      (fun N =>
        c N
          * ((lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N))
      atTop (nhds 0) :=
    hLHS_renorm.congr' hProj
  -- From `c N * T N → 0` and `‖c N‖ ≥ δ > 0`, deduce `‖T N‖ → 0`.
  have hcT_norm : Tendsto
      (fun N =>
        ‖c N
          * ((lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)‖)
      atTop (nhds 0) := by
    have := hcT.norm
    simpa using this
  set bound : ℕ → ℝ := fun N =>
    ‖c N
        * ((lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)‖
      / δ with hbound_def
  have hbound_tendsto : Tendsto bound atTop (nhds 0) := by
    have := hcT_norm.div_const δ
    simpa [bound] using this
  have hle : ∀ᶠ N in atTop,
      ‖(lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
        ≤ bound N := by
    filter_upwards [hδ] with N hN
    have hTnn :
        0 ≤ ‖(lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
      norm_nonneg _
    have h1 :
        ‖c N
            * ((lam0 ^ N)⁻¹
                * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)‖
          = ‖c N‖
              * ‖(lam0 ^ N)⁻¹
                  * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
      norm_mul _ _
    have h2 :
        δ * ‖(lam0 ^ N)⁻¹
                * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
          ≤ ‖c N‖
              * ‖(lam0 ^ N)⁻¹
                  * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
      mul_le_mul_of_nonneg_right hN hTnn
    have h3 :
        ‖(lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
          ≤ (‖c N‖
                * ‖(lam0 ^ N)⁻¹
                    * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖)
              / δ := by
      rw [le_div_iff₀ hδpos, mul_comm]
      exact h2
    have h4 :
        (‖c N‖
            * ‖(lam0 ^ N)⁻¹
                * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖)
          / δ
          = bound N := by
      simp only [bound]
      rw [← h1]
    exact h3.trans h4.le
  have hTnorm : Tendsto
      (fun N =>
        ‖(lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖)
      atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      hle hbound_tendsto
  have hT_tendsto : Tendsto
      (fun N => (lam0 ^ N)⁻¹ * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hTnorm
  -- Contradiction with the Q-side renormalised non-decay.
  exact mpvOverlap_toTensor_basis_renorm_not_tendsto_zero
    Q hQ hQRate k₀ hℓ_ne hQ_self hT_tendsto

set_option linter.style.longLine false in
/-- **Two-layer right-block discharge under rate quantification.**

The renormalised counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`
(in `PerBlockProjection.lean`).  In the abstract two-layer skeleton,
the load-bearing `hNoCancel` hypothesis is unsatisfiable on the
non-dominant `k₀` branch (per
`audits/2026-05-13_cpsv16_ft_renormalized_discharge_design.md`).  The
present theorem replaces `hNoCancel` by the two rate hypotheses
`hQRate`, `hCrossRate` and the nonzero self-overlap limit, and
discharges the contradiction via the renormalised analytic argument.

The qualitative decay of cross-family overlaps used in the abstract
form (`hAllDecay`) is automatically derivable from `hCrossRate`:
each cross-family overlap is bounded by `C j k₀ · η j k₀ ^ N` with
`η j k₀ < 1`, and therefore tends to zero.  The present signature
therefore omits the redundant `hAllDecay` hypothesis.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. -/
theorem fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer_rateQuantified
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hQRate : HasRateQuantifiedCrossOverlapDecay Q hQ.spectralLevel)
    (hCrossRate : HasCrossFamilyRateDecay P Q hP.spectralLevel hQ.spectralLevel)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hQ_self_limit : ∃ ℓ : ℂ, ℓ ≠ 0 ∧
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (hc_lower :
        ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    False := by
  classical
  -- Extract a scalar sequence `c` witnessing the eventual proportionality.
  set Pprop : ℕ → Prop := fun N =>
    ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c * mpv Q.toTensor σ
  have hEvent : ∀ᶠ N in atTop, Pprop N := hProp
  let c : ℕ → ℂ := fun N => if hN : Pprop N then Classical.choose hN else 1
  have hc_eq : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv P.toTensor σ = c N * mpv Q.toTensor σ := by
    refine hEvent.mono ?_
    intro N hN
    simp only [c]
    rw [dif_pos hN]
    exact (Classical.choose_spec hN).2
  exact hNoCancel_renorm_single_seq P Q hP hQ hQRate hCrossRate k₀
    hQ_self_limit c (hc_lower c hc_eq) hc_eq

set_option linter.style.longLine false in
/-- **Two-layer left-block discharge under rate quantification.**

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer_rateQuantified`
fixing a `P`-block `j₀` instead of a `Q`-block.  Reduces to the
right-block rate-quantified version after swapping the two families
(`EventuallyNonzeroProportionalMPV₂.symm`).

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185. -/
theorem fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer_rateQuantified
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hPRate : HasRateQuantifiedCrossOverlapDecay P hP.spectralLevel)
    (hCrossRate : HasCrossFamilyRateDecay Q P hQ.spectralLevel hP.spectralLevel)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hP_self_limit : ∃ ℓ : ℂ, ℓ ≠ 0 ∧
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N)
          atTop (nhds ℓ))
    (hc_lower :
        ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    False :=
  fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer_rateQuantified
    Q P hQ hP hPRate hCrossRate hProp.symm j₀ hP_self_limit hc_lower

end RateQuantifiedDischarge

end MPSTensor
