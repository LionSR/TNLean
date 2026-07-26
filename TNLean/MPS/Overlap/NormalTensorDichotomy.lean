/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge

/-!
# Normal-tensor overlap dichotomy

The self-overlap of each normal tensor tends to one. Two normal tensors have rectangular matrix
product vector overlap tending to zero, unless their bond dimensions agree and they are related by
an invertible gauge and a unit phase. In the latter case the overlap modulus tends to one, and the
matrix product vectors differ by the corresponding power of the phase at every length.

## Main statements

* `IsNormalTensor.overlap_dichotomy`: both self-overlaps tend to one, and the cross-overlap tends
  to zero or has modulus tending to one with gauge-phase equivalence by a unit phase.
* `IsNormalTensor.mpv_phase_alternative`: the overlap tends to zero, or the matrix product vectors
  differ by a unit phase raised to each chain length.
* `EventuallyNonzeroProportionalMPV₂.exists_unit_phase_power_of_isNormalTensor`: eventually
  proportional normal matrix product vectors differ by the powers of one unit phase.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Appendix A,
  Lemma A.2 (equalMPS) and Corollary A.3 (eqV), lines 1080--1128.
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-- **Normal-tensor overlap dichotomy** (arXiv:1606.00608, Appendix A,
Lemma A.2 (equalMPS), lines 1080--1117).

For two normal tensors of positive, possibly different, bond dimensions, both self-overlaps tend
to one. Their rectangular overlap either tends to zero, or its modulus tends to one and the tensors
are related by an invertible gauge and a unit phase. -/
theorem IsNormalTensor.overlap_dichotomy
    [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B) :
    (Tendsto (fun N ↦ mpvOverlap (d := d) A A N) atTop (nhds 1) ∧
      Tendsto (fun N ↦ mpvOverlap (d := d) B B N) atTop (nhds 1)) ∧
        (Tendsto (fun N ↦ mpvOverlap (d := d) A B N) atTop (nhds 0) ∨
          (Tendsto (fun N ↦ ‖mpvOverlap (d := d) A B N‖) atTop (nhds (1 : ℝ)) ∧
            ∃ hdim : D₁ = D₂,
              ∃ X : GL (Fin D₂) ℂ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
                ∀ i, B i = ζ • ((X : Matrix (Fin D₂) (Fin D₂) ℂ) *
                  (cast (congr_arg (MPSTensor d) hdim) A) i *
                  (↑(X⁻¹) : Matrix (Fin D₂) (Fin D₂) ℂ)))) := by
  refine ⟨⟨hA.selfOverlap_tendsto_one, hB.selfOverlap_tendsto_one⟩, ?_⟩
  obtain ⟨σA, _hσA, _hσAfix, hTPA, hGaugeA, _hPrimA, hIrrA⟩ := hA.exists_tpGauge
  obtain ⟨σB, _hσB, _hσBfix, hTPB, hGaugeB, _hPrimB, hIrrB⟩ := hB.exists_tpGauge
  let A' := tpGauge (d := d) (D := D₁) A σA
  let B' := tpGauge (d := d) (D := D₂) B σB
  have hOverlapGauge : ∀ N,
      mpvOverlap (d := d) A B N = mpvOverlap (d := d) A' B' N := by
    intro N
    apply Finset.sum_congr rfl
    intro w _hw
    rw [GaugeEquiv.sameMPV hGaugeA N w, GaugeEquiv.sameMPV hGaugeB N w]
  by_cases hdim : D₁ = D₂
  · by_cases hGPE : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim) A) B
    · right
      rcases hGPE with ⟨X, ζ, _hζ, hrel⟩
      have hζnorm : ‖ζ‖ = 1 :=
        norm_eq_one_of_gaugePhase_cast_of_isNormalTensor hA hB hdim hrel
      have hmpv : ∀ (N : ℕ) (w : Fin N → Fin d),
          mpv B w = ζ ^ N * mpv A w := by
        intro N w
        rw [mpv_eq_pow_mul_of_gaugePhase
          (A := cast (congr_arg (MPSTensor d) hdim) A) (B := B) X ζ hrel N w,
          mpv_cast_dim hdim A N w]
      have hCrossEq : ∀ N,
          mpvOverlap (d := d) A B N =
            (star ζ) ^ N * mpvOverlap (d := d) A A N :=
        mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul hmpv
      have hCrossNormEq : ∀ N,
          ‖mpvOverlap (d := d) A B N‖ = ‖mpvOverlap (d := d) A A N‖ := by
        intro N
        rw [hCrossEq N, norm_mul, norm_pow, norm_star, hζnorm, one_pow, one_mul]
      have hSelfNorm : Tendsto (fun N ↦ ‖mpvOverlap (d := d) A A N‖)
          atTop (nhds (1 : ℝ)) := by
        simpa using hA.selfOverlap_tendsto_one.norm
      refine ⟨hSelfNorm.congr fun N ↦ (hCrossNormEq N).symm, hdim, X, ζ, hζnorm, hrel⟩
    · left
      have hNotPrepared : ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) hdim) A') B' := by
        intro hPrepared
        exact hGPE (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast
          hdim hGaugeA hPrepared hGaugeB)
      have hPrepared :=
        mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
          hdim A' B' hIrrA hIrrB hTPA hTPB hNotPrepared
      exact hPrepared.congr' (Eventually.of_forall fun N ↦ (hOverlapGauge N).symm)
  · left
    have hPrepared := mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      A' B' hIrrA hIrrB hTPA hTPB hdim
    exact hPrepared.congr' (Eventually.of_forall fun N ↦ (hOverlapGauge N).symm)

/-- **Exact phase alternative for normal tensors** (arXiv:1606.00608, Appendix A,
Corollary A.3 (eqV), lines 1121--1128).

For two normal tensors of positive, possibly different, bond dimensions, either the rectangular
overlap tends to zero, or their matrix product vectors differ at every length by a fixed unit phase
raised to that length. -/
theorem IsNormalTensor.mpv_phase_alternative
    [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B) :
    Tendsto (fun N ↦ mpvOverlap (d := d) A B N) atTop (nhds 0) ∨
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ N,
        mpvState (d := d) B N = ζ ^ N • mpvState (d := d) A N := by
  rcases hA.overlap_dichotomy hB with ⟨_hself, hzero | ⟨_hone, hdim, X, ζ, hζ, hrel⟩⟩
  · exact Or.inl hzero
  · right
    refine ⟨ζ, hζ, fun N ↦ ?_⟩
    ext w
    simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply]
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) hdim) A) (B := B) X ζ hrel N w,
      mpv_cast_dim hdim A N w]

/-- **Geometric proportionality scalar for two normal blocks.**

If two CPSV16 normal tensors generate matrix product vectors that are
eventually proportional by a nonzero scalar, then at every positive length
their proportionality may be chosen as the power of one fixed unit phase. The
bond dimensions may differ.

This theorem concerns the unit-phase part of the proportionality between
normalized normal blocks. It does not construct the positive geometric
rescaling needed to remove a length-dependent positive coefficient in
the commuting-form decomposition; the missing rescaling argument is
documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: CPSV16, Corollary eqV, lines 1121--1128, combined with the one-block
case of the proportionality hypothesis in Theorem thm1, lines 1167--1182;
see also arXiv:2011.12127, Theorem IV.4. -/
theorem EventuallyNonzeroProportionalMPV₂.exists_unit_phase_power_of_isNormalTensor
    [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hProp : EventuallyNonzeroProportionalMPV₂ A B)
    (hA : IsNormalTensor A) (hB : IsNormalTensor B) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin d,
      mpv A σ = a ^ N * mpv B σ := by
  have hEvent : ∀ᶠ N in atTop, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
      mpv A σ = c * mpv B σ := by
    exact hProp.mono fun _ hN ↦ ⟨hN.choose, hN.choose_spec.2⟩
  have hCrossNorm : Tendsto (fun N ↦ ‖mpvOverlap (d := d) A B N‖)
      atTop (nhds (1 : ℝ)) :=
    mpvOverlap_norm_tendsto_one_of_eventually_proportionalMPV₂
      A B hA.selfOverlap_tendsto_one hB.selfOverlap_tendsto_one hEvent
  rcases hA.mpv_phase_alternative hB with hZero | ⟨ζ, hζ, hState⟩
  · exfalso
    have hZeroNorm : Tendsto (fun N ↦ ‖mpvOverlap (d := d) A B N‖)
        atTop (nhds (0 : ℝ)) := by
      simpa using hZero.norm
    exact one_ne_zero (tendsto_nhds_unique hCrossNorm hZeroNorm)
  · refine ⟨ζ⁻¹, ?_, ?_⟩
    · rw [norm_inv, hζ, inv_one]
    · intro N _hN σ
      have hζ0 : ζ ≠ 0 := Complex.ne_zero_of_norm_eq_one hζ
      have hComponent := congrArg (fun v : MPVSpace d N ↦ v σ) (hState N)
      simp only [mpvState_apply, PiLp.smul_apply, smul_eq_mul] at hComponent
      rw [hComponent, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hζ0, one_pow, one_mul]

/-- Positive-length nonzero proportionality is a sufficient special case of
the eventual geometric-phase theorem for normal tensors.

Source: CPSV16, Corollary eqV, lines 1121--1128, combined with the one-block
case of the proportionality hypothesis in Theorem thm1, lines 1167--1182. -/
theorem NonzeroProportionalMPV₂.exists_unit_phase_power_of_isNormalTensor
    [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hProp : NonzeroProportionalMPV₂ A B)
    (hA : IsNormalTensor A) (hB : IsNormalTensor B) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin d,
      mpv A σ = a ^ N * mpv B σ :=
  hProp.eventually.exists_unit_phase_power_of_isNormalTensor hA hB

end MPSTensor
