/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.VirtualUnitaryGauge

/-!
# Virtual rigidity from equality on even periodic chains

Equality of the even periodic families of two reduced canonical MPU tensors
still determines an unblocked virtual unitary gauge, with a possible sign.
The normal-tensor overlap dichotomy supplies the unblocked gauge: its vanishing
overlap alternative contradicts equality along the even subsequence. Equality
at length two then forces the scalar phase to square to one. No extra physical
blocking is used.

Source: arXiv:1703.09188, `PropChiral`, lines 1209–1252, and CPSV16,
Corollary `eqV`, lines 1121–1128. This is the virtual comparison needed before
reconstructing the four-spin source gates, not the local gate criterion itself.
**Scope restriction (reduced canonical presentation):** The supplied full-support
presentation restriction is documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`; the even-length issue is
recorded in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- Even-chain equality determines an unblocked virtual unitary similarity
up to a sign. In particular, this does not infer equality on odd chains.
Source: CPSV17, `PropChiral`, lines 1209–1252, using the normal overlap
dichotomy of CPSV16, Corollary `eqV`, lines 1121–1128. -/
theorem IsMPUCanonicalFormII.exists_unitary_virtual_sign_gauge_of_mpo_eq_even
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → Even N → mpo U N = mpo V N) :
    ∃ (hdim : D₁ = D₂) (η : ℂ) (z : Matrix.unitaryGroup (Fin D₂) ℂ),
      (η = 1 ∨ η = -1) ∧ ∀ i j : Fin d,
        V i j = η • ((z : Matrix (Fin D₂) (Fin D₂) ℂ) *
          (cast (congrArg (MPOTensor d) hdim) U) i j *
          (z : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ) := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D₁ := hU.neZero_bond
  let : NeZero D₂ := hV.neZero_bond
  have hMPV : ∀ N : ℕ, 1 < N → Even N → ∀ w : Fin N → Fin (d * d),
      MPSTensor.mpv U.normalizedFlattening w =
        MPSTensor.mpv V.normalizedFlattening w := by
    intro N hN heven w
    change MPSTensor.mpv (fun ij ↦ ((Real.sqrt d : ℂ)⁻¹) • U.toMPSTensor ij) w =
      MPSTensor.mpv (fun ij ↦ ((Real.sqrt d : ℂ)⁻¹) • V.toMPSTensor ij) w
    rw [MPSTensor.mpv_smul, MPSTensor.mpv_smul]
    congr 1
    rw [MPOTensor.mpv_toMPSTensor, MPOTensor.mpv_toMPSTensor, hEq N hN heven]
  have hA := hU.isNormalTensor_normalizedFlattening
  have hB := hV.isNormalTensor_normalizedFlattening
  have hEvenTop : Filter.Tendsto (fun n : ℕ ↦ 2 * n) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun n : ℕ ↦ n) (fun n ↦ by omega)
      Filter.tendsto_id
  obtain ⟨_, hzero | ⟨_, hdim, X, η, hη, hrel⟩⟩ := hA.overlap_dichotomy hB
  · exfalso
    have hCrossSelf : ∀ᶠ n : ℕ in Filter.atTop,
        MPSTensor.mpvOverlap U.normalizedFlattening V.normalizedFlattening (2 * n) =
          MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening (2 * n) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      unfold MPSTensor.mpvOverlap
      apply Finset.sum_congr rfl
      intro w _
      rw [← hMPV (2 * n) (by omega) (even_two_mul n) w]
    have hone := (hA.selfOverlap_tendsto_one.comp hEvenTop).congr' hCrossSelf.symm
    exact zero_ne_one (tendsto_nhds_unique (hzero.comp hEvenTop) hone)
  · have hη0 : η ≠ 0 := Complex.ne_zero_of_norm_eq_one hη
    have hηsq : η ^ 2 = 1 := by
      have hSelf : MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening 2 = 1 := by
        rw [← MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap]
        exact hU.isMPU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega)
      have hNonzero : ∃ w : Fin 2 → Fin (d * d),
          MPSTensor.mpv U.normalizedFlattening w ≠ 0 := by
        by_contra hall
        push Not at hall
        simp only [MPSTensor.mpvOverlap, hall, star_zero, mul_zero,
          Finset.sum_const_zero] at hSelf
        exact zero_ne_one hSelf
      obtain ⟨w, hw⟩ := hNonzero
      have hphase := MPSTensor.mpv_eq_pow_mul_of_gaugePhase
        (A := cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening)
        (B := V.normalizedFlattening) X η hrel 2 w
      rw [MPSTensor.mpv_cast_dim hdim U.normalizedFlattening 2 w,
        ← hMPV 2 (by omega) (by decide) w] at hphase
      apply mul_right_cancel₀ hw
      simpa only [one_mul] using hphase.symm
    have hLeftU : MPSTensor.IsLeftCanonical
        (cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening) :=
      (MPSTensor.leftCanonical_cast_dim hdim U.normalizedFlattening).2
        hU.isLeftCanonical_normalizedFlattening
    have hIrrU : Kraus.IsIrreducibleFamily
        (cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening) :=
      (MPSTensor.isIrreducibleTensor_cast_dim hdim U.normalizedFlattening).2
        hA.no_invariant_proj
    obtain ⟨z, _, hRel⟩ :=
      MPSTensor.exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
        X η hη0 hrel hLeftU hV.isLeftCanonical_normalizedFlattening hIrrU
        hB.no_invariant_proj
    refine ⟨hdim, η, z, sq_eq_one_iff.mp hηsq, ?_⟩
    intro i j
    have h := hRel (finProdFinEquiv (i, j))
    have hcast : cast (congrArg (MPSTensor (d * d)) hdim) U.normalizedFlattening =
        (cast (congrArg (MPOTensor d) hdim) U).normalizedFlattening := by
      cases hdim
      rfl
    rw [hcast] at h
    simp only [normalizedFlattening, toMPSTensor,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat] at h
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at h
    have hc : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 := by
      apply inv_ne_zero
      exact Complex.ofReal_ne_zero.mpr ((Real.sqrt_pos.mpr
        (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))).ne')
    apply Matrix.ext
    intro a b
    have he := congrArg (fun M : Matrix (Fin D₂) (Fin D₂) ℂ ↦ M a b) h
    simp only [Matrix.smul_apply, smul_eq_mul] at he ⊢
    apply mul_left_cancel₀ hc
    simpa only [mul_assoc, mul_left_comm η] using he

end MPOTensor
