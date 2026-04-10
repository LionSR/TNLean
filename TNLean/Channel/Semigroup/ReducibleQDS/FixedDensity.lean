/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS.Defs
import TNLean.MPS.Core.OrthogonalProjectionInvariance

/-!
# Fixed Density ↔ Kernel Element (Wolf Prop 7.6, (1) ↔ (2)) and (1) → (3)

This file proves the equivalence between conditions (1) and (2) of Wolf
Proposition 7.6, and the implication (1) → (3).
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## (1) ↔ (2): Fixed density ↔ kernel element

This is the simplest equivalence, following directly from the bridge
`L X = 0 ↔ exp(tL) X = X ∀ t ≥ 0` (Wolf §7.1, formalized in `Kernel.lean`).
-/

/-- **(2) → (1)**: A rank-deficient kernel element of `L` is automatically
a fixed point of the semigroup.

**Proof**: Apply `expSemigroup_apply_eq_self_of_generator_apply_eq_zero`. -/
theorem hasRankDeficientFixedDensity_of_hasRankDeficientKernelElement
    {L : Mat →ₗ[ℂ] Mat}
    (h : HasRankDeficientKernelElement L) :
    HasRankDeficientFixedDensity L := by
  obtain ⟨ρ₀, hρ_mem, hρ_rank, hL_zero⟩ := h
  exact ⟨ρ₀, hρ_mem, hρ_rank,
    expSemigroup_apply_eq_self_of_generator_apply_eq_zero L hL_zero⟩

/-- **(1) → (2)**: A rank-deficient fixed density of the semigroup lies in `ker(L)`.

**Proof**: Apply `generator_apply_eq_zero_of_expSemigroup_apply_eq_self`. -/
theorem hasRankDeficientKernelElement_of_hasRankDeficientFixedDensity
    {L : Mat →ₗ[ℂ] Mat}
    (h : HasRankDeficientFixedDensity L) :
    HasRankDeficientKernelElement L := by
  obtain ⟨ρ₀, hρ_mem, hρ_rank, hρ_fix⟩ := h
  exact ⟨ρ₀, hρ_mem, hρ_rank,
    generator_apply_eq_zero_of_expSemigroup_apply_eq_self L hρ_fix⟩

/-- **Wolf Proposition 7.6, (1) ↔ (2)**: A rank-deficient density matrix is
a fixed point of `exp(tL)` for all `t ≥ 0` if and only if it lies in the
kernel of `L`. -/
theorem wolf_prop_7_6_one_iff_two (L : Mat →ₗ[ℂ] Mat) :
    HasRankDeficientFixedDensity L ↔ HasRankDeficientKernelElement L :=
  ⟨hasRankDeficientKernelElement_of_hasRankDeficientFixedDensity,
   hasRankDeficientFixedDensity_of_hasRankDeficientKernelElement⟩

/-! ## (1) → (3): Fixed density → invariant compression

For a fixed density matrix `ρ₀`, every channel `expSemigroup L t` preserves the
support of `ρ₀`. Taking the support projection therefore produces a nontrivial
compression invariant under the whole semigroup.
-/

private theorem invariantCompression_of_supportProj_fixed_by_channel
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E) {ρ : Mat}
    (hρ_psd : ρ.PosSemidef) (hρ_fix : E ρ = ρ) :
    let P := MPSTensor.supportProj (D := D) ρ hρ_psd
    IsOrthogonalProjection P ∧
      ∀ X : Mat, P * E (P * X * P) * P = E (P * X * P) := by
  obtain ⟨r, K, hK⟩ := hE.cp
  have hE_eq_transfer : E = MPSTensor.transferMap (d := r) (D := D) K := by
    ext1 X
    simp only [MPSTensor.transferMap_apply]
    exact hK X
  have hρ_fix' : MPSTensor.transferMap (d := r) (D := D) K ρ = ρ := by
    simpa [hE_eq_transfer] using hρ_fix
  let P := MPSTensor.supportProj (D := D) ρ hρ_psd
  have hP_data :
      IsOrthogonalProjection P ∧
        (∀ i : Fin r, (1 - P) * K i * P = 0) := by
    simpa [P] using
      (MPSTensor.lowerZero_of_posSemidef_fixedPoint
        (d := r) (D := D) K ρ hρ_psd hρ_fix')
  refine ⟨hP_data.1, ?_⟩
  intro X
  rw [hE_eq_transfer]
  exact MPSTensor.lowerZero_implies_invariance K P hP_data.1 hP_data.2 X

private lemma not_posDef_of_proj_sandwich_eq_self
    {P ρ : Mat}
    (hP : IsOrthogonalProjection P)
    (hP1 : P ≠ 1)
    (hρ : P * ρ * P = ρ) :
    ¬ ρ.PosDef := by
  intro hρ_pd
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP.2, sub_self]
  have hQρ : (1 - P) * ρ = 0 := by
    conv_lhs => rw [← hρ]
    have h_expand : (1 - P) * (P * ρ * P) = ((1 - P) * P) * ρ * P := by
      noncomm_ring
    rw [h_expand, hQP, Matrix.zero_mul, Matrix.zero_mul]
  obtain ⟨u, hu⟩ := hρ_pd.isUnit
  have hQu : (1 - P) * (u : Mat) = 0 := by
    simpa [hu] using hQρ
  have h1P : 1 - P = 0 := by
    calc
      1 - P = (1 - P) * 1 := (Matrix.mul_one _).symm
      _ = (1 - P) * ((u : Mat) * (↑u⁻¹ : Mat)) := by rw [Units.mul_inv]
      _ = ((1 - P) * (u : Mat)) * (↑u⁻¹ : Mat) := (Matrix.mul_assoc _ _ _).symm
      _ = 0 * (↑u⁻¹ : Mat) := by rw [hQu]
      _ = 0 := Matrix.zero_mul _
  exact hP1 (sub_eq_zero.mp h1P).symm

/-- **Wolf Proposition 7.6, (1) → (3)**: A rank-deficient fixed density matrix
produces an invariant compression via its support projection. -/
theorem wolf_prop_7_6_one_implies_three
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (h : HasRankDeficientFixedDensity L) :
    HasInvariantCompression L := by
  obtain ⟨ρ₀, hρ_mem, ⟨Q, hQ_nt, hQρ⟩, hρ_fix⟩ := h
  have hρ_psd : ρ₀.PosSemidef := hρ_mem.1
  have hρ_ne : ρ₀ ≠ 0 := by
    intro hρ_zero
    simpa [hρ_zero] using hρ_mem.2
  have hρ_not_pd : ¬ ρ₀.PosDef :=
    not_posDef_of_proj_sandwich_eq_self hQ_nt.1 hQ_nt.2.2 hQρ
  let P : Mat := MPSTensor.supportProj (D := D) ρ₀ hρ_psd
  have hP_proj : IsOrthogonalProjection P :=
    MPSTensor.isOrthogonalProjection_supportProj (D := D) (ρ := ρ₀) (hρ := hρ_psd)
  have hP0 : P ≠ 0 :=
    MPSTensor.supportProj_ne_zero_of_ne_zero ρ₀ hρ_psd hρ_ne
  have hP1 : P ≠ 1 :=
    MPSTensor.supportProj_ne_one_of_not_posDef ρ₀ hρ_psd hρ_not_pd
  refine ⟨P, ⟨hP_proj, hP0, hP1⟩, ?_⟩
  intro t ht X
  have hChannel : IsChannel (expSemigroup L t) := hGKSL t ht
  have hInv :
      IsOrthogonalProjection P ∧
        (∀ Y : Mat, P * expSemigroup L t (P * Y * P) * P =
          expSemigroup L t (P * Y * P)) := by
    simpa [P] using
      (invariantCompression_of_supportProj_fixed_by_channel
        (D := D) hChannel hρ_psd (hρ_fix t ht))
  exact hInv.2 X

end -- noncomputable section
