/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlap

/-!
# Periodic overlap dichotomy: Case 1

This module contains the different-period case of Appendix A of
arXiv:1708.00029: if two periodic tensors have different periods, then their
overlap tends to $0$.

## Main declarations

* `periodicOverlap_tendsto_zero_of_ne_period`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 1: Different periods → orthogonal (Appendix A, first case) -/

/-- Cancellation: `X⁻¹ * (X * Y * Xᴴ) * (X⁻¹)ᴴ = Y`. -/
private theorem gl_conj_cancel (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ = Y := by
  have h1 : X⁻¹.val * X.val = 1 := Units.inv_mul X
  have h2 : X.valᴴ * X⁻¹.valᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.inv_mul]; simp
  calc _ = X⁻¹.val * X.val * Y * (X.valᴴ * X⁻¹.valᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * Y * 1 := by rw [h1, h2]
      _ = Y := by simp

/-- The conjugation `Y ↦ X Y Xᴴ` as a linear equivalence on matrices. -/
private noncomputable def glConjEquiv (X : GL (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearEquiv.ofLinear
    ((LinearMap.mulLeft ℂ X.val).comp (LinearMap.mulRight ℂ X.valᴴ))
    ((LinearMap.mulLeft ℂ X⁻¹.val).comp (LinearMap.mulRight ℂ X⁻¹.valᴴ))
    (LinearMap.ext fun Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, LinearMap.id_apply, ← Matrix.mul_assoc]
      rw [Units.mul_inv, one_mul, Matrix.mul_assoc Y,
        show X⁻¹.valᴴ * X.valᴴ = 1 from by
          rw [← Matrix.conjTranspose_mul, Units.mul_inv]; simp,
        mul_one])
    (LinearMap.ext fun Y => by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, LinearMap.id_apply, ← Matrix.mul_assoc]
      rw [Units.inv_mul, one_mul, Matrix.mul_assoc Y,
        show X.valᴴ * X⁻¹.valᴴ = 1 from by
          rw [← Matrix.conjTranspose_mul, Units.inv_mul]; simp,
        mul_one])

/-- **GaugePhaseEquiv preserves periods.**

If two periodic tensors (same bond dimension) are gauge-phase equivalent,
they must have the same period.

arXiv:0909.5347, via eigenvalue uniqueness (Wolf Theorem 6.3). -/
private theorem period_eq_of_gaugePhaseEquiv_of_isPeriodic
    [NeZero D] {A B : MPSTensor d D}
    {m_a m_b : ℕ} (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hGPE : GaugePhaseEquiv A B) : m_a = m_b := by
  obtain ⟨X, ζ, hζ_ne, hBi⟩ := hGPE
  -- PSD fixed points
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hA.leftCanonical (NeZero.pos D)
  obtain ⟨τ, hτ_psd, hτ_ne, hτ_fix⟩ :=
    exists_posSemidef_fixedPoint B hB.leftCanonical (NeZero.pos D)
  -- E_B is irreducible CP
  have hB_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB.irreducible
  have hB_cp : IsCPMap (transferMap (d := d) (D := D) B) := transferMap_isCPMap B
  -- Transfer map scaling: B = ζ • (X A X⁻¹) implies E_B = |ζ|² E_{XAX⁻¹}
  have hEB_eq : ∀ Y, transferMap (d := d) (D := D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * transferMap (d := d) (D := D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [transferMap_apply]
    simp_rw [hBi]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1; exact mul_comm _ _
  -- σ = X ρ Xᴴ is a PSD eigenvector of E_B with eigenvalue |ζ|²
  set σ := X.val * ρ * X.valᴴ
  have hσ_psd : σ.PosSemidef :=
    hρ_psd.mul_mul_conjTranspose_same X.val
  have hσ_ne : σ ≠ 0 := by
    intro h
    apply hρ_ne
    have h1 := congr_arg (X⁻¹.val * · * X⁻¹.valᴴ) h
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rwa [gl_conj_cancel] at h1
  have hEB_σ : transferMap (d := d) (D := D) B σ = (ζ * starRingEnd ℂ ζ) • σ := by
    simp only [σ, hEB_eq, gl_conj_cancel, hρ_fix]
  -- ζ * star ζ = ‖ζ‖²
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hζζ_pos : (0 : ℝ) < ‖ζ‖ ^ 2 := by positivity
  -- By eigenvalue uniqueness (Wolf 6.3): ‖ζ‖² = 1
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 :=
    (eigenvalue_unique_of_irreducible_cp
      (transferMap (d := d) (D := D) B) hB_cp hB_irrMap
      τ σ 1 (‖ζ‖ ^ 2) hτ_psd hτ_ne one_pos hσ_psd hσ_ne hζζ_pos
      (by simp [hτ_fix]) (by rw [hEB_σ, hζζ_real])).symm
  have hζ_norm : ‖ζ‖ = 1 := by nlinarith [norm_nonneg ζ]
  -- RepeatedBlocks A B with phase ζ⁻¹
  have hRepeated : RepeatedBlocks A B := by
    refine ⟨ζ⁻¹, X⁻¹, by rw [norm_inv, hζ_norm, inv_one], ?_⟩
    intro i
    -- Goal: A i = ζ⁻¹ • (↑(X⁻¹) * B i * ↑((X⁻¹)⁻¹))
    -- Simplify (X⁻¹)⁻¹ = X
    simp only [inv_inv]
    -- Goal: A i = ζ⁻¹ • (X⁻¹.val * B i * X.val)
    -- Show X⁻¹ * B i * X = ζ • A i
    have hconj : X⁻¹.val * B i * X.val = ζ • A i := by
      rw [hBi i, mul_smul_comm, smul_mul_assoc]
      congr 1
      calc X⁻¹.val * (X.val * A i * X⁻¹.val) * X.val
          = X⁻¹.val * X.val * A i * (X⁻¹.val * X.val) := by
            simp only [Matrix.mul_assoc]
        _ = 1 * A i * 1 := by rw [Units.inv_mul]
        _ = A i := by simp
    rw [hconj, smul_smul, inv_mul_cancel₀ hζ_ne, one_smul]
  -- Peripheral eigenvalue equality via conjugation
  have hSpec : peripheralEigenvalues (transferMap (d := d) (D := D) A) =
      peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
    have hEB_is_conj : transferMap (d := d) (D := D) B =
        (glConjEquiv X).conj (transferMap (d := d) (D := D) A) := by
      apply LinearMap.ext; intro Y
      rw [hEB_eq, hζζ_real, show (↑(‖ζ‖ ^ 2) : ℂ) = (1 : ℂ) from by simp [h_eig_eq],
        one_smul,
        show (glConjEquiv X).conj (transferMap (d := d) (D := D) A) Y =
          X.val * (transferMap (d := d) (D := D) A
            (X⁻¹.val * (Y * X⁻¹.valᴴ)) * X.valᴴ) from rfl]
      simp only [Matrix.mul_assoc]
    rw [hEB_is_conj]
    exact (peripheralEigenvalues_conj (glConjEquiv X)
      (transferMap (d := d) (D := D) A)).symm
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRepeated hSpec

/-- If two periodic tensors have different periods `m_a ≠ m_b`, their overlap
decays to zero.

*Proof*: split on whether `D₁ = D₂`. If not, use dimension mismatch
(`periodicOverlap_tendsto_zero_of_ne_dim`). If `D₁ = D₂`, assume for
contradiction that `GaugePhaseEquiv A B`; then
`period_eq_of_gaugePhaseEquiv_of_isPeriodic` gives `m_a = m_b`, contradicting
`hne`. So `¬ GaugePhaseEquiv`, and `mpvOverlap_tendsto_zero_of_irreducible_TP`
gives the result.

This is the first substantial argument in Appendix A of arXiv:1708.00029. -/
theorem periodicOverlap_tendsto_zero_of_ne_period
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B)
    (hne : m_a ≠ m_b) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  by_cases hD : D₁ = D₂
  · subst hD
    exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical
      (fun hGPE => hne (period_eq_of_gaugePhaseEquiv_of_isPeriodic hA hB hGPE))
  · exact mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B
      hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical hD


end MPSTensor
