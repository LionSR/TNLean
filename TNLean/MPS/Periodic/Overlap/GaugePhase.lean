/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Periodic.Defs
import TNLean.QPF.Assembly

/-!
# Gauge-phase matrix identities

This module contains elementary matrix identities used in the periodic-overlap
arguments of Appendix A of arXiv:1708.00029.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Cancellation for conjugation by an invertible matrix:
$X^{-1}(X Y X^\dagger)(X^{-1})^\dagger = Y$. -/
theorem gaugePhase_conj_cancel (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ = Y := by
  have h1 : X⁻¹.val * X.val = 1 := Units.inv_mul X
  have h2 : X.valᴴ * X⁻¹.valᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.inv_mul]
    simp
  calc
    X⁻¹.val * (X.val * Y * X.valᴴ) * X⁻¹.valᴴ =
        X⁻¹.val * X.val * Y * (X.valᴴ * X⁻¹.valᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = 1 * Y * 1 := by rw [h1, h2]
    _ = Y := by simp

/-- In a gauge-phase equivalence between normalized irreducible tensor blocks,
the scalar has modulus one.

This is the Perron-Frobenius normalization step used in the periodic overlap
argument.  Applying the gauge relation to a positive fixed point of the first
transfer map gives a positive eigenvector of the second transfer map with
eigenvalue ζ · conj(ζ); irreducibility and trace preservation force this
eigenvalue to be 1. -/
theorem gaugePhase_scalar_norm_eq_one_of_leftCanonical_irreducible
    [NeZero D] {A B : MPSTensor d D}
    (hA_left : IsLeftCanonical A) (hB_left : IsLeftCanonical B)
    (hB_irr : IsIrreducibleTensor B)
    {X : GL (Fin D) ℂ} {ζ : ℂ} (hζ_ne : ζ ≠ 0)
    (hB :
      ∀ i : Fin d,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 := by
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hA_left (NeZero.pos D)
  obtain ⟨τ, hτ_psd, hτ_ne, hτ_fix⟩ :=
    exists_posSemidef_fixedPoint B hB_left (NeZero.pos D)
  have hB_irrMap : IsIrreducibleMap (transferMap (d := d) (D := D) B) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor B hB_irr
  have hB_cp : IsCPMap (transferMap (d := d) (D := D) B) := transferMap_isCPMap B
  have hEB_eq : ∀ Y, transferMap (d := d) (D := D) B Y =
      (ζ * starRingEnd ℂ ζ) •
        (X.val * transferMap (d := d) (D := D) A
          (X⁻¹.val * Y * X⁻¹.valᴴ) * X.valᴴ) := by
    intro Y
    simp only [transferMap_apply]
    simp_rw [hB]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, ← Finset.smul_sum, Matrix.conjTranspose_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    congr 1
    exact mul_comm _ _
  let σ : Matrix (Fin D) (Fin D) ℂ := X.val * ρ * X.valᴴ
  have hσ_psd : σ.PosSemidef :=
    hρ_psd.mul_mul_conjTranspose_same X.val
  have hσ_ne : σ ≠ 0 := by
    intro hσ_zero
    apply hρ_ne
    have hcancel :=
      congr_arg (fun Y : Matrix (Fin D) (Fin D) ℂ => X⁻¹.val * Y * X⁻¹.valᴴ)
        hσ_zero
    simp only [σ, Matrix.mul_zero, Matrix.zero_mul] at hcancel
    rwa [gaugePhase_conj_cancel] at hcancel
  have hEB_σ :
      transferMap (d := d) (D := D) B σ =
        (ζ * starRingEnd ℂ ζ) • σ := by
    simp only [σ, hEB_eq, gaugePhase_conj_cancel, hρ_fix]
  have hζζ_real : ζ * starRingEnd ℂ ζ = (↑(‖ζ‖ ^ 2) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hζζ_pos : (0 : ℝ) < ‖ζ‖ ^ 2 := by
    have hnorm_ne : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ_ne
    exact sq_pos_of_ne_zero hnorm_ne
  have h_eig_eq : ‖ζ‖ ^ 2 = 1 :=
    (eigenvalue_unique_of_irreducible_cp
      (transferMap (d := d) (D := D) B) hB_cp hB_irrMap
      τ σ 1 (‖ζ‖ ^ 2) hτ_psd hτ_ne one_pos hσ_psd hσ_ne hζζ_pos
      (by simp [hτ_fix]) (by rw [hEB_σ, hζζ_real])).symm
  nlinarith [norm_nonneg ζ]

end MPSTensor
