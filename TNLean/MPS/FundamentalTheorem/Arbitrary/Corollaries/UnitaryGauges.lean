/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.AdmissibleBlock
import TNLean.MPS.FundamentalTheorem.Arbitrary.CompletelyReducible

/-!
# Unitary gauges between left-canonical tensors

Let `A` be irreducible and left-canonical, `B` left-canonical, `ζ ≠ 0` and `X` invertible with
`B^i = ζ X A^i X⁻¹` for every letter. Then `|ζ| = 1` and `X = κ U` with `κ > 0` and `U` unitary.

The tensor `B` is gauge related to `ζ A`, hence irreducible. The Perron–Frobenius argument for the
adjoint transfer map, which has `X†X` and `1` as positive eigenvectors, is
`MPSTensor.exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible`; it gives `|ζ| = 1`
and a unitary `U` with `B^i = ζ U A^i U†`. Then `U† X` commutes with every `A^i`, so it is a
nonzero scalar `c` by Schur's lemma, and `X = |c| ((c / |c|) U)`.

## Main results

* `MPSTensor.norm_eq_one_and_exists_pos_mem_unitaryGroup_eq_smul_of_leftCanonical`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If `B^i = ζ X A^i X⁻¹` with `ζ ≠ 0` and `A` irreducible, then `B` is irreducible: it is gauge
related to `ζ A`, whose word module is simple. -/
private theorem isIrreducibleAction_of_eq_smul_conj [NeZero D] {A B : MPSTensor d D}
    (hA : Matrix.IsIrreducibleAction A) {ζ : ℂ} (hζ : ζ ≠ 0) (X : GL (Fin D) ℂ)
    (hX : ∀ i, B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    Matrix.IsIrreducibleAction B := by
  have hg : IsGaugeRelated B (ζ • A) := by
    refine ⟨X, ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), Units.mul_inv X,
      Units.inv_mul X, fun i => ?_⟩
    rw [hX i, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc ((X : Matrix (Fin D) (Fin D) ℂ) * A i), Units.inv_mul, Matrix.mul_one]
  have := (isIrreducibleAction_and_pos_iff_isSimpleModule (ζ • A)).1
    ⟨isIrreducibleAction_smul hA hζ, NeZero.pos D⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_wordModule_of_isGaugeRelated hg
  exact ((isIrreducibleAction_and_pos_iff_isSimpleModule B).2 (IsSimpleModule.congr e)).1

/-- **Unitary gauges.** Let `A` be irreducible and left-canonical, `B`
left-canonical, `ζ ≠ 0`, and `X` invertible with `B^i = ζ X A^i X⁻¹` for every letter. Then
`|ζ| = 1` and `X = κ U` with `κ > 0` and `U` unitary. -/
theorem norm_eq_one_and_exists_pos_mem_unitaryGroup_eq_smul_of_leftCanonical [NeZero D]
    {A B : MPSTensor d D} (hA : Matrix.IsIrreducibleAction A)
    (hAl : IsLeftCanonical A) (hBl : IsLeftCanonical B) {ζ : ℂ} (hζ : ζ ≠ 0)
    (X : GL (Fin D) ℂ)
    (hX : ∀ i, B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ U ∈ Matrix.unitaryGroup (Fin D) ℂ,
      (X : Matrix (Fin D) (Fin D) ℂ) = (κ : ℂ) • U := by
  have hB := isIrreducibleAction_of_eq_smul_conj hA hζ X hX
  obtain ⟨U, hζ1, hU⟩ := exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible X ζ
    hζ hX hAl hBl ((Kraus.isIrreducibleAction_iff_isIrreducibleFamily A).1 hA)
    ((Kraus.isIrreducibleAction_iff_isIrreducibleFamily B).1 hB)
  refine ⟨hζ1, ?_⟩
  have hUU : (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 U.2
  have hUU' : (U : Matrix (Fin D) (Fin D) ℂ) * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 U.2
  -- `X A^i X⁻¹ = U A^i U†`, cancelling `ζ`
  have hconj : ∀ i, (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
        (U : Matrix (Fin D) (Fin D) ℂ) * A i * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := fun i =>
    smul_right_injective _ hζ ((hX i).symm.trans (hU i))
  -- `U† X` commutes with every letter of `A`, hence is a scalar (Schur)
  have hcomm : ∀ i, (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X * A i =
      A i * ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X) := by
    intro i
    have hXA : (X : Matrix (Fin D) (Fin D) ℂ) * A i =
        (U : Matrix (Fin D) (Fin D) ℂ) * A i * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X := by
      rw [← hconj i, Matrix.mul_assoc ((X : Matrix (Fin D) (Fin D) ℂ) * A i), Units.inv_mul,
        Matrix.mul_one]
    rw [Matrix.mul_assoc, hXA]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_intertwines hA hcomm
  have hXc : (X : Matrix (Fin D) (Fin D) ℂ) = c • (U : Matrix (Fin D) (Fin D) ℂ) := by
    calc (X : Matrix (Fin D) (Fin D) ℂ)
        = U * ((U : Matrix (Fin D) (Fin D) ℂ)ᴴ * X) := by
          rw [← Matrix.mul_assoc, hUU', Matrix.one_mul]
      _ = c • (U : Matrix (Fin D) (Fin D) ℂ) := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have hc0 : c ≠ 0 := by
    intro hc0
    have h1 : (X : Matrix (Fin D) (Fin D) ℂ) *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := Units.mul_inv X
    rw [hXc, hc0, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  -- `X = |c| ((c / |c|) U)`, and `(c / |c|) U` is unitary
  have hκ : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hκ0 : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hs : ‖(‖c‖ : ℂ)⁻¹ * c‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hκ.le, inv_mul_cancel₀ hκ.ne']
  have hss : star ((‖c‖ : ℂ)⁻¹ * c) * ((‖c‖ : ℂ)⁻¹ * c) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hs]
    simp
  refine ⟨‖c‖, hκ, ((‖c‖ : ℂ)⁻¹ * c) • (U : Matrix (Fin D) (Fin D) ℂ), ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, hUU, smul_smul, hss, one_smul]
  · rw [smul_smul, mul_inv_cancel_left₀ hκ0, hXc]

end MPSTensor
