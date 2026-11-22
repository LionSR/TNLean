/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Matrix

/-!
# Interpolation of two maximally entangled bonds

The diagonal matrix below is the coefficient matrix of the bond vector
`(1 - γ) ∑ᵢ |i,i⟩ + γ ∑ⱼ |j,j⟩` on two complementary direct-sum spaces.
The second sum runs over the *second block* of dimension `D₁`, correcting
the printed upper range in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:sym:omega-gamma`.

**Local fix (second-block range):** The printed upper limit `D₁` is read as
`D₀+D₁`; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

This module establishes the nonvanishing of the interpolating bond. The
commuting parent Hamiltonian and its uniform gap require separate arguments.
-/

open scoped Matrix

namespace MPSTensor

/-- The coefficient on a basis vector in either summand of the direct-sum
bond space. Schuch–Pérez-García–Cirac, arXiv:1010.3732, equation
`eq:sym:omega-gamma`, with the corrected second-block upper range. -/
def bondInterpolationWeight (D₀ D₁ : ℕ) (γ : ℝ)
    (i : Fin (D₀ + D₁)) : ℂ :=
  match finSumFinEquiv.symm i with
  | Sum.inl _ => ((1 - γ : ℝ) : ℂ)
  | Sum.inr _ => (γ : ℂ)

/-- The matrix of coefficients of the interpolating maximally entangled
bond in the standard basis. Schuch–Pérez-García–Cirac, arXiv:1010.3732,
equation `eq:sym:omega-gamma`. -/
def bondInterpolationMatrix (D₀ D₁ : ℕ) (γ : ℝ) :
    Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ :=
  Matrix.diagonal (bondInterpolationWeight D₀ D₁ γ)

@[simp]
theorem bondInterpolationWeight_left (D₀ D₁ : ℕ) (γ : ℝ)
    (i : Fin D₀) :
    bondInterpolationWeight D₀ D₁ γ (finSumFinEquiv (Sum.inl i)) =
      ((1 - γ : ℝ) : ℂ) := by
  simp [bondInterpolationWeight]

@[simp]
theorem bondInterpolationWeight_right (D₀ D₁ : ℕ) (γ : ℝ)
    (i : Fin D₁) :
    bondInterpolationWeight D₀ D₁ γ (finSumFinEquiv (Sum.inr i)) =
      (γ : ℂ) := by
  simp [bondInterpolationWeight]

/-- The bond coefficients vary continuously with the interpolation parameter.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
equation `eq:sym:omega-gamma`. -/
theorem continuous_bondInterpolationMatrix (D₀ D₁ : ℕ) :
    Continuous (bondInterpolationMatrix D₀ D₁) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · subst j
    simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq]
    unfold bondInterpolationWeight
    split <;> fun_prop
  · simpa [bondInterpolationMatrix, hij] using
      (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))

/-- At the first endpoint, the first block has unit diagonal
coefficients. -/
@[simp]
theorem bondInterpolationMatrix_zero_left (D₀ D₁ : ℕ) (i : Fin D₀) :
    bondInterpolationMatrix D₀ D₁ 0
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl i)) = 1 := by
  simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq]
  rw [bondInterpolationWeight_left]
  norm_num

/-- At the first endpoint, the second block vanishes. -/
@[simp]
theorem bondInterpolationMatrix_zero_right (D₀ D₁ : ℕ) (i : Fin D₁) :
    bondInterpolationMatrix D₀ D₁ 0
      (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr i)) = 0 := by
  simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq]
  rw [bondInterpolationWeight_right]
  norm_num

/-- At the second endpoint, the first block vanishes. -/
@[simp]
theorem bondInterpolationMatrix_one_left (D₀ D₁ : ℕ) (i : Fin D₀) :
    bondInterpolationMatrix D₀ D₁ 1
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl i)) = 0 := by
  simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq]
  rw [bondInterpolationWeight_left]
  norm_num

/-- At the second endpoint, the second block has unit diagonal
coefficients. -/
@[simp]
theorem bondInterpolationMatrix_one_right (D₀ D₁ : ℕ) (i : Fin D₁) :
    bondInterpolationMatrix D₀ D₁ 1
      (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr i)) = 1 := by
  simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq]
  rw [bondInterpolationWeight_right]
  norm_num

/-- With both endpoint bond spaces nonzero, every point of the real
interpolation has a nonzero bond coefficient. In particular, it holds for
`0 ≤ γ ≤ 1`, as used in the symmetric interpolation of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2. -/
theorem bondInterpolationMatrix_ne_zero {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    bondInterpolationMatrix D₀ D₁ γ ≠ 0 := by
  intro h
  let i₀ : Fin D₀ := ⟨0, h₀⟩
  let i₁ : Fin D₁ := ⟨0, h₁⟩
  have hleft := congrArg (fun M : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ =>
    M (finSumFinEquiv (Sum.inl i₀)) (finSumFinEquiv (Sum.inl i₀))) h
  have hright := congrArg (fun M : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ =>
    M (finSumFinEquiv (Sum.inr i₁)) (finSumFinEquiv (Sum.inr i₁))) h
  simp only [bondInterpolationMatrix, Matrix.diagonal_apply_eq] at hleft hright
  change bondInterpolationWeight D₀ D₁ γ
    (finSumFinEquiv (Sum.inl i₀)) = 0 at hleft
  change bondInterpolationWeight D₀ D₁ γ
    (finSumFinEquiv (Sum.inr i₁)) = 0 at hright
  rw [bondInterpolationWeight_left] at hleft
  rw [bondInterpolationWeight_right] at hright
  have hγ : γ = 0 := by exact_mod_cast hright
  simp [hγ] at hleft

/-- Squared Hilbert norm of the interpolating bond vector. The two blocks
are orthogonal, so their contributions have multiplicities `D₀` and `D₁`.
Schuch–Pérez-García–Cirac, arXiv:1010.3732, equation
`eq:sym:omega-gamma`. -/
def bondInterpolationSquaredNorm (D₀ D₁ : ℕ) (γ : ℝ) : ℝ :=
  (D₀ : ℝ) * (1 - γ) ^ 2 + (D₁ : ℝ) * γ ^ 2

/-- The stated squared norm is the sum of squared moduli of all entries
of the bond coefficient matrix. -/
theorem bondInterpolationMatrix_sum_normSq (D₀ D₁ : ℕ) (γ : ℝ) :
    (∑ i : Fin (D₀ + D₁), ∑ j : Fin (D₀ + D₁),
      Complex.normSq (bondInterpolationMatrix D₀ D₁ γ i j)) =
      bondInterpolationSquaredNorm D₀ D₁ γ := by
  classical
  calc
    _ = ∑ i : Fin (D₀ + D₁),
          Complex.normSq (bondInterpolationWeight D₀ D₁ γ i) := by
      simp_rw [bondInterpolationMatrix, Matrix.diagonal_apply,
        apply_ite Complex.normSq]
      simp
    _ = ∑ i : Fin D₀ ⊕ Fin D₁,
          Complex.normSq (bondInterpolationWeight D₀ D₁ γ
            (finSumFinEquiv i)) := by
      rw [← Equiv.sum_comp finSumFinEquiv]
    _ = bondInterpolationSquaredNorm D₀ D₁ γ := by
      simp only [Fintype.sum_sum_type, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, bondInterpolationWeight,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Complex.normSq_ofReal, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul, bondInterpolationSquaredNorm]
      ring

/-- The interpolating bond has strictly positive squared Hilbert norm
when both endpoint bond dimensions are positive. -/
theorem bondInterpolationSquaredNorm_pos {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    0 < bondInterpolationSquaredNorm D₀ D₁ γ := by
  have hD₀ : 0 < (D₀ : ℝ) := by exact_mod_cast h₀
  have hD₁ : 0 < (D₁ : ℝ) := by exact_mod_cast h₁
  by_cases hγ : γ = 0
  · simp [bondInterpolationSquaredNorm, hγ, hD₀]
  · have hγ2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
    have hleft : 0 ≤ (D₀ : ℝ) * (1 - γ) ^ 2 :=
      mul_nonneg (le_of_lt hD₀) (sq_nonneg _)
    exact add_pos_of_nonneg_of_pos hleft (mul_pos hD₁ hγ2)

/-- Coefficient matrix divided by the Hilbert norm of its bond vector.
For positive endpoint dimensions the denominator is strictly positive. -/
noncomputable def normalizedBondInterpolationMatrix
    (D₀ D₁ : ℕ) (γ : ℝ) :
    Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ :=
  ((Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ)⁻¹) •
    bondInterpolationMatrix D₀ D₁ γ

/-- The normalized bond is nonzero throughout the interpolation for
positive endpoint dimensions. -/
theorem normalizedBondInterpolationMatrix_ne_zero {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    normalizedBondInterpolationMatrix D₀ D₁ γ ≠ 0 := by
  have hs : Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (bondInterpolationSquaredNorm_pos h₀ h₁ γ))
  have hc : (Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ) ≠ 0 := by
    exact_mod_cast hs
  exact smul_ne_zero (inv_ne_zero hc) (bondInterpolationMatrix_ne_zero h₀ h₁ γ)

/-- The normalized coefficient matrix represents a unit bond vector in
the Hilbert tensor product: the sum of squared moduli of its coordinates is
one. -/
theorem normalizedBondInterpolationMatrix_sum_normSq {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) (γ : ℝ) :
    (∑ i : Fin (D₀ + D₁), ∑ j : Fin (D₀ + D₁),
      Complex.normSq (normalizedBondInterpolationMatrix D₀ D₁ γ i j)) = 1 := by
  let s := bondInterpolationSquaredNorm D₀ D₁ γ
  have hs : 0 < s := bondInterpolationSquaredNorm_pos h₀ h₁ γ
  have hfactor : Complex.normSq ((Real.sqrt s : ℂ)⁻¹) = s⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt (le_of_lt hs)]
  simp only [normalizedBondInterpolationMatrix, Matrix.smul_apply, smul_eq_mul,
    Complex.normSq_mul, ← Finset.mul_sum]
  rw [hfactor, bondInterpolationMatrix_sum_normSq]
  exact inv_mul_cancel₀ (ne_of_gt hs)

/-- At the first endpoint, the normalized bond has equal coefficients
only on the diagonal of the first summand. -/
theorem normalizedBondInterpolationMatrix_zero_apply
    (D₀ D₁ : ℕ) (i j : Fin (D₀ + D₁)) :
    normalizedBondInterpolationMatrix D₀ D₁ 0 i j =
      if i = j then
        match finSumFinEquiv.symm i with
        | Sum.inl _ => ((Real.sqrt (D₀ : ℝ) : ℂ)⁻¹)
        | Sum.inr _ => 0
      else 0 := by
  simp [normalizedBondInterpolationMatrix, bondInterpolationMatrix,
    bondInterpolationWeight, bondInterpolationSquaredNorm,
    Matrix.diagonal_apply]
  split_ifs
  · split <;> simp
  · rfl

/-- At the second endpoint, the normalized bond has equal coefficients
only on the diagonal of the second summand. -/
theorem normalizedBondInterpolationMatrix_one_apply
    (D₀ D₁ : ℕ) (i j : Fin (D₀ + D₁)) :
    normalizedBondInterpolationMatrix D₀ D₁ 1 i j =
      if i = j then
        match finSumFinEquiv.symm i with
        | Sum.inl _ => 0
        | Sum.inr _ => ((Real.sqrt (D₁ : ℝ) : ℂ)⁻¹)
      else 0 := by
  simp [normalizedBondInterpolationMatrix, bondInterpolationMatrix,
    bondInterpolationWeight, bondInterpolationSquaredNorm,
    Matrix.diagonal_apply]
  split_ifs
  · split <;> simp
  · rfl

/-- The normalized bond matrix varies continuously along the full real
interpolation when both endpoint dimensions are positive. -/
theorem continuous_normalizedBondInterpolationMatrix {D₀ D₁ : ℕ}
    (h₀ : 0 < D₀) (h₁ : 0 < D₁) :
    Continuous (normalizedBondInterpolationMatrix D₀ D₁) := by
  have hnorm : Continuous fun γ : ℝ =>
      (Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ) := by
    unfold bondInterpolationSquaredNorm
    fun_prop
  have hne : ∀ γ : ℝ,
      (Real.sqrt (bondInterpolationSquaredNorm D₀ D₁ γ) : ℂ) ≠ 0 := by
    intro γ
    exact_mod_cast (ne_of_gt
      (Real.sqrt_pos.2 (bondInterpolationSquaredNorm_pos h₀ h₁ γ)))
  exact (Continuous.inv₀ hnorm hne).smul
    (continuous_bondInterpolationMatrix D₀ D₁)

end MPSTensor
