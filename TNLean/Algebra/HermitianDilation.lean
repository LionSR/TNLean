/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Hermitian dilation and its variance bound

The Hermitian dilation of a rectangular complex matrix has the same operator norm,
and that norm is a positive spectral value of the dilation. The squared dilation
has the two Gram matrices as its diagonal blocks. For finite uniform averages,
positive-semidefinite block domination bounds its variance norm by the maximum of
the two Gram-matrix variance norms.

These are the dilation identities used in Tropp, *User-friendly tail bounds for
sums of random matrices*, equations (2.12)--(2.13) and Remark 3.11:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

private theorem posSemidef_fromBlocks_diag
    {m n : Type*} [Finite m] [Finite n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A 0 0 B).PosSemidef := by
  classical
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite n
  let S := fromBlocks (hA.isHermitian.cfc Real.sqrt) 0 0 (hB.isHermitian.cfc Real.sqrt)
  have hsq : Sᴴ * S = fromBlocks A 0 0 B := by
    dsimp [S]
    rw [fromBlocks_conjTranspose, hA.cfc_sqrt_isHermitian.eq,
      hB.cfc_sqrt_isHermitian.eq]
    simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add,
      hA.cfc_sqrt_mul_self, hB.cfc_sqrt_mul_self]
  rw [← hsq]
  exact posSemidef_conjTranspose_mul_self S

private theorem fromBlocks_diag_mono
    {m n : Type*} [Finite m] [Finite n]
    {A C : Matrix m m ℂ} {B D : Matrix n n ℂ} (hAC : A ≤ C) (hBD : B ≤ D) :
    fromBlocks A 0 0 B ≤ fromBlocks C 0 0 D := by
  classical
  have heq : fromBlocks C 0 0 D - fromBlocks A 0 0 B =
      fromBlocks (C - A) 0 0 (D - B) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  rw [← sub_nonneg, heq]
  exact Matrix.nonneg_iff_posSemidef.mpr
    (posSemidef_fromBlocks_diag (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAC))
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hBD)))

/-- The self-adjoint dilation of a rectangular matrix; Tropp, equation (2.12). -/
def hermitianDilation {m n : Type*} (Y : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks 0 Y Yᴴ 0

/-- The dilation is Hermitian by its off-diagonal adjoint blocks; Tropp, equation (2.12). -/
theorem isHermitian_hermitianDilation {m n : Type*} (Y : Matrix m n ℂ) :
    (hermitianDilation Y).IsHermitian :=
  IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero

/-- The squared dilation has the two Gram matrices as diagonal blocks; Tropp, equation (2.13). -/
theorem hermitianDilation_sq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (Y : Matrix m n ℂ) :
    hermitianDilation Y ^ 2 = fromBlocks (Y * Yᴴ) 0 0 (Yᴴ * Y) := by
  simp only [hermitianDilation, pow_two, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero]

private theorem norm_hermitianDilation_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (Y : Matrix m n ℂ) : ‖hermitianDilation Y‖ ≤ ‖Y‖ := by
  have hYY : Y * Yᴴ ≤ ‖Y‖ ^ 2 • (1 : Matrix m m ℂ) := by
    have hp := posSemidef_self_mul_conjTranspose Y
    have hn : ‖Y * Yᴴ‖ ≤ ‖Y‖ ^ 2 := by
      have hh := l2_opNorm_conjTranspose_mul_self Yᴴ
      simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using hh.le
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖Y‖) hp.nonneg).mp hn
  have hYY' : Yᴴ * Y ≤ ‖Y‖ ^ 2 • (1 : Matrix n n ℂ) := by
    simpa [Algebra.algebraMap_eq_smul_one, l2_opNorm_conjTranspose_mul_self, pow_two] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (Yᴴ * Y) (sq_nonneg ‖Y‖)
        (posSemidef_conjTranspose_mul_self Y).nonneg).mp (by
          rw [l2_opNorm_conjTranspose_mul_self, pow_two])
  have hD : hermitianDilation Y ^ 2 ≤ ‖Y‖ ^ 2 • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
    rw [hermitianDilation_sq]
    convert fromBlocks_diag_mono hYY hYY' using 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hnorm : ‖hermitianDilation Y‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    have hp : (hermitianDilation Y ^ 2).PosSemidef := by
      simpa only [(isHermitian_hermitianDilation Y).eq, pow_two] using
        posSemidef_conjTranspose_mul_self (hermitianDilation Y)
    have hh := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖Y‖) hp.nonneg).mpr
      (by simpa [Algebra.algebraMap_eq_smul_one] using hD)
    have hsq : ‖hermitianDilation Y ^ 2‖ = ‖hermitianDilation Y‖ ^ 2 := by
      simpa only [(isHermitian_hermitianDilation Y).eq, pow_two] using
        l2_opNorm_conjTranspose_mul_self (hermitianDilation Y)
    rwa [hsq] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm

end Matrix

namespace Matrix

private theorem norm_fromRows_one_zero {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [Nonempty m] :
    ‖fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ)‖ = 1 := by
  have heq : (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))ᴴ *
      fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ) = 1 := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
    simp only [conjTranspose_one, conjTranspose_zero, Matrix.mul_zero, one_mul, add_zero]
  have h := l2_opNorm_conjTranspose_mul_self (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))
  rw [heq, norm_one] at h
  nlinarith [norm_nonneg (fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))]

private theorem norm_fromRows_zero_one {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n] :
    ‖fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ)‖ = 1 := by
  have heq : (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))ᴴ *
      fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ) = 1 := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
    simp only [conjTranspose_one, conjTranspose_zero, Matrix.mul_zero, one_mul, zero_add]
  have h := l2_opNorm_conjTranspose_mul_self (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))
  rw [heq, norm_one] at h
  nlinarith [norm_nonneg (fromRows (0 : Matrix m n ℂ) (1 : Matrix n n ℂ))]

private theorem norm_le_hermitianDilation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (Y : Matrix m n ℂ) : ‖Y‖ ≤ ‖hermitianDilation Y‖ := by
  let E : Matrix (m ⊕ n) m ℂ := fromRows 1 0
  let F : Matrix (m ⊕ n) n ℂ := fromRows 0 1
  have hE : ‖E‖ = 1 := norm_fromRows_one_zero
  have hF : ‖F‖ = 1 := norm_fromRows_zero_one
  have heq : Eᴴ * hermitianDilation Y * F = Y := by
    dsimp [E, F, hermitianDilation]
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows]
    simp only [conjTranspose_one, conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  calc
    ‖Y‖ = ‖Eᴴ * hermitianDilation Y * F‖ := congrArg norm heq.symm
    _ ≤ ‖Eᴴ * hermitianDilation Y‖ * ‖F‖ := l2_opNorm_mul _ _
    _ ≤ (‖Eᴴ‖ * ‖hermitianDilation Y‖) * ‖F‖ :=
      mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ = _ := by rw [l2_opNorm_conjTranspose, hE, hF, one_mul, mul_one]

end Matrix

namespace Matrix

/-- The dilation preserves the operator norm; Tropp, equation (2.12). -/
theorem norm_hermitianDilation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] (Y : Matrix m n ℂ) :
    ‖hermitianDilation Y‖ = ‖Y‖ :=
  le_antisymm (norm_hermitianDilation_le Y) (norm_le_hermitianDilation Y)

/-- The norm is a positive spectral endpoint of the Hermitian dilation.
This gives the one-sided reduction in Tropp, Remark 3.11, without a union of two tails. -/
theorem norm_mem_spectrum_hermitianDilation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] (Y : Matrix m n ℂ) :
    ‖Y‖ ∈ spectrum ℝ (hermitianDilation Y) := by
  let J : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 1 0 0 (-1)
  have hJ : J * J = 1 := by
    dsimp [J]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      neg_mul_neg, mul_one, fromBlocks_one]
  let u : (Matrix (m ⊕ n) (m ⊕ n) ℂ)ˣ := ⟨J, J, hJ, hJ⟩
  have hconj : J * hermitianDilation Y * J = -hermitianDilation Y := by
    dsimp [J, hermitianDilation]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, fromBlocks_neg, neg_zero]
  have hsymm : spectrum ℝ (-hermitianDilation Y) = spectrum ℝ (hermitianDilation Y) := by
    have h := spectrum.units_conjugate (R := ℝ) (a := hermitianDilation Y) (u := u)
    change spectrum ℝ (J * hermitianDilation Y * J) = spectrum ℝ (hermitianDilation Y) at h
    rwa [hconj] at h
  obtain hp | hn := CStarAlgebra.norm_or_neg_norm_mem_spectrum (hermitianDilation Y)
    (isHermitian_hermitianDilation Y).isSelfAdjoint
  · simpa only [norm_hermitianDilation] using hp
  · have hh : ‖hermitianDilation Y‖ ∈ spectrum ℝ (-hermitianDilation Y) := by
      rw [← spectrum.neg_eq]
      exact hn
    rw [hsymm, norm_hermitianDilation] at hh
    exact hh

end Matrix

namespace Matrix

/-- The Hermitian dilation preserves finite sums; Tropp, Remark 3.11. -/
theorem hermitianDilation_sum {ι m n : Type*} [Fintype ι] (Y : ι → Matrix m n ℂ) :
    hermitianDilation (∑ a, Y a) = ∑ a, hermitianDilation (Y a) := by
  ext i j
  cases i <;> cases j <;>
    simp [hermitianDilation, fromBlocks, conjTranspose_apply, Matrix.sum_apply]

/-- The Hermitian dilation is real-linear; Tropp, Remark 3.11. -/
theorem hermitianDilation_real_smul {m n : Type*} (Y : Matrix m n ℂ) (r : ℝ) :
    hermitianDilation (r • Y) = r • hermitianDilation Y := by
  ext i j
  cases i <;> cases j <;> simp [hermitianDilation, fromBlocks, conjTranspose_apply]

open Classical in
/-- The variance norm of a finite uniform dilation is bounded by the maximum of the
two Gram-matrix variance norms. This is the domination needed in Tropp, Theorem 1.6. -/
theorem norm_average_hermitianDilation_sq_le {α m n : Type*}
    [Fintype α] [Nonempty α] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    (Y : α → Matrix m n ℂ) :
    ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, hermitianDilation (Y a) ^ 2‖ ≤
      max ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Y a * (Y a)ᴴ‖
        ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, (Y a)ᴴ * Y a‖ := by
  classical
  let A : Matrix m m ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, Y a * (Y a)ᴴ
  let B : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, (Y a)ᴴ * Y a
  have hA : A.PosSemidef := (posSemidef_sum Finset.univ
    fun a _ ↦ posSemidef_self_mul_conjTranspose (Y a)).smul (by positivity :
      0 ≤ (Fintype.card α : ℝ)⁻¹)
  have hB : B.PosSemidef := (posSemidef_sum Finset.univ
    fun a _ ↦ posSemidef_conjTranspose_mul_self (Y a)).smul (by positivity :
      0 ≤ (Fintype.card α : ℝ)⁻¹)
  have hAc : A ≤ (max ‖A‖ ‖B‖) • (1 : Matrix m m ℂ) := by
    have h := hA.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
    have hh : A ≤ ‖A‖ • (1 : Matrix m m ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using h
    exact hh.trans (smul_le_smul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hBc : B ≤ (max ‖A‖ ‖B‖) • (1 : Matrix n n ℂ) := by
    have h := hB.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
    have hh : B ≤ ‖B‖ • (1 : Matrix n n ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using h
    exact hh.trans (smul_le_smul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hcap : fromBlocks A 0 0 B ≤ (max ‖A‖ ‖B‖) •
      (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
    convert fromBlocks_diag_mono hAc hBc using 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hp : (fromBlocks A 0 0 B).PosSemidef := posSemidef_fromBlocks_diag hA hB
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap _
    (le_trans (norm_nonneg A) (le_max_left _ _)) hp.nonneg).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hcap)
  have heq : (Fintype.card α : ℝ)⁻¹ • ∑ a, hermitianDilation (Y a) ^ 2 =
      fromBlocks A 0 0 B := by
    simp only [hermitianDilation_sq]
    ext i j
    cases i <;> cases j <;> simp [A, B, fromBlocks, Matrix.sum_apply]
  simpa only [heq] using hn

end Matrix
