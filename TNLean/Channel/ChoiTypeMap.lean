/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.Algebra.MatrixAux

/-!
# Choi-type positive maps

This file records the Choi-type maps appearing in Wolf Chapter 3, Example 3.1,
equation (3.20).  The map is written on the cyclic index set `ZMod d`, which is
the natural home for the shift matrices \(U_{k0}\):
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger}),
\]
where `D` projects a matrix to its diagonal part.

The main theorem in this file is the exact action on rank-one projectors.  This
is the algebraic reduction needed for the later positivity proof of Wolf
Example 3.1.  Positivity and indecomposability of the Choi-type maps are not
proved here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.20)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder InnerProductSpace
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## Basic cyclic and diagonal operations -/

/-- The cyclic shift matrix \(U_{k0}\) from Wolf, equation (2.24), sending
\(\ket r\) to \(\ket{k+r}\). -/
def choiTypeShift (k : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight (-k)).permMatrix ℂ

/-- The diagonal projection \(D(X)\), which keeps the diagonal entries and
sets all off-diagonal entries to zero. -/
def diagonalProjection (d : ℕ) :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ where
  toFun X := diagonal fun i => X i i
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [h]

omit [NeZero d] in
@[simp]
theorem diagonalProjection_apply (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d X = diagonal fun i => X i i :=
  rfl

/-! ## Rank-one diagonal positivity criterion -/

section DiagonalRankOne

variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

/-- If the squared norm of a vector is at most one, then `I - |v><v|` is
positive semidefinite. -/
theorem one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one (v : ι → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 ≤ 1) :
    ((1 : Matrix ι ι ℂ) - vecMulVec v (star v)).PosSemidef := by
  classical
  set V : EuclideanSpace ℂ ι := WithLp.toLp 2 v with hV
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact isHermitian_one.sub (Matrix.posSemidef_vecMulVec_self_star v).1
  · intro w
    set W : EuclideanSpace ℂ ι := WithLp.toLp 2 w with hW
    have hQ :
        star w ⬝ᵥ (((1 : Matrix ι ι ℂ) - vecMulVec v (star v)) *ᵥ w) =
          star w ⬝ᵥ w - (star v ⬝ᵥ w) * (star w ⬝ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
        star_dotProduct_vecMulVec_mulVec]
    rw [hQ]
    have hVW : star v ⬝ᵥ w = ⟪V, W⟫_ℂ := by
      rw [hV, hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm w (star v)).symm
    have hWV : star w ⬝ᵥ v = ⟪W, V⟫_ℂ := by
      rw [hV, hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm v (star w)).symm
    have hWW : star w ⬝ᵥ w = ⟪W, W⟫_ℂ := by
      rw [hW, EuclideanSpace.inner_toLp_toLp]
      exact (dotProduct_comm w (star w)).symm
    rw [hVW, hWV, hWW]
    have hVVnorm : ‖V‖ ^ 2 ≤ 1 := by
      rw [hV, EuclideanSpace.norm_sq_eq]
      simpa using hv
    have hinner_le : ‖⟪V, W⟫_ℂ‖ ^ 2 ≤ ‖W‖ ^ 2 := by
      have hCS := norm_inner_le_norm (𝕜 := ℂ) V W
      have hsq : ‖⟪V, W⟫_ℂ‖ ^ 2 ≤ (‖V‖ * ‖W‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hCS 2
      have hWnonneg : 0 ≤ ‖W‖ ^ 2 := by positivity
      nlinarith [hVVnorm, hsq, norm_nonneg V, norm_nonneg W]
    have hWWreal : ⟪W, W⟫_ℂ = ((‖W‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) W]
      norm_cast
    have hprod : ⟪V, W⟫_ℂ * ⟪W, V⟫_ℂ = ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm W V, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hWWreal, hprod]
    rw [show ((‖W‖ ^ 2 : ℝ) : ℂ) - ((‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
        ((‖W‖ ^ 2 - ‖⟪V, W⟫_ℂ‖ ^ 2 : ℝ) : ℂ) by norm_num]
    rw [Complex.zero_le_real]
    linarith

/-- Weighted Schur-complement form of the rank-one diagonal criterion.

The hypothesis `hvzero` is the usual support condition at zero diagonal
entries: if the diagonal weight vanishes, the corresponding component of the
rank-one vector must vanish. -/
theorem diagonal_sub_vecMulVec_posSemidef_of_sum_normSq_div_le_one
    (a : ι → ℝ) (v : ι → ℂ) (ha : ∀ i, 0 ≤ a i)
    (hvzero : ∀ i, a i = 0 → v i = 0)
    (hbound : ∑ i, ‖v i‖ ^ 2 / a i ≤ 1) :
    (diagonal (fun i => (a i : ℂ)) - vecMulVec v (star v)).PosSemidef := by
  classical
  let s : ι → ℝ := fun i => Real.sqrt (a i)
  let p : ι → ℂ := fun i => if a i = 0 then 0 else v i / (s i : ℂ)
  let D : Matrix ι ι ℂ := diagonal fun i => (s i : ℂ)
  have hs_nonneg : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hp_norm : ∑ i, ‖p i‖ ^ 2 ≤ 1 := by
    have hterm : ∀ i, ‖p i‖ ^ 2 = ‖v i‖ ^ 2 / a i := by
      intro i
      by_cases hi : a i = 0
      · simp [p, hi, hvzero i hi]
      · have hai_pos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
        have hsi_pos : 0 < s i := by simpa [s] using Real.sqrt_pos.2 hai_pos
        have hsi_ne : (s i : ℂ) ≠ 0 := by exact_mod_cast hsi_pos.ne'
        rw [show p i = v i / (s i : ℂ) by simp [p, hi]]
        rw [norm_div]
        rw [show (‖v i‖ / ‖(s i : ℂ)‖) ^ 2 =
            ‖v i‖ ^ 2 / ‖(s i : ℂ)‖ ^ 2 by ring]
        rw [← Complex.normSq_eq_norm_sq ((s i : ℂ)), Complex.normSq_ofReal]
        rw [show s i * s i = a i by
          rw [← pow_two]
          simpa [s] using Real.sq_sqrt (ha i)]
    simpa [hterm] using hbound
  have hp_psd : ((1 : Matrix ι ι ℂ) - vecMulVec p (star p)).PosSemidef :=
    one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one p hp_norm
  have hD_mulVec (x : ι → ℂ) : D *ᵥ x = fun i => (s i : ℂ) * x i := by
    ext i
    simp [D, Matrix.mulVec]
  have hD_conj : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, hij, eq_comm]
  have hDp : D *ᵥ p = v := by
    rw [hD_mulVec]
    ext i
    by_cases hi : a i = 0
    · simp [p, hi, hvzero i hi]
    · have hai_pos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hsi_pos : 0 < s i := by simpa [s] using Real.sqrt_pos.2 hai_pos
      have hsi_ne : (s i : ℂ) ≠ 0 := by exact_mod_cast hsi_pos.ne'
      simp [p, hi]
      field_simp [hsi_ne]
  have hpD : star p ᵥ* Dᴴ = star v := by
    rw [hD_conj]
    ext i
    rw [Matrix.vecMul_diagonal]
    by_cases hi : a i = 0
    · simp [p, hi, hvzero i hi]
    · have hai_pos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
      have hsi_pos : 0 < s i := by simpa [s] using Real.sqrt_pos.2 hai_pos
      have hsi_ne : (s i : ℂ) ≠ 0 := by exact_mod_cast hsi_pos.ne'
      simp [p, hi, div_eq_mul_inv]
      field_simp [hsi_ne]
  have hDone : D * (1 : Matrix ι ι ℂ) * Dᴴ = diagonal (fun i => (a i : ℂ)) := by
    rw [hD_conj, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]
      exact_mod_cast (by
        rw [← pow_two]
        simpa [s] using Real.sq_sqrt (ha i))
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  have hdrank : D * vecMulVec p (star p) * Dᴴ = vecMulVec v (star v) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hDp, hpD]
  have hfactor :
      D * ((1 : Matrix ι ι ℂ) - vecMulVec p (star p)) * Dᴴ =
        diagonal (fun i => (a i : ℂ)) - vecMulVec v (star v) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hDone, hdrank]
  rw [← hfactor]
  exact hp_psd.mul_mul_conjTranspose_same D

end DiagonalRankOne

/-- Conjugation by a matrix, as the linear map \(X\mapsto AXA^\dagger\).

Wolf's Choi-type maps use this operation in the terms
\(U_{k0}XU_{k0}^{\dagger}\).  As a map on matrices it is completely positive;
that fact is not used in this file. -/
def conjugationLinearMap {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := A * X * Aᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp]
theorem conjugationLinearMap_apply {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (X : Matrix n n ℂ) :
    conjugationLinearMap A X = A * X * Aᴴ :=
  rfl

/-- The diagonal part of a cyclically conjugated matrix is the shifted diagonal. -/
theorem diagonalProjection_conj_choiTypeShift
    (k : ZMod d) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d (choiTypeShift k * X * (choiTypeShift k)ᴴ) =
      diagonal fun i => X (i - k) (i - k) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagonalProjection, choiTypeShift, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, Matrix.mul_apply, sub_eq_add_neg]
  · simp [diagonalProjection, h]

/-! ## The Choi-type map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.20).**  The Choi-type map
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger})
\]
on matrices indexed by the cyclic group `ZMod d`.  The coefficient `d - n` is
the scalar difference appearing in the source; the positivity theorem uses the
range `1 ≤ n ≤ d - 2`. -/
def choiTypeMap (d n : ℕ) [NeZero d] :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ :=
  ((d : ℂ) - (n : ℂ)) • diagonalProjection d - LinearMap.id +
    ∑ k : Fin n,
      (diagonalProjection d).comp
        (conjugationLinearMap (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d)))

@[simp]
theorem choiTypeMap_apply (n : ℕ) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    choiTypeMap d n X =
      ((d : ℂ) - (n : ℂ)) • diagonalProjection d X - X +
        ∑ k : Fin n,
          diagonalProjection d
            (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d) * X *
              (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d))ᴴ) := by
  simp [choiTypeMap]

/-- The Choi-type map applied to a rank-one projector is a diagonal matrix minus
that projector.  This is the rank-one reduction underlying Wolf's positivity
argument for equation (3.20). -/
theorem choiTypeMap_vecMulVec
    (n : ℕ) (v : ZMod d → ℂ) :
    choiTypeMap d n (vecMulVec v (star v)) =
      diagonal (fun i =>
        ((d : ℂ) - (n : ℂ)) * (v i * star (v i)) +
          ∑ k : Fin n,
            v (i - ((k.1 + 1 : ℕ) : ZMod d)) *
              star (v (i - ((k.1 + 1 : ℕ) : ZMod d)))) -
        vecMulVec v (star v) := by
  rw [choiTypeMap_apply]
  simp_rw [diagonalProjection_conj_choiTypeShift]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    ring_nf
  · simp [Matrix.sum_apply, vecMulVec_apply, h, smul_eq_mul]

/-- The real diagonal weight appearing in the rank-one Choi-type image. -/
noncomputable def choiTypeRankOneWeight (d n : ℕ) [NeZero d] (v : ZMod d → ℂ)
    (i : ZMod d) : ℝ :=
  ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
    ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2

/-- Rank-one positivity of the Choi-type map reduced to the cyclic reciprocal
bound for the diagonal weights.

In the range \(n \le d-2\), the remaining scalar task is to prove the displayed
bound for all vectors `v`. -/
theorem choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one
    (n : ℕ) (v : ZMod d → ℂ) (hn₂ : n ≤ d - 2)
    (hbound : ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d n v i ≤ 1) :
    (choiTypeMap d n (vecMulVec v (star v))).PosSemidef := by
  classical
  let a : ZMod d → ℝ := fun i => choiTypeRankOneWeight d n v i
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hnlt : n < d := by omega
  have hnle : n ≤ d := le_of_lt hnlt
  have hdn_nonneg : 0 ≤ (d : ℝ) - (n : ℝ) := by
    have hnleR : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hnle
    linarith
  have hdn_pos : 0 < (d : ℝ) - (n : ℝ) := by
    have hnltR : (n : ℝ) < (d : ℝ) := by exact_mod_cast hnlt
    linarith
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a, choiTypeRankOneWeight]
    exact add_nonneg (mul_nonneg hdn_nonneg (sq_nonneg _))
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hvzero : ∀ i, a i = 0 → v i = 0 := by
    intro i hi
    have hfirst_nonneg : 0 ≤ ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 :=
      mul_nonneg hdn_nonneg (sq_nonneg _)
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hsum_eq :
        ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
            ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 = 0 := by
      simpa [a, choiTypeRankOneWeight] using hi
    have hfirst_zero : ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 = 0 := by
      nlinarith
    have hnormsq_zero : ‖v i‖ ^ 2 = 0 := by
      nlinarith [hfirst_zero, hdn_pos, sq_nonneg (‖v i‖)]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq_zero)
  have hdiag :
      (diagonal (fun i => (a i : ℂ)) - vecMulVec v (star v)).PosSemidef :=
    diagonal_sub_vecMulVec_posSemidef_of_sum_normSq_div_le_one a v ha hvzero
      (by simpa [a] using hbound)
  rw [choiTypeMap_vecMulVec]
  convert hdiag using 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [a, choiTypeRankOneWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [hij]

end Matrix
