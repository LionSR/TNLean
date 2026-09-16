/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# Explicit gauges for multi-block compression data

The multi-block asymmetric compression data of
`MPSTensor.MultiBlockCompression` carries its change of bond coordinates as a linear
equivalence onto a graded coordinate space. For a worked example the change of coordinates is
a concrete invertible matrix together with a concrete labelling of the coordinates by blocks.
This file packages that presentation: a bijection of the graded coordinate space with the bond
index set, and a pair of mutually inverse square matrices, assemble into a gauge whose
conjugation is the matrix conjugation followed by the relabelling.

The worked examples have integer entries throughout, so this file also records the entrywise
coercion of an integer matrix into the complex matrices and its compatibility with products.
That coercion is what reduces every verification of a worked example to a decidable identity
between integer matrices.

## Main definitions

* `MPSTensor.complexOfInt`: the entrywise coercion of an integer matrix.
* `MPSTensor.gaugeOfMatrix`: the gauge attached to a bijective labelling and an invertible
  matrix.

## Main results

* `MPSTensor.conjMatrix_gaugeOfMatrix`: conjugation by such a gauge is matrix conjugation
  followed by the relabelling.
* `MPSTensor.MultiBlockCompression.left_gaugeOfMatrix`,
  `MPSTensor.MultiBlockCompression.right_gaugeOfMatrix`: the compression pair of a slot reads
  off the rows of the matrix and the columns of its inverse at the coordinates of that slot.
-/

open scoped Matrix

namespace MPSTensor

/-! ### Entrywise coercion of integer matrices -/

/-- The entrywise coercion of an integer matrix into the complex matrices. -/
def complexOfInt {m n : Type*} (X : Matrix m n ℤ) : Matrix m n ℂ :=
  X.map (Int.cast)

@[simp] theorem complexOfInt_apply {m n : Type*} (X : Matrix m n ℤ) (i : m) (j : n) :
    complexOfInt X i j = (X i j : ℂ) := rfl

theorem complexOfInt_mul {m n o : Type*} [Fintype n] (X : Matrix m n ℤ) (Y : Matrix n o ℤ) :
    complexOfInt (X * Y) = complexOfInt X * complexOfInt Y := by
  ext i j
  simp only [complexOfInt_apply, Matrix.mul_apply]
  push_cast
  rfl

theorem complexOfInt_one {n : Type*} [DecidableEq n] :
    complexOfInt (1 : Matrix n n ℤ) = 1 := by
  ext i j
  simp only [complexOfInt_apply, Matrix.one_apply]
  split <;> simp

theorem complexOfInt_neg {m n : Type*} (X : Matrix m n ℤ) :
    complexOfInt (-X) = -complexOfInt X := by
  ext i j
  simp only [complexOfInt_apply, Matrix.neg_apply, Int.cast_neg]

theorem complexOfInt_injective {m n : Type*} :
    Function.Injective (complexOfInt (m := m) (n := n)) := by
  intro X Y h
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa only [complexOfInt_apply, Int.cast_inj] using hij

/-! ### The gauge attached to an invertible matrix -/

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {D : ι → ℕ} {S : Finset ι} {z : ℕ}

variable (τ : BlockSpace D S z ≃ Fin DB) (G Ginv : Matrix (Fin DB) (Fin DB) ℂ)

/-- The change of bond coordinates given by an invertible matrix `G` with inverse `Ginv`,
followed by the labelling of the bond coordinates by the graded coordinate space along the
bijection `τ`. -/
noncomputable def gaugeOfMatrix (hG : G * Ginv = 1) (hG' : Ginv * G = 1) :
    (Fin DB → ℂ) ≃ₗ[ℂ] (BlockSpace D S z → ℂ) where
  toFun v b := (G *ᵥ v) (τ b)
  map_add' u v := by funext b; simp [Matrix.mulVec_add]
  map_smul' c v := by funext b; simp [Matrix.mulVec_smul]
  invFun u := Ginv *ᵥ fun x => u (τ.symm x)
  left_inv v := by
    have hcomp : (fun x => (G *ᵥ v) (τ (τ.symm x))) = G *ᵥ v := by
      funext x
      exact congrArg (G *ᵥ v) (τ.apply_symm_apply x)
    simp only [hcomp, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
  right_inv u := by
    funext b
    change (G *ᵥ (Ginv *ᵥ fun x => u (τ.symm x))) (τ b) = u b
    rw [Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
    exact congrArg u (τ.symm_apply_apply b)

variable (hG : G * Ginv = 1) (hG' : Ginv * G = 1)

omit [DecidableEq ι] in
theorem gaugeMatrix_gaugeOfMatrix :
    gaugeMatrix (gaugeOfMatrix τ G Ginv hG hG') = G.submatrix τ id := by
  ext b x
  simp [gaugeMatrix, LinearMap.toMatrix'_apply, gaugeOfMatrix, Matrix.mulVec_single]

theorem gaugeMatrixInv_gaugeOfMatrix :
    gaugeMatrixInv (gaugeOfMatrix τ G Ginv hG hG') = Ginv.submatrix id τ := by
  ext x b
  have hsingle : (fun y => (Pi.single b (1 : ℂ) : BlockSpace D S z → ℂ) (τ.symm y)) =
      Pi.single (τ b) (1 : ℂ) := by
    funext y
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  simp [gaugeMatrixInv, LinearMap.toMatrix'_apply, gaugeOfMatrix, hsingle,
    Matrix.mulVec_single]

/-- Conjugation by an explicit gauge is matrix conjugation followed by the relabelling. -/
theorem conjMatrix_gaugeOfMatrix (A : Matrix (Fin DB) (Fin DB) ℂ) :
    conjMatrix (gaugeOfMatrix τ G Ginv hG hG') A = (G * A * Ginv).submatrix τ τ := by
  rw [conjMatrix_eq_gaugeMatrix_mul, gaugeMatrix_gaugeOfMatrix, gaugeMatrixInv_gaugeOfMatrix]
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
  exact Finset.sum_comm

namespace MultiBlockCompression

variable {B : MPSTensor d DB} {C : ∀ s, MPSTensor d (D s)}

/-- The compression out of the bond space onto a slot reads off the rows of the gauge matrix at
the coordinates of that slot. -/
theorem left_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (s : {s // s ∈ S}) :
    P.left s = G.submatrix (fun i => τ ⟨Sum.inl s, i⟩) id := by
  ext i y
  rw [left, hgauge, gaugeMatrix_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨Sum.inl s, i⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockProj, Matrix.blockEmbed]
  · intro x _ hx
    rw [Matrix.blockProj, Matrix.transpose_apply, Matrix.blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨Sum.inl s, i⟩ : BlockSpace D S P.z)) h

/-- The compression into the bond space from a slot reads off the columns of the inverse gauge
matrix at the coordinates of that slot. -/
theorem right_gaugeOfMatrix (P : MultiBlockCompression B S C)
    {τ : BlockSpace D S P.z ≃ Fin DB} {G Ginv : Matrix (Fin DB) (Fin DB) ℂ}
    {hG : G * Ginv = 1} {hG' : Ginv * G = 1}
    (hgauge : P.gauge = gaugeOfMatrix τ G Ginv hG hG') (s : {s // s ∈ S}) :
    P.right s = Ginv.submatrix id fun j => τ ⟨Sum.inl s, j⟩ := by
  ext x j
  rw [right, hgauge, gaugeMatrixInv_gaugeOfMatrix, Matrix.mul_apply,
    Finset.sum_eq_single (⟨Sum.inl s, j⟩ : BlockSpace D S P.z)]
  · simp [Matrix.blockEmbed]
  · intro y _ hy
    rw [Matrix.blockEmbed_apply_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (⟨Sum.inl s, j⟩ : BlockSpace D S P.z)) h

end MultiBlockCompression

end MPSTensor
