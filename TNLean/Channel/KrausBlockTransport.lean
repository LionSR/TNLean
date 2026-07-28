/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP

/-!
# Block and coordinate transport for rectangular Kraus maps

This file records how rectangular Kraus maps act on dependent tensor blocks
and commute with simultaneous changes of input and output coordinates.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace Matrix

/-- A dependent block-diagonal rectangular Kraus family acts independently
on every common factor and leaves each spectator factor unchanged. -/
theorem rectangularKrausMap_blockDiagonal_kronecker_one
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {α β δ : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Fintype (δ i)]
    [∀ i, DecidableEq (δ i)]
    (L : κ → ∀ i, Matrix (β i) (α i) ℂ)
    (A : ∀ i, Matrix (α i) (α i) ℂ)
    (B : ∀ i, Matrix (δ i) (δ i) ℂ) :
    rectangularKrausMap
        (fun k ↦ Matrix.blockDiagonal' (fun i ↦
          L k i ⊗ₖ (1 : Matrix (δ i) (δ i) ℂ)))
        (Matrix.blockDiagonal' fun i ↦ A i ⊗ₖ B i) =
      Matrix.blockDiagonal' fun i ↦
        rectangularKrausMap (fun k ↦ L k i) (A i) ⊗ₖ B i := by
  classical
  change
    (∑ k, Matrix.blockDiagonal' (fun i ↦
          L k i ⊗ₖ (1 : Matrix (δ i) (δ i) ℂ)) *
        (Matrix.blockDiagonal' fun i ↦ A i ⊗ₖ B i) *
        (Matrix.blockDiagonal' (fun i ↦
          L k i ⊗ₖ (1 : Matrix (δ i) (δ i) ℂ)))ᴴ) =
      Matrix.blockDiagonal' fun i ↦
        (∑ k, L k i * A i * (L k i)ᴴ) ⊗ₖ B i
  have hterm (k : κ) :
      Matrix.blockDiagonal' (fun i ↦
          L k i ⊗ₖ (1 : Matrix (δ i) (δ i) ℂ)) *
          (Matrix.blockDiagonal' fun i ↦ A i ⊗ₖ B i) *
          (Matrix.blockDiagonal' (fun i ↦
            L k i ⊗ₖ (1 : Matrix (δ i) (δ i) ℂ)))ᴴ =
        Matrix.blockDiagonal' fun i ↦
          (L k i * A i * (L k i)ᴴ) ⊗ₖ B i := by
    rw [Matrix.blockDiagonal'_conjTranspose]
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  simp_rw [hterm]
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.blockDiagonal'_apply_eq]
    rcases x with ⟨xα, xδ⟩
    rcases y with ⟨yα, yδ⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply]
    rw [Finset.sum_mul]
  · simp only [Matrix.sum_apply]
    calc
      (∑ k, Matrix.blockDiagonal' (fun i ↦
          (L k i * A i * (L k i)ᴴ) ⊗ₖ B i) ⟨i, x⟩ ⟨j, y⟩) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        exact Matrix.blockDiagonal'_apply_ne _ _ _ hij
      _ = Matrix.blockDiagonal' (fun i ↦
          (∑ k, L k i * A i * (L k i)ᴴ) ⊗ₖ B i)
            ⟨i, x⟩ ⟨j, y⟩ :=
        (Matrix.blockDiagonal'_apply_ne _ _ _ hij).symm

/-- Simultaneously relabeling the input and output coordinates commutes with
a rectangular Kraus map. -/
theorem rectangularKrausMap_reindex
    {κ α α' β β' : Type*} [Fintype κ] [Fintype α]
    [Fintype α']
    (eα : α ≃ α') (eβ : β ≃ β')
    (K : κ → Matrix β α ℂ) (X : Matrix α α ℂ) :
    rectangularKrausMap
        (fun k ↦ Matrix.reindex eβ eα (K k))
        (Matrix.reindex eα eα X) =
      Matrix.reindex eβ eβ (rectangularKrausMap K X) := by
  change
    (∑ k, Matrix.reindex eβ eα (K k) *
        Matrix.reindex eα eα X *
        (Matrix.reindex eβ eα (K k))ᴴ) =
      Matrix.reindex eβ eβ (∑ k, K k * X * (K k)ᴴ)
  have hreindexSum :
      Matrix.reindex eβ eβ (∑ k, K k * X * (K k)ᴴ) =
        ∑ k, Matrix.reindex eβ eβ (K k * X * (K k)ᴴ) := by
    ext b b'
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.sum_apply]
  rw [hreindexSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.conjTranspose_reindex]
  calc
    Matrix.reindex eβ eα (K k) *
          Matrix.reindex eα eα X *
          Matrix.reindex eα eβ (K k)ᴴ =
      Matrix.reindex eβ eα (K k * X) *
          Matrix.reindex eα eβ (K k)ᴴ := by
        rw [show Matrix.reindex eβ eα (K k) *
              Matrix.reindex eα eα X =
            Matrix.reindex eβ eα (K k * X) by
          exact Matrix.reindexLinearEquiv_mul ℂ ℂ eβ eα eα _ _]
    _ = Matrix.reindex eβ eβ (K k * X * (K k)ᴴ) := by
      exact Matrix.reindexLinearEquiv_mul ℂ ℂ eβ eα eβ _ _

end Matrix
