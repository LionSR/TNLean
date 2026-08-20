/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Virtual-boundary decomposition for finite block sums

This file gives the arbitrary-boundary form of the elementary direct-sum
identity for matrix-product tensors. A block-diagonal word evaluation pairs
only with the diagonal blocks of the virtual boundary. It also records the
corresponding covariance under an invertible virtual gauge.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1646--1665 and 1810--1825.
-/

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The diagonal block of a matrix written on a flattened finite dependent
direct sum. -/
def finSigmaDiagonalBlock
    (X : Matrix (Fin (∑ j : Fin r, dim j)) (Fin (∑ j : Fin r, dim j)) ℂ)
    (j : Fin r) : Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
  (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X).submatrix
    (fun a ↦ ⟨j, a⟩) (fun a ↦ ⟨j, a⟩)

end Matrix

namespace MPSTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- Heterogeneously equal tensors have equal closed word evaluations after
transporting the virtual boundary across the equality of bond dimensions. -/
theorem trace_evalWord_mul_cast_of_heq
    {D₁ D₂ : ℕ} (hD : D₁ = D₂)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (hA : A ≍ B)
    (w : List (Fin d)) (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Matrix.trace (evalWord A w * X) =
      Matrix.trace (evalWord B w *
        cast (congrArg (fun n ↦ Matrix (Fin n) (Fin n) ℂ) hD) X) := by
  cases hD
  rw [eq_of_heq hA]
  have hX : cast
      (congrArg (fun n ↦ Matrix (Fin n) (Fin n) ℂ) (Eq.refl D₁)) X = X :=
    cast_eq_iff_heq.mpr HEq.rfl
  rw [hX]

/-- An arbitrary virtual boundary paired with a finite block-diagonal tensor
depends only on its diagonal blocks.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1665 and 1810--1825. -/
theorem trace_evalWord_toTensorFromBlocks_mul
    (weight : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (w : List (Fin d))
    (X : Matrix (Fin (∑ j : Fin r, dim j)) (Fin (∑ j : Fin r, dim j)) ℂ) :
    Matrix.trace (evalWord (toTensorFromBlocks weight A) w * X) =
      ∑ j : Fin r, Matrix.trace
        ((weight j) ^ w.length • evalWord (A j) w *
          Matrix.finSigmaDiagonalBlock X j) := by
  classical
  let e : ((j : Fin r) × Fin (dim j)) ≃ Fin (∑ j : Fin r, dim j) :=
    finSigmaFinEquiv
  let Xσ : Matrix ((j : Fin r) × Fin (dim j))
      ((j : Fin r) × Fin (dim j)) ℂ :=
    Matrix.reindex e.symm e.symm X
  have hX : X = Matrix.reindex e e Xσ := by
    ext a b
    simp [Xσ, e]
  rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal weight A w, hX]
  have hmul :
      Matrix.reindex e e
          (Matrix.blockDiagonal' fun j : Fin r ↦
            weight j ^ w.length • evalWord (A j) w) *
          Matrix.reindex e e Xσ =
        Matrix.reindex e e
          (Matrix.blockDiagonal' (fun j : Fin r ↦
              weight j ^ w.length • evalWord (A j) w) * Xσ) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ e e e _ _
  rw [show finSigmaFinEquiv = e from rfl, hmul, Matrix.trace_reindex]
  rw [Matrix.trace_blockDiagonal'_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext a b
  simp [Matrix.finSigmaDiagonalBlock, Xσ, e]

/-- Moving an invertible virtual gauge from a tensor word to its boundary.

Source: arXiv:1606.00608, bicanonical-form gauge convention at lines
1666--1674 and Appendix C.2, lines 1646--1665. -/
theorem trace_evalWord_gauge_mul
    {A B : MPSTensor d D} (G : GL (Fin D) ℂ)
    (hG : ∀ i, B i =
      (G : Matrix (Fin D) (Fin D) ℂ) * A i *
        (↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ))
    (w : List (Fin d)) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (evalWord B w * X) =
      Matrix.trace (evalWord A w *
        ((↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ) * X *
          (G : Matrix (Fin D) (Fin D) ℂ))) := by
  rw [evalWord_gauge G hG]
  calc
    Matrix.trace (((G : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          (↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ)) * X) =
        Matrix.trace (((G : Matrix (Fin D) (Fin D) ℂ) * evalWord A w) *
          ((↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ) * X)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        (((↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ) * X) *
          ((G : Matrix (Fin D) (Fin D) ℂ) * evalWord A w)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((((↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ) * X) *
          (G : Matrix (Fin D) (Fin D) ℂ)) * evalWord A w) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        (evalWord A w * (((↑(G⁻¹) : Matrix (Fin D) (Fin D) ℂ) * X) *
          (G : Matrix (Fin D) (Fin D) ℂ))) := Matrix.trace_mul_comm _ _

/-- An arbitrary virtual boundary of a gauge-transformed finite block sum is
the sum of the component closures with the diagonal blocks of the transformed
boundary.

The same transformed boundary is used at every word length. This is the
arbitrary-boundary identity required when the one-site and two-site channel
equations are combined over canonical sectors.

Source: arXiv:1606.00608, bicanonical-form gauge convention at lines
1666--1674 and Appendix C.2, lines 1646--1665 and 1810--1825. -/
theorem trace_evalWord_gauge_toTensorFromBlocks_mul
    (weight : Fin r → ℂ) (A : (j : Fin r) → MPSTensor d (dim j))
    (B : MPSTensor d (∑ j : Fin r, dim j))
    (G : GL (Fin (∑ j : Fin r, dim j)) ℂ)
    (hG : ∀ i, B i =
      (G : Matrix (Fin (∑ j : Fin r, dim j))
        (Fin (∑ j : Fin r, dim j)) ℂ) *
        toTensorFromBlocks weight A i *
        (↑(G⁻¹) : Matrix (Fin (∑ j : Fin r, dim j))
          (Fin (∑ j : Fin r, dim j)) ℂ))
    (w : List (Fin d))
    (X : Matrix (Fin (∑ j : Fin r, dim j))
      (Fin (∑ j : Fin r, dim j)) ℂ) :
    Matrix.trace (evalWord B w * X) =
      ∑ j : Fin r, Matrix.trace
        ((weight j) ^ w.length • evalWord (A j) w *
          Matrix.finSigmaDiagonalBlock
            ((↑(G⁻¹) : Matrix (Fin (∑ j : Fin r, dim j))
                (Fin (∑ j : Fin r, dim j)) ℂ) * X *
              (G : Matrix (Fin (∑ j : Fin r, dim j))
                (Fin (∑ j : Fin r, dim j)) ℂ)) j) := by
  rw [trace_evalWord_gauge_mul G hG]
  exact trace_evalWord_toTensorFromBlocks_mul weight A w _

end MPSTensor
