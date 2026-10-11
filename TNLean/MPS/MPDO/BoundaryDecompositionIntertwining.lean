/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport

/-!
# Intertwiners between exact boundary coordinates

Exact biorthogonal reconstruction makes each analysis and synthesis map an
intertwiner. Cross products between two decompositions therefore intertwine
their target blocks. This is the Schur-separation step for the actual
multiplicity L matrices, before choosing any scalar coefficients.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:orthoV`,
  `rawrels`, and `1Fsymbol`.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι : Type*} [Fintype ι] {d DB : ℕ} {D : ι → ℕ}
  {B : MPSTensor d DB} {A : ∀ i, MPSTensor d (D i)}
  {V : ∀ i, Matrix (Fin (D i)) (Fin DB) ℂ}
  {W : ∀ i, Matrix (Fin DB) (Fin (D i)) ℂ}

/-- Each analysis matrix intertwines the incoming tensor with its target
block. Source: GLM23 `fusiontensors2` and `eq:orthoV`. -/
theorem analysis_mul_letter (h : IsBiorthogonalDecomposition B A V W)
    (i : ι) (a : Fin d) : V i * B a = A i a * V i := by
  classical
  rw [h.letter, Matrix.mul_sum, Finset.sum_eq_single i]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.retract, Matrix.one_mul]
  · intro j _ hji
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.orthogonal i j hji.symm,
      Matrix.zero_mul, Matrix.zero_mul]
  · simp

/-- Each synthesis matrix intertwines its target block with the incoming
tensor. Source: GLM23 `fusiontensors2` and `eq:orthoV`. -/
theorem letter_mul_synthesis (h : IsBiorthogonalDecomposition B A V W)
    (i : ι) (a : Fin d) : B a * W i = W i * A i a := by
  classical
  rw [h.letter, Matrix.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.mul_assoc, h.retract, Matrix.mul_one]
  · intro j _ hji
    rw [Matrix.mul_assoc, h.orthogonal j i hji, Matrix.mul_zero]
  · simp

/-- A cross product of analysis and synthesis from two exact decompositions
intertwines the corresponding target blocks. Source: GLM23 `1Fsymbol`. -/
theorem cross_intertwines
    {κ : Type*} [Fintype κ] {E : κ → ℕ} {C : ∀ j, MPSTensor d (E j)}
    {V' : ∀ j, Matrix (Fin (E j)) (Fin DB) ℂ}
    {W' : ∀ j, Matrix (Fin DB) (Fin (E j)) ℂ}
    (h : IsBiorthogonalDecomposition B A V W)
    (h' : IsBiorthogonalDecomposition B C V' W')
    (i : ι) (j : κ) (a : Fin d) :
    A i a * (V i * W' j) = (V i * W' j) * C j a := by
  calc
    _ = (A i a * V i) * W' j := (Matrix.mul_assoc _ _ _).symm
    _ = (V i * B a) * W' j := by rw [h.analysis_mul_letter]
    _ = V i * (B a * W' j) := Matrix.mul_assoc _ _ _
    _ = V i * (W' j * C j a) := by rw [h'.letter_mul_synthesis]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

/-- Reindexing the finite target copies changes no exact decomposition
identity. This permits grouping two-stage paths by their final block. -/
theorem reindex {κ : Type*} [Fintype κ]
    (h : IsBiorthogonalDecomposition B A V W) (e : κ ≃ ι) :
    IsBiorthogonalDecomposition B (fun j ↦ A (e j))
      (fun j ↦ V (e j)) (fun j ↦ W (e j)) where
  retract j := h.retract (e j)
  orthogonal i j hij := h.orthogonal (e i) (e j) (e.injective.ne hij)
  letter a := by
    rw [h.letter]
    exact (e.sum_comp (fun i ↦ W i * A i a * V i)).symm

end MPSTensor.IsBiorthogonalDecomposition
