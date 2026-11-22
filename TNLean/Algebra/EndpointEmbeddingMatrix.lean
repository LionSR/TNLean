/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The matrix of a coordinate inclusion

The matrix that includes the coordinates indexed by `β` into those indexed by `α` along an
embedding `β ↪ α` is an isometry, and its range consists of the vectors vanishing off the image.
Source: SCP10, arXiv:1001.3807, Section 7, the physical bond isometries, lines 3008–3019.
-/

open scoped Matrix BigOperators

namespace TNLean.PEPS

/-- Include a finite family of orthonormal endpoint coordinates into a larger coordinate space.
Source: SCP10, Section 7, the physical bond isometries, lines 3008–3019. -/
noncomputable def endpointEmbeddingMatrix {α β : Type*} [DecidableEq α]
    (e : β ↪ α) : Matrix α β ℂ := fun r c => if r = e c then 1 else 0

/-- An injective relabelling of endpoint coordinates defines an isometry.
Source: SCP10, Section 7, the physical bond isometries, lines 3008–3019. -/
theorem endpointEmbeddingMatrix_isIsometry {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β] (e : β ↪ α) :
    Matrix.IsIsometry (endpointEmbeddingMatrix e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix]
  rw [Finset.sum_eq_single (e i)]
  · simp [Matrix.one_apply, e.injective.eq_iff]
  · intro r _ hri
    simp [hri]
  · simp

/-- An endpoint inclusion recovers each original coordinate at its image. -/
theorem endpointEmbeddingMatrix_mulVec_image {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (x : β → ℂ) (i : β) :
    (endpointEmbeddingMatrix e *ᵥ x) (e i) = x i := by
  classical
  simp [Matrix.mulVec, dotProduct, endpointEmbeddingMatrix, e.injective.eq_iff]

/-- An endpoint inclusion vanishes outside the embedded coordinate set. -/
theorem endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (x : β → ℂ) (a : α)
    (ha : a ∉ Set.range e) : (endpointEmbeddingMatrix e *ᵥ x) a = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hne : a ≠ e b := fun h => ha ⟨b, h.symm⟩
  simp only [endpointEmbeddingMatrix, hne, ↓reduceIte, zero_mul]

/-- The range of a coordinate inclusion consists precisely of vectors
vanishing off the included coordinates. -/
theorem mem_range_endpointEmbeddingMatrix_iff {α β : Type*}
    [Fintype β] [DecidableEq α] (e : β ↪ α) (ψ : α → ℂ) :
    ψ ∈ (Matrix.mulVecLin (endpointEmbeddingMatrix e)).range ↔
      ∀ a, a ∉ Set.range e → ψ a = 0 := by
  constructor
  · rintro ⟨χ, rfl⟩ a ha
    exact endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range e χ a ha
  · intro hψ
    refine ⟨fun b => ψ (e b), ?_⟩
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := ha
      exact endpointEmbeddingMatrix_mulVec_image e _ b
    · exact (endpointEmbeddingMatrix_mulVec_eq_zero_of_notMem_range e _ a ha).trans
        (hψ a ha).symm

end TNLean.PEPS
