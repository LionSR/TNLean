/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt
import QICLean.Probability.ComplexGaussian.SchmidtSource

/-!
# Schmidt coordinates determined by original gate labels

The normalized vector at each original source occurrence determines probability
weights and two isometric Schmidt frames. These choices are made for every local
gate label before an affected set or a partial expansion is chosen.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and 342–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-random-source.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct ComplexConjugate Matrix
open QICLean.ComplexGaussian
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Standard orthonormal coordinates of the source vector at an original occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–289. -/
def sourceCoordinates {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) (ξ : branchLabels w e.1) :
    EuclideanSpace ℂ (Fin (sourceDims w e).1 × Fin (sourceDims w e).2) :=
  ((EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)).repr (sourceVectorAt w e ξ)

/-- The actual source coordinates have unit Euclidean norm.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–290. -/
theorem sourceCoordinates_norm {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) (ξ : branchLabels w e.1) :
    ‖sourceCoordinates w e ξ‖ = 1 := by
  rw [sourceCoordinates, LinearIsometryEquiv.norm_map, sourceVectorAt_norm]

/-- Choose Schmidt probability weights and endpoint frames separately for each
original source occurrence and local gate label. The same choices represent every
partial source vector and its mixed ket–bra source matrix, for every affected set.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and 342–417. -/
theorem exists_local_schmidt_source_frames {a b : Layout P} (w : SourceCircuit a b) :
    ∃ lam : ∀ e : sourceLocations w, branchLabels w e.1 →
        Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ,
      ∃ E : ∀ e : sourceLocations w, branchLabels w e.1 →
          Matrix (Fin (sourceDims w e).1)
            (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ,
        ∃ F : ∀ e : sourceLocations w, branchLabels w e.1 →
            Matrix (Fin (sourceDims w e).2)
              (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ,
          (∀ e ξ, (∀ j, 0 ≤ lam e ξ j) ∧ ∑ j, lam e ξ j = 1 ∧
            (E e ξ)ᴴ * E e ξ = 1 ∧ (F e ξ)ᴴ * F e ξ = 1 ∧
            ambientSchmidtVector (lam e ξ) (E e ξ) (F e ξ) =
              (sourceCoordinates w e ξ).ofLp) ∧
          ∀ (A : P → Bool) (ξ ζ : Choices A w) (i : Fin (partialSlots A w).length),
            let e := (partialSlotEquiv A w i).1
            let ξ₀ := partialSlotChoice A w ξ i
            let ζ₀ := partialSlotChoice A w ζ i
            let b := (EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ).tensorProduct
              (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)
            ambientSchmidtVector (lam e ξ₀) (E e ξ₀) (F e ξ₀) =
                (b.repr (partialSlotVector A w ξ i)).ofLp ∧
              ambientSchmidtSource (lam e ξ₀) (lam e ζ₀)
                  (E e ξ₀) (F e ξ₀) (E e ζ₀) (F e ζ₀) =
                Matrix.vecMulVec (b.repr (partialSlotVector A w ξ i)).ofLp
                  (fun p ↦ conj ((b.repr (partialSlotVector A w ζ i)).ofLp p)) := by
  classical
  have hex (e : sourceLocations w) (ξ : branchLabels w e.1) :
      ∃ (lam : Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
        (E : Matrix (Fin (sourceDims w e).1)
          (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
        (F : Matrix (Fin (sourceDims w e).2)
          (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ),
        (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ Eᴴ * E = 1 ∧ Fᴴ * F = 1 ∧
          ambientSchmidtVector lam E F = (sourceCoordinates w e ξ).ofLp := by
    have h := exists_probability_schmidtSourceFrames (sourceCoordinates w e ξ)
      (sourceCoordinates_norm w e ξ)
    rw [Fintype.card_fin, Fintype.card_fin] at h
    exact h
  choose lam E F hnonneg hmass hE hF hrepr using hex
  refine ⟨lam, E, F, ?_, ?_⟩
  · intro e ξ
    exact ⟨hnonneg e ξ, hmass e ξ, hE e ξ, hF e ξ, hrepr e ξ⟩
  · intro A ξ ζ i
    constructor
    · exact hrepr _ _
    · dsimp only
      rw [ambientSchmidtSource, hrepr, hrepr]
      rfl

end TNLean.PEPS.PairEffect.SourceCircuit
