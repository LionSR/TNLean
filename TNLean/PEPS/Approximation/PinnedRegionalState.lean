/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareGridSource
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Regional coordinates of the physical-first source presentation

Adapted definitions from PEPSFilters/Basic.lean at openai/math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. These retain the source's finite-set
complement and Gram-matrix formula. They are compared with the native partial
trace in `RegionalStates`; the canonical entropy definition is not duplicated.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.Pinned

/-- Adapted from `PinnedEntropy.RegionConfiguration`, Basic.lean lines 32–33. -/
abbrev RegionConfiguration {L : ℕ} (q : ℕ) (S : Finset (Vertex L)) :=
  {v : Vertex L // v ∈ S} → Fin q

/-- Adapted from `PinnedEntropy.joinConfigurations`, with its original complement convention. -/
def joinConfigurations {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) : Vertex L → Fin q := by
  classical
  exact fun v => if h : v ∈ A then x ⟨v, h⟩ else z ⟨v, Finset.mem_compl.mpr h⟩

/-- Adapted from `PinnedEntropy.coefficientMatrix`. -/
def coefficientMatrix {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q Aᶜ) ℂ :=
  fun x z => Ω (joinConfigurations A x z)

/-- Adapted from `PinnedEntropy.reducedDensity`: the unnormalized regional Gram matrix. -/
def reducedDensity {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ :=
  coefficientMatrix Ω A * (coefficientMatrix Ω A).conjTranspose

end TNLean.PEPS.Approximation.Pinned
