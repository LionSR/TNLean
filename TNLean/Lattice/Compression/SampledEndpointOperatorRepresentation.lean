/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSampledEndpointInputWord
import TNLean.Lattice.Compression.SelectedPartialSourceSlots

/-!
# Original sampled endpoint operators and their ordered word

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean
open TNLean.Lattice.PartyCircuit TNLean.PEPS.PairEffect
namespace Lattice.PartyCircuit.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- Read the original branch label at an original source occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
def allSourceLabel (w : SourceCircuit a b) (ξ : Choices (fun _ ↦ true) w)
    (e : sourceLocations w) : branchLabels w e.1 :=
  choiceAt (fun _ ↦ true) w ξ e.1
    (isTouched_of_source_endpoint (fun _ ↦ true) w e (Or.inl rfl))

/-- Projection of all-party choices retains the label of every surviving source.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem projectedSlotChoice_eq_allSourceLabel (A : P → Bool)
    (w : SourceCircuit a b) (ξ : Choices (fun _ ↦ true) w)
    (i : Fin (partialSlots A w).length) :
    partialSlotChoice A w (projectAllChoices A w ξ) i =
      allSourceLabel w ξ (partialSlotEquiv A w i).1 :=
  choiceAt_projectAllChoices A w ξ (partialSlotEquiv A w i).1.1
    (isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1
      (partialSlotEquiv A w i).2)

/-- The complete slot enumeration reads the same original gate label.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem allPartialSlotChoice_eq_allSourceLabel
    (w : SourceCircuit a b) (ξ : Choices (fun _ ↦ true) w)
    (i : Fin (partialSlots (fun _ ↦ true) w).length) :
    partialSlotChoice (fun _ ↦ true) w ξ i =
      allSourceLabel w ξ (partialSlotEquiv (fun _ ↦ true) w i).1 := rfl

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The left endpoint operator uses the original ket and bra labels, source
index, sample, and Gaussian array.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309. -/
def sampledEndpointOperatorLeft (ξ ζ : Choices (fun _ ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k)
    (e : sourceLocations w) :
    euc (Fin (sourceDims w e).1) →L[ℂ] euc (Fin (sourceDims w e).1) :=
  basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ)
    (sampledEndpointLeft w k lam E e
      (allSourceLabel w ξ e, allSourceLabel w ζ e) (j e) ω)

/-- The right endpoint operator retains the same original source sample as
its left endpoint.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309. -/
def sampledEndpointOperatorRight (ξ ζ : Choices (fun _ ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k)
    (e : sourceLocations w) :
    euc (Fin (sourceDims w e).2) →L[ℂ] euc (Fin (sourceDims w e).2) :=
  basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)
    (sampledEndpointRight w k lam F e
      (allSourceLabel w ξ e, allSourceLabel w ζ e) (j e) ω)

/-- Express the sampled word using its endpoint operators before restricting
or identifying layouts. The complete slot enumeration retains the original
source indices and both original branch labels.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem sampledEndpointWord_eq_endpointWord
    (ξ ζ : Choices (fun _ ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) :
    sampledEndpointWord w k lam E F ξ ζ j ω =
      SourceInventory.endpointWord (partialSlots (fun _ ↦ true) w)
        w.allSourceU w.allSourceV
        (fun i ↦ sampledEndpointOperatorLeft w k lam E ξ ζ j ω
          (partialSlotEquiv (fun _ ↦ true) w i).1)
        (fun i ↦ sampledEndpointOperatorRight w k lam F ξ ζ j ω
          (partialSlotEquiv (fun _ ↦ true) w i).1) := by
  simp only [sampledEndpointWord, SourceInventory.endpointMatrixWord,
    allSourceSlotEquiv_apply, allPartialSlotChoice_eq_allSourceLabel,
    sampledEndpointOperatorLeft, sampledEndpointOperatorRight, allSourceU, allSourceV]


end Lattice.PartyCircuit.SourceCircuit
end TNLean
