/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledEndpointInputWord
import TNLean.PEPS.Approximation.EndpointWordRestrictionCongruence

/-! # Local dependence of the actual endpoint samples

Fix independent ket and bra choices. Restriction to selected owners uses only
the sample indices and Gaussian arrays at sources with a selected endpoint.
Changing the remaining sample data leaves the restricted operator unchanged.
The same sample and ordered ket–bra array are used at both endpoints of each
source throughout this comparison.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The actual sampled source-input operator restricted to selected owners
depends only on the samples at incident source occurrences. The ket and bra
choices are fixed independently, and no unused sample or branch label is chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and
565–588, pointwise locality of the sampled endpoint factors. -/
theorem restrict_sampledEndpointInputWord_eval_eq_of_incident_samples
    (w : SourceCircuit a b) (k : ℕ)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (L : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (R : ∀ e : sourceLocations w, branchLabels w e.1 →
      Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
    (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j j' : w.sourceLocations → Fin k) (ω ω' : SourceGaussianSamples w k)
    (f : Option {_p : P // true = true} → Bool)
    (h : ∀ i : Fin (partialSlots (fun _ : P ↦ true) w).length,
      f ((partialSlots (fun _ : P ↦ true) w).get i).left = true ∨
        f ((partialSlots (fun _ : P ↦ true) w).get i).right = true →
      j (allSourceSlotEquiv w i) = j' (allSourceSlotEquiv w i) ∧
        ω (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i) =
          ω' (partialSlotEquiv (fun _ : P ↦ true) w i).1
            (partialSlotChoice (fun _ : P ↦ true) w ξ i,
              partialSlotChoice (fun _ : P ↦ true) w ζ i)) :
    ((sampledEndpointInputWord w k lam L R ξ ζ j ω).restrict f
      (sources_sampledEndpointInputWord w k lam L R ξ ζ j ω)).eval =
      ((sampledEndpointInputWord w k lam L R ξ ζ j' ω').restrict f
        (sources_sampledEndpointInputWord w k lam L R ξ ζ j' ω')).eval := by
  classical
  have hWord :
      ((sampledEndpointWord w k lam L R ξ ζ j ω).restrict f
        (sources_sampledEndpointWord w k lam L R ξ ζ j ω)).eval =
        ((sampledEndpointWord w k lam L R ξ ζ j' ω').restrict f
          (sources_sampledEndpointWord w k lam L R ξ ζ j' ω')).eval := by
    dsimp only [sampledEndpointWord, SourceInventory.endpointMatrixWord]
    refine SourceInventory.restrict_endpointWord_eval_eq_of_local_eq f
      (partialSlots (fun _ : P ↦ true) w) w.allSourceU w.allSourceV _ _ _ _ ?_ ?_
    · intro i hi
      obtain ⟨hj, hω⟩ := h i (Or.inl hi)
      simp only [sampledEndpointLeft, hj, hω]
    · intro i hi
      obtain ⟨hj, hω⟩ := h i (Or.inr hi)
      simp only [sampledEndpointRight, hj, hω]
  unfold sampledEndpointInputWord
  rw [Word.restrict_castLayouts, Word.restrict_castLayouts]
  simp only [Word.eval_castLayouts, hWord]

end TNLean.PEPS.PairEffect.SourceCircuit
