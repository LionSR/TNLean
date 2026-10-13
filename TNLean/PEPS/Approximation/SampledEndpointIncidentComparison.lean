/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentSampledEndpointRepresentation

/-!
# Restricted sampled endpoint words and incident data

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
namespace SourceCircuit
variable {P : Type} {a b : Layout P}

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- Restricting the sampled endpoint operators gives the word constructed
from the incident labels. The input-layout identification is compared
separately, so this proof concerns only original endpoint operators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
theorem restrict_sampledEndpointWord_eval_heq_incidentSampledEndpointWord
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    HEq ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict
        (partySelector (some ⟨p, rfl⟩))
        (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).eval
      (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω).eval := by
  classical
  let all : P → Bool := fun _ ↦ true
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let A : P → Bool := fun t ↦ partySelector qp (affectedOwner all t)
  let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
    (decide_eq_true rfl)
  let q : Option {t : P // A t = true} := some ⟨p, hp⟩
  let M := sampledEndpointOperatorLeft w k lam E ξ ζ j ω
  let N := sampledEndpointOperatorRight w k lam F ξ ζ j ω
  let Ua := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).1)
  let Va := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).2)
  let Za := SourceInventory.endpointWord (partialSlots all w) Ua Va
    (fun i ↦ M (partialSlotEquiv all w i).1)
    (fun i ↦ N (partialSlotEquiv all w i).1)
  have hsa : Za.sources = [] := SourceInventory.sources_endpointWord ..
  let Ds := (partialPositions A w).flatMap (endpointDataAt A w M N)
  let Ds' := Ds.filter (fun z ↦ partySelector q z.1.owner)
  have hselected : HEq (Za.restrict (partySelector qp) hsa).eval
      (SourceInventory.endpointRegisterWord Ds').eval :=
    restrict_endpointWord_eval_heq_selectedRegisterWord w p M N
  have hword : sampledEndpointWord w k lam E F ξ ζ j ω = Za :=
    sampledEndpointWord_eq_endpointWord w k lam E F ξ ζ j ω
  have hinput :
      ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict
        (partySelector qp) (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).eval =
      (Za.restrict (partySelector qp) hsa).eval := by
    have h : (⟨sampledEndpointWord w k lam E F ξ ζ j ω,
          sources_sampledEndpointWord w k lam E F ξ ζ j ω⟩ :
          {Z : Word w.allResidualSourceLayout w.allResidualSourceLayout // Z.sources = []}) =
        ⟨Za, hsa⟩ := Subtype.ext hword
    exact congrArg
      (fun z : {Z : Word w.allResidualSourceLayout w.allResidualSourceLayout // Z.sources = []} ↦
        (z.1.restrict (partySelector qp) z.2).eval) h
  have hincident := incidentSampledEndpointWord_eval_heq_selectedRegisterWord
    w k lam E F p ξ ζ j ω
  exact ((heq_of_eq hinput).trans hselected).trans hincident.symm


end SourceCircuit
end TNLean.PEPS.PairEffect
