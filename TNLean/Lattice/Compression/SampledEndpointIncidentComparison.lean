/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.IncidentSampledEndpointRepresentation
import TNLean.Lattice.Compression.WordEvalComparison

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

/-- A source-free word representing arbitrary original endpoint maps is
compared with another word through their common selected register data.
The comparison is formed before the sampled maps are supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
private theorem isEvalComparison_restrict_of_endpoint_data {R : Type}
    {c d : Layout R} (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2))
    (W : Word w.allResidualSourceLayout w.allResidualSourceLayout) (hs : W.sources = [])
    (V : Word c d)
    (hword : W = SourceInventory.endpointWord (partialSlots (fun _ ↦ true) w)
      w.allSourceU w.allSourceV
      (fun i ↦ M (partialSlotEquiv (fun _ ↦ true) w i).1)
      (fun i ↦ N (partialSlotEquiv (fun _ ↦ true) w i).1))
    (hincident :
      let all : P → Bool := fun _ ↦ true
      let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
      let A : P → Bool := fun t ↦ partySelector qp (affectedOwner all t)
      let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
        (by classical exact decide_eq_true rfl)
      let q : Option {t : P // A t = true} := some ⟨p, hp⟩
      let D := (partialPositions A w).flatMap (endpointDataAt A w M N)
      HEq V.eval
        (SourceInventory.endpointRegisterWord
          (D.filter (fun z ↦ partySelector q z.1.owner))).eval) :
    Word.IsEvalComparison
      (W.restrict (partySelector (some ⟨p, rfl⟩)) hs) V := by
  subst W
  exact (restrict_endpointWord_eval_heq_selectedRegisterWord w p M N).trans hincident.symm

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
  exact isEvalComparison_restrict_of_endpoint_data w p
    (sampledEndpointOperatorLeft w k lam E ξ ζ j ω)
    (sampledEndpointOperatorRight w k lam F ξ ζ j ω)
    (sampledEndpointWord w k lam E F ξ ζ j ω)
    (sources_sampledEndpointWord w k lam E F ξ ζ j ω)
    (incidentSampledEndpointWord w k lam E F p
      (originalGateLabelsAtOfAllChoices w p ξ)
      (originalGateLabelsAtOfAllChoices w p ζ)
      (fun i ↦ j (partialSlotEquiv
        (fun t ↦ partySelector (some ⟨p, rfl⟩)
          (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω)
    (sampledEndpointWord_eq_endpointWord w k lam E F ξ ζ j ω)
    (incidentSampledEndpointWord_eval_heq_selectedRegisterWord w k lam E F p ξ ζ j ω)

end SourceCircuit
end TNLean.PEPS.PairEffect
