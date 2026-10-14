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

/-- The common selected endpoint operator is formed from arbitrary original
endpoint maps. Owner selection preserves the original source and register order.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
private def selectedEndpointOperator (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let D := (partialPositions A w).flatMap (endpointDataAt A w M N)
    let L := (D.filter (fun z ↦ partySelector q z.1.owner)).map Sigma.fst
    Mem L →L[ℂ] Mem L :=
  let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
    (affectedOwner (fun _ : P ↦ true) t)
  let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
    (by classical exact decide_eq_true rfl)
  let q : Option {t : P // A t = true} := some ⟨p, hp⟩
  let D := (partialPositions A w).flatMap (endpointDataAt A w M N)
  (SourceInventory.endpointRegisterWord
    (D.filter (fun z ↦ partySelector q z.1.owner))).eval

/-- The canonical original endpoint word has the common selected operator.
Selection is compared before an arbitrary representing word is supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–434. -/
private theorem restrict_endpointWord_eval_heq_selectedEndpointOperator
    (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) :
    let all : P → Bool := fun _ ↦ true
    let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
    let Z := SourceInventory.endpointWord (partialSlots all w) w.allSourceU w.allSourceV
      (fun i ↦ M (partialSlotEquiv all w i).1)
      (fun i ↦ N (partialSlotEquiv all w i).1)
    let hz : Z.sources = [] := SourceInventory.sources_endpointWord ..
    HEq (Z.restrict (partySelector qp) hz).eval
      (selectedEndpointOperator w p M N) :=
  restrict_endpointWord_eval_heq_selectedRegisterWord w p M N

/-- An arbitrary source-free word representing the original endpoint maps
has their common selected operator after restriction. The equality transports
its own source-free proof before any sampled maps are supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–434. -/
private theorem restrict_eval_heq_selectedEndpointOperator
    (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2))
    (W : Word w.allResidualSourceLayout w.allResidualSourceLayout) (hs : W.sources = [])
    (hword : W = SourceInventory.endpointWord (partialSlots (fun _ ↦ true) w)
      w.allSourceU w.allSourceV
      (fun i ↦ M (partialSlotEquiv (fun _ ↦ true) w i).1)
      (fun i ↦ N (partialSlotEquiv (fun _ ↦ true) w i).1)) :
    HEq (W.restrict (partySelector (some ⟨p, rfl⟩)) hs).eval
      (selectedEndpointOperator w p M N) := by
  subst W
  exact restrict_endpointWord_eval_heq_selectedEndpointOperator w p M N

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The actual restricted endpoint comparison, stated before the sampled
operators and the common incident register list are specialized in its proof.
The two original branch choices and the source samples are unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588. -/
private def sampledEndpointIncidentComparison
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) : Prop :=
    HEq ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict
        (partySelector (some ⟨p, rfl⟩))
        (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).eval
      (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω).eval

/-- The sampled endpoint word restricts to the common selected operator of
its original endpoint maps. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–434. -/
private theorem restrict_sampledEndpointWord_eval_heq_selectedEndpointOperator
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    HEq ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict
        (partySelector (some ⟨p, rfl⟩))
        (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).eval
      (selectedEndpointOperator w p
        (sampledEndpointOperatorLeft w k lam E ξ ζ j ω)
        (sampledEndpointOperatorRight w k lam F ξ ζ j ω)) :=
  restrict_eval_heq_selectedEndpointOperator w p
    (sampledEndpointOperatorLeft w k lam E ξ ζ j ω)
    (sampledEndpointOperatorRight w k lam F ξ ζ j ω)
    (sampledEndpointWord w k lam E F ξ ζ j ω)
    (sources_sampledEndpointWord w k lam E F ξ ζ j ω)
    (sampledEndpointWord_eq_endpointWord w k lam E F ξ ζ j ω)

/-- The incident sampled word has the same common selected endpoint operator.
Its local labels and samples are those extracted from the original choices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
private theorem incidentSampledEndpointWord_eval_heq_selectedEndpointOperator
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    HEq (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω).eval
      (selectedEndpointOperator w p
        (sampledEndpointOperatorLeft w k lam E ξ ζ j ω)
        (sampledEndpointOperatorRight w k lam F ξ ζ j ω)) :=
  incidentSampledEndpointWord_eval_heq_selectedRegisterWord w k lam E F p ξ ζ j ω

/-- The two sampled words are compared through their independently identified
common selected endpoint operator. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588. -/
private theorem sampledEndpointIncidentComparison_of_original_labels
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    sampledEndpointIncidentComparison w k lam E F p ξ ζ j ω :=
  (restrict_sampledEndpointWord_eval_heq_selectedEndpointOperator
    w k lam E F p ξ ζ j ω).trans
    (incidentSampledEndpointWord_eval_heq_selectedEndpointOperator
      w k lam E F p ξ ζ j ω).symm

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
  exact sampledEndpointIncidentComparison_of_original_labels w k lam E F p ξ ζ j ω

end SourceCircuit
end TNLean.PEPS.PairEffect
