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

/-- Equal source-free words on fixed layouts have the same restricted
operator. If their restriction and another operator both agree with a common
operator, compose these comparisons before specializing the word and maps.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
private theorem restrict_eval_heq_of_eq_and_common_eval {Q : Type}
    {ℓ ℓ' : Layout Q} (f : Q → Bool) (u v : Word ℓ ℓ')
    (hu : u.sources = []) (hv : v.sources = []) (hword : u = v)
    {E F G H : HSpace} {X : E →L[ℂ] F} {Y : G →L[ℂ] H}
    (hselected : HEq (v.restrict f hv).eval X) (hincident : HEq Y X) :
    HEq (u.restrict f hu).eval Y := by
  have h : (⟨u, hu⟩ : {z : Word ℓ ℓ' // z.sources = []}) = ⟨v, hv⟩ :=
    Subtype.ext hword
  have hrestriction := congrArg
    (fun z : {z : Word ℓ ℓ' // z.sources = []} ↦ (z.1.restrict f z.2).eval) h
  exact ((heq_of_eq hrestriction).trans hselected).trans hincident.symm

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

/-- The canonical comparison follows from equal source-free words and the
common selected endpoint operator. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588. -/
private theorem sampledEndpointIncidentComparison_of_original_labels
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    sampledEndpointIncidentComparison w k lam E F p ξ ζ j ω := by
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
  have hincident := incidentSampledEndpointWord_eval_heq_selectedRegisterWord
    w k lam E F p ξ ζ j ω
  exact restrict_eval_heq_of_eq_and_common_eval (partySelector qp)
    (sampledEndpointWord w k lam E F ξ ζ j ω) Za
    (sources_sampledEndpointWord w k lam E F ξ ζ j ω) hsa hword hselected hincident

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
