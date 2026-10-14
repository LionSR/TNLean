/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentSampledEndpointWord
import TNLean.PEPS.Approximation.SampledEndpointOperatorRepresentation
import TNLean.PEPS.Approximation.EndpointSelectedRegisterComparison
import TNLean.PEPS.Approximation.EndpointRegisterOwnerTransport

/-!
# Incident sampled endpoint data and original labels

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

/-- Equal ordered endpoint data give the same filtered word comparison. The
comparison is transported before the original labels and sampled maps are supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
private theorem eval_heq_filtered_endpointRegisterWord_of_eq
    {Q R : Type} {c d : Layout Q} (u : Word c d)
    (D D' : List (Sigma (fun r : Reg R ↦ r.space →L[ℂ] r.space)))
    (f : R → Bool) (hD : D = D')
    (h : HEq u.eval (SourceInventory.endpointRegisterWord
      (D.filter (fun z ↦ f z.1.owner))).eval) :
    HEq u.eval (SourceInventory.endpointRegisterWord
      (D'.filter (fun z ↦ f z.1.owner))).eval := by
  cases hD
  exact h

/-- Removing the canonical layout and owner identifications from the incident
word leaves its ordered filtered endpoint data. The original incident labels
and local samples are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
theorem incidentSampledEndpointWord_eval_heq_endpointRegisterWord
    (p : P) (η θ : OriginalGateLabelsAt w p)
    (j : Fin (partialSlots
      (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w).length → Fin k)
    (ω : SourceGaussianSamples w k) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let M := fun i : Fin R.length ↦
      basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w
        (partialSlotEquiv A w i).1).1) ℂ)
        (sampledEndpointLeft w k lam E (partialSlotEquiv A w i).1
          (partialSlotChoice A w (choicesOfOriginalGateLabelsAt w p η) i,
            partialSlotChoice A w (choicesOfOriginalGateLabelsAt w p θ) i) (j i) ω)
    let N := fun i : Fin R.length ↦
      basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w
        (partialSlotEquiv A w i).1).2) ℂ)
        (sampledEndpointRight w k lam F (partialSlotEquiv A w i).1
          (partialSlotChoice A w (choicesOfOriginalGateLabelsAt w p η) i,
            partialSlotChoice A w (choicesOfOriginalGateLabelsAt w p θ) i) (j i) ω)
    HEq (incidentSampledEndpointWord w k lam E F p η θ j ω).eval
      (SourceInventory.endpointRegisterWord
        ((SourceInventory.endpointRegisterData R U V M N).filter
          (fun z ↦ partySelector q z.1.owner))).eval := by
  classical
  intro A hp q R U V M N
  let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let D := SourceInventory.endpointRegisterData R U V M N
  let Dp := D.filter (fun z ↦ partySelector q z.1.owner)
  have hDp : Dp.map Sigma.fst =
      Layout.restrict (partySelector q) (SourceInventory.slotLayout R U V) :=
    SourceInventory.endpointRegisterData_filter_layout (partySelector q) R U V M N
  have hselected :
      Layout.mapOwner lift (Layout.restrict (partySelector q)
        (SourceInventory.slotLayout R U V)) =
      Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []) := by
    rw [List.append_nil]
    exact mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hin : Layout.mapOwner lift (Dp.map Sigma.fst) =
      Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []) :=
    (congrArg (Layout.mapOwner lift) hDp).trans hselected
  change HEq
    (((SourceInventory.endpointRegisterWord Dp).mapOwner lift).castLayouts hin hin).eval
    (SourceInventory.endpointRegisterWord Dp).eval
  exact SourceInventory.endpointRegisterWord_eval_heq_mapOwner_castLayouts Dp lift hin hin

/-- Reconstructing incident choices preserves the original label at each
surviving source slot. This equality is proved before any sampled operator or
layout identification is formed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem incidentPartialSlotChoice_eq_allSourceLabel (w : SourceCircuit a b)
    (p : P) (ξ : Choices (fun _ ↦ true) w)
    (i : Fin (partialSlots
      (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w).length) :
    partialSlotChoice
        (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
          (affectedOwner (fun _ : P ↦ true) t)) w
        (choicesOfOriginalGateLabelsAt w p (originalGateLabelsAtOfAllChoices w p ξ)) i =
      allSourceLabel w ξ (partialSlotEquiv
        (fun t : P ↦ partySelector (some ⟨p, rfl⟩)
          (affectedOwner (fun _ : P ↦ true) t)) w i).1 := by
  rw [choicesOfOriginalGateLabelsAt_eq_projectAllChoices]
  exact projectedSlotChoice_eq_allSourceLabel _ w ξ i

/-- The incident sampled word with extracted labels evaluates to the filtered
original endpoint data. Label substitution is confined to the two operator
families, before comparison of endpoint words.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–434. -/
theorem incidentSampledEndpointWord_eval_heq_selectedRegisterWord
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let M := sampledEndpointOperatorLeft w k lam E ξ ζ j ω
    let N := sampledEndpointOperatorRight w k lam F ξ ζ j ω
    let D := (partialPositions A w).flatMap (endpointDataAt A w M N)
    HEq (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv A w i).1) ω).eval
      (SourceInventory.endpointRegisterWord
        (D.filter (fun z ↦ partySelector q z.1.owner))).eval := by
  classical
  intro A hp q M N D
  let U := fun i : Fin (partialSlots A w).length ↦
    euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
  let V := fun i : Fin (partialSlots A w).length ↦
    euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
  let χξ := choicesOfOriginalGateLabelsAt w p (originalGateLabelsAtOfAllChoices w p ξ)
  let χζ := choicesOfOriginalGateLabelsAt w p (originalGateLabelsAtOfAllChoices w p ζ)
  let Mi : ∀ i, U i →L[ℂ] U i := fun i ↦
    basisMatrixOperator (EuclideanSpace.basisFun _ ℂ)
      (sampledEndpointLeft w k lam E (partialSlotEquiv A w i).1
        (partialSlotChoice A w χξ i, partialSlotChoice A w χζ i)
        (j (partialSlotEquiv A w i).1) ω)
  let Ni : ∀ i, V i →L[ℂ] V i := fun i ↦
    basisMatrixOperator (EuclideanSpace.basisFun _ ℂ)
      (sampledEndpointRight w k lam F (partialSlotEquiv A w i).1
        (partialSlotChoice A w χξ i, partialSlotChoice A w χζ i)
        (j (partialSlotEquiv A w i).1) ω)
  have hM : Mi = (fun i ↦ M (partialSlotEquiv A w i).1) := by
    funext i
    exact congrArg₂
      (fun η θ ↦ basisMatrixOperator
        (EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).1) ℂ)
        (sampledEndpointLeft w k lam E (partialSlotEquiv A w i).1
          (η, θ) (j (partialSlotEquiv A w i).1) ω))
      (incidentPartialSlotChoice_eq_allSourceLabel w p ξ i)
      (incidentPartialSlotChoice_eq_allSourceLabel w p ζ i)
  have hN : Ni = (fun i ↦ N (partialSlotEquiv A w i).1) := by
    funext i
    exact congrArg₂
      (fun η θ ↦ basisMatrixOperator
        (EuclideanSpace.basisFun (Fin (sourceDims w (partialSlotEquiv A w i).1).2) ℂ)
        (sampledEndpointRight w k lam F (partialSlotEquiv A w i).1
          (η, θ) (j (partialSlotEquiv A w i).1) ω))
      (incidentPartialSlotChoice_eq_allSourceLabel w p ξ i)
      (incidentPartialSlotChoice_eq_allSourceLabel w p ζ i)
  have hdata : SourceInventory.endpointRegisterData (partialSlots A w) U V Mi Ni = D :=
    (congrArg₂ (SourceInventory.endpointRegisterData (partialSlots A w) U V) hM hN).trans
      (endpointRegisterData_partialSlots A w M N)
  have hcast := incidentSampledEndpointWord_eval_heq_endpointRegisterWord w k lam E F p
    (originalGateLabelsAtOfAllChoices w p ξ) (originalGateLabelsAtOfAllChoices w p ζ)
    (fun i ↦ j (partialSlotEquiv A w i).1) ω
  exact eval_heq_filtered_endpointRegisterWord_of_eq
    (incidentSampledEndpointWord w k lam E F p
      (originalGateLabelsAtOfAllChoices w p ξ) (originalGateLabelsAtOfAllChoices w p ζ)
      (fun i ↦ j (partialSlotEquiv A w i).1) ω)
    (SourceInventory.endpointRegisterData (partialSlots A w) U V Mi Ni) D
    (partySelector q) hdata hcast

end SourceCircuit
end TNLean.PEPS.PairEffect
