/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentSampledEndpointWord
import TNLean.PEPS.Approximation.EndpointRegisterRestriction
import TNLean.PEPS.Approximation.WordOwnerEvaluation
import TNLean.PEPS.Approximation.PartyTensorMaps
import Mathlib.Data.List.OfFn

/-! # Comparing the actual sampled endpoint word with its incident construction

After restriction to one original party, the all-party endpoint word and the
word constructed from that party's incident labels have the same ordered
endpoint spaces and maps. Each map retains its original source occurrence,
the independently extracted ket and bra labels, and the same original sample
index and ordered-pair Gaussian array. The local word receives only incident
sample indices; neither labels nor samples are extended to other positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect

namespace SourceInventory
variable {P Q : Type}

private def mapEndpointData (f : P → Q)
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    List (Sigma (fun r : Reg Q ↦ r.space →L[ℂ] r.space)) :=
  D.map (fun z ↦ ⟨⟨f z.1.owner, z.1.space⟩, z.2⟩)

private theorem eval_endpointRegisterWord_cons
    (z : Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    (endpointRegisterWord (z :: D)).eval =
      TensorProduct.mapL z.2 (endpointRegisterWord D).eval := by
  apply clm_ext_tmul
  intro x y
  simp [endpointRegisterWord, Word.localEndpoint, Word.eval, appendIso,
    isoL_apply, LinearIsometryEquiv.symm_lTensor, ContinuousLinearMap.lTensor_tmul,
    TensorProduct.mapL_tmul]

/-- Owner labels do not change the operator of an already retained endpoint
word. Its endpoint spaces, maps and order are unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434
and 565–588. -/
private theorem endpointRegisterWord_eval_heq_mapOwner (f : P → Q)
    (D : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))) :
    HEq (endpointRegisterWord D).eval
      (endpointRegisterWord (mapEndpointData f D)).eval := by
  induction D with
  | nil => rfl
  | cons z D ih =>
      have hL : (mapEndpointData f D).map Sigma.fst =
          Layout.mapOwner f (D.map Sigma.fst) := by
        simp only [mapEndpointData, List.map_map, Layout.mapOwner, Function.comp_def]
      have hM : Mem (D.map Sigma.fst) = Mem ((mapEndpointData f D).map Sigma.fst) :=
        ((congrArg Mem hL).trans (Layout.mem_mapOwner f _)).symm
      exact (heq_of_eq (eval_endpointRegisterWord_cons z D)).trans
        ((mapL_heq rfl rfl hM hM z.2 z.2
          (endpointRegisterWord D).eval
          (endpointRegisterWord (mapEndpointData f D)).eval HEq.rfl ih).trans
          (heq_of_eq (eval_endpointRegisterWord_cons
            ⟨⟨f z.1.owner, z.1.space⟩, z.2⟩ (mapEndpointData f D))).symm)

private theorem endpointRegisterData_eq_ofFn (R : SourceInventory P)
    (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i) :
    endpointRegisterData R U V A B =
      (List.ofFn fun i : Fin R.length ↦
        ([⟨⟨(R.get i).left, U i⟩, A i⟩,
          ⟨⟨(R.get i).right, V i⟩, B i⟩] :
          List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space)))).flatten := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      simp only [endpointRegisterData, List.ofFn_succ, List.flatten_cons,
        List.get_cons_zero, List.get_cons_succ', List.cons_append, List.nil_append]
      exact congrArg (List.cons ⟨⟨r.left, U 0⟩, A 0⟩)
        (congrArg (List.cons ⟨⟨r.right, V 0⟩, B 0⟩) (ih _ _ _ _))

private theorem endpointRegisterWord_eval_heq_of_eq
    {D E : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))} (h : D = E) :
    HEq (endpointRegisterWord D).eval (endpointRegisterWord E).eval := by
  cases h
  rfl

end SourceInventory

namespace SourceCircuit
variable {P : Type} {a b : Layout P}

private def endpointDataAt (A : P → Bool) (w : SourceCircuit a b)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) (e : sourceLocations w) :
    List (Sigma (fun r : Reg (Option {p : P // A p = true}) ↦ r.space →L[ℂ] r.space)) :=
  [⟨⟨affectedOwner A (endpoints w e).1, euc (Fin (sourceDims w e).1)⟩, M e⟩,
    ⟨⟨affectedOwner A (endpoints w e).2, euc (Fin (sourceDims w e).2)⟩, N e⟩]

private theorem endpointRegisterData_partialSlots (A : P → Bool) (w : SourceCircuit a b)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) :
    SourceInventory.endpointRegisterData (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
      (fun i ↦ M (partialSlotEquiv A w i).1)
      (fun i ↦ N (partialSlotEquiv A w i).1) =
        (partialPositions A w).flatMap (endpointDataAt A w M N) := by
  rw [SourceInventory.endpointRegisterData_eq_ofFn]
  have hdata (i : Fin (partialSlots A w).length) :
      ([⟨⟨((partialSlots A w).get i).left,
          euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)⟩,
          M (partialSlotEquiv A w i).1⟩,
        ⟨⟨((partialSlots A w).get i).right,
          euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)⟩,
          N (partialSlotEquiv A w i).1⟩] :
        List (Sigma (fun r : Reg (Option {p : P // A p = true}) ↦
          r.space →L[ℂ] r.space))) =
      endpointDataAt A w M N (partialSlotEquiv A w i).1 := by
    exact congrArg₂
      (fun (left right : Option {p : P // A p = true}) ↦
        ([⟨⟨left, euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)⟩,
            M (partialSlotEquiv A w i).1⟩,
          ⟨⟨right, euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)⟩,
            N (partialSlotEquiv A w i).1⟩] :
          List (Sigma (fun r : Reg (Option {p : P // A p = true}) ↦
            r.space →L[ℂ] r.space))))
      (partialSlot_spec A w i).1 (partialSlot_spec A w i).2.1
  simp_rw [hdata]
  have hn : (partialSlots A w).length = (partialPositions A w).length := by
    simp only [partialSlots, List.length_map, List.length_attach]
  rw [List.ofFn_congr hn]
  simp only [partialSlotEquiv_apply, Fin.val_cast]
  change (List.ofFn fun i : Fin (partialPositions A w).length ↦
    endpointDataAt A w M N ((partialPositions A w).get i)).flatten = _
  rw [List.ofFn_comp', List.ofFn_get, List.flatMap_def]

private theorem selectedEndpointData_eq (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    SourceInventory.mapEndpointData lift
        (((partialPositions A w).flatMap (endpointDataAt A w M N)).filter
          (fun z ↦ partySelector q z.1.owner)) =
      ((partialPositions (fun _ ↦ true) w).flatMap
        (endpointDataAt (fun _ ↦ true) w M N)).filter
          (fun z ↦ partySelector (some ⟨p, rfl⟩) z.1.owner) := by
  classical
  intro A hp q lift
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  simp only [partialPositions]
  generalize sourceOrder w = L
  induction L with
  | nil => rfl
  | cons e L ih =>
      by_cases hl : (endpoints w e).1 = p
      · by_cases hr : (endpoints w e).2 = p
        · exact False.elim (endpoints_ne w e (hl.trans hr.symm))
        · simpa [SourceInventory.mapEndpointData, List.filter_cons, List.flatMap_cons,
            endpointDataAt, A, hp, q, qp, lift, partySelector, affectedOwner, hl, hr]
            using congrArg (List.cons
              (⟨⟨qp, euc (Fin (sourceDims w e).1)⟩, M e⟩ :
                Sigma (fun r : Reg (Option {_p : P // true = true}) ↦
                  r.space →L[ℂ] r.space))) ih
      · by_cases hr : (endpoints w e).2 = p
        · simpa [SourceInventory.mapEndpointData, List.filter_cons, List.flatMap_cons,
            endpointDataAt, A, hp, q, qp, lift, partySelector, affectedOwner, hl, hr]
            using congrArg (List.cons
              (⟨⟨qp, euc (Fin (sourceDims w e).2)⟩, N e⟩ :
                Sigma (fun r : Reg (Option {_p : P // true = true}) ↦
                  r.space →L[ℂ] r.space))) ih
        · simpa [SourceInventory.mapEndpointData, List.filter_cons, List.flatMap_cons,
            endpointDataAt, A, hp, q, qp, lift, partySelector, affectedOwner, hl, hr]
            using ih

/-- Restriction of arbitrary endpoint endomorphisms agrees with the endpoint
list selected at the original party. This comparison is independent of the
sampled matrices. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 279–309, 409–434 and 565–588. -/
private theorem restrict_endpointWord_eval_heq_selectedRegisterWord
    (w : SourceCircuit a b) (p : P)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) :
    let all : P → Bool := fun _ ↦ true
    let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
    let A : P → Bool := fun t ↦ partySelector qp (affectedOwner all t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let Ua := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).1)
    let Va := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).2)
    let Za := SourceInventory.endpointWord (partialSlots all w) Ua Va
      (fun i ↦ M (partialSlotEquiv all w i).1)
      (fun i ↦ N (partialSlotEquiv all w i).1)
    let hsa : Za.sources = [] := SourceInventory.sources_endpointWord ..
    let Ds := (partialPositions A w).flatMap (endpointDataAt A w M N)
    let Ds' := Ds.filter (fun z ↦ partySelector q z.1.owner)
    HEq (Za.restrict (partySelector qp) hsa).eval
      (SourceInventory.endpointRegisterWord Ds').eval := by
  classical
  intro all qp A hp q Ua Va Za hsa Ds Ds'
  let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let Da := (partialPositions all w).flatMap (endpointDataAt all w M N)
  let Da' := Da.filter (fun z ↦ partySelector qp z.1.owner)
  have hdataA := endpointRegisterData_partialSlots all w M N
  have ha : HEq (Za.restrict (partySelector qp) hsa).eval
      (SourceInventory.endpointRegisterWord Da').eval :=
    (SourceInventory.restrict_endpointWord_eval_heq_registerWord (partySelector qp)
      (partialSlots all w) Ua Va (fun i ↦ M (partialSlotEquiv all w i).1)
      (fun i ↦ N (partialSlotEquiv all w i).1)).trans
      (SourceInventory.endpointRegisterWord_eval_heq_of_eq
        (congrArg (List.filter (fun z ↦ partySelector qp z.1.owner)) hdataA))
  have hdata : SourceInventory.mapEndpointData lift Ds' = Da' :=
    selectedEndpointData_eq w p M N
  have hnorm : HEq (SourceInventory.endpointRegisterWord Ds').eval
      (SourceInventory.endpointRegisterWord Da').eval :=
    (SourceInventory.endpointRegisterWord_eval_heq_mapOwner lift Ds').trans
      (SourceInventory.endpointRegisterWord_eval_heq_of_eq hdata)
  exact ha.trans hnorm.symm

private def allSourceLabel (w : SourceCircuit a b) (ξ : Choices (fun _ ↦ true) w)
    (e : sourceLocations w) : branchLabels w e.1 :=
  choiceAt (fun _ ↦ true) w ξ e.1
    (isTouched_of_source_endpoint (fun _ ↦ true) w e (Or.inl rfl))

private theorem projectedSlotChoice_eq_allSourceLabel (A : P → Bool)
    (w : SourceCircuit a b) (ξ : Choices (fun _ ↦ true) w)
    (i : Fin (partialSlots A w).length) :
    partialSlotChoice A w (projectAllChoices A w ξ) i =
      allSourceLabel w ξ (partialSlotEquiv A w i).1 :=
  choiceAt_projectAllChoices A w ξ (partialSlotEquiv A w i).1.1
    (isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1
      (partialSlotEquiv A w i).2)

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The actual sampled endpoint operator at one original party is the word
constructed directly from its incident ket and bra labels. Both endpoints
retain the same original sample assignment and ordered-pair Gaussian array.
Empty source inventories, sample sets and halfspaces are included; no
positivity, normalization, label or sample extension, or factorization premise
is assumed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines
253–267, 279–355, 409–434 and 565–588. -/
theorem restrict_sampledEndpointInputWord_eval_eq_incidentSampledEndpointWord
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    ((sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict
      (partySelector (some ⟨p, rfl⟩))
      (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω)).eval =
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
  let lift : Option {t : P // A t = true} → Option {_p : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let M (e : sourceLocations w) :=
    basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w e).1) ℂ)
      (sampledEndpointLeft w k lam E e
        (allSourceLabel w ξ e, allSourceLabel w ζ e) (j e) ω)
  let N (e : sourceLocations w) :=
    basisMatrixOperator (EuclideanSpace.basisFun (Fin (sourceDims w e).2) ℂ)
      (sampledEndpointRight w k lam F e
        (allSourceLabel w ξ e, allSourceLabel w ζ e) (j e) ω)
  let Ua := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).1)
  let Va := fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv all w i).1).2)
  let Za := SourceInventory.endpointWord (partialSlots all w) Ua Va
    (fun i ↦ M (partialSlotEquiv all w i).1)
    (fun i ↦ N (partialSlotEquiv all w i).1)
  have hsa : Za.sources = [] := SourceInventory.sources_endpointWord ..
  let Ds := (partialPositions A w).flatMap (endpointDataAt A w M N)
  let Ds' := Ds.filter (fun z ↦ partySelector q z.1.owner)
  have hdataS := endpointRegisterData_partialSlots A w M N
  have hselected : HEq (Za.restrict (partySelector qp) hsa).eval
      (SourceInventory.endpointRegisterWord Ds').eval :=
    restrict_endpointWord_eval_heq_selectedRegisterWord w p M N
  have hinput : HEq
      ((sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict
        (partySelector qp) (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω)).eval
      (Za.restrict (partySelector qp) hsa).eval := by
    unfold sampledEndpointInputWord
    rw [Word.restrict_castLayouts (partySelector qp)
      (sampledEndpointWord w k lam E F ξ ζ j ω)
      (List.append_nil _).symm (List.append_nil _).symm
      (sources_sampledEndpointWord w k lam E F ξ ζ j ω)]
    exact Word.eval_castLayouts_heq _ _ _
  have hincident : HEq
      (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv A w i).1) ω).eval
      (SourceInventory.endpointRegisterWord Ds').eval := by
    unfold incidentSampledEndpointWord
    dsimp only
    rw [choicesOfOriginalGateLabelsAt_eq_projectAllChoices,
      choicesOfOriginalGateLabelsAt_eq_projectAllChoices]
    simp_rw [projectedSlotChoice_eq_allSourceLabel]
    refine (Word.eval_castLayouts_heq _ _ _).trans ?_
    refine (Word.eval_mapOwner_heq lift _).trans ?_
    exact SourceInventory.endpointRegisterWord_eval_heq_of_eq
      (congrArg (List.filter (fun z ↦ partySelector q z.1.owner)) hdataS)
  apply eq_of_heq
  exact (hinput.trans hselected).trans hincident.symm

end SourceCircuit
end TNLean.PEPS.PairEffect
