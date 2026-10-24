/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPartialSourceSlots
import TNLean.Lattice.Compression.EndpointRegisterRestriction
import TNLean.Lattice.Compression.WordOwnerEvaluation
import TNLean.Lattice.PartyCircuit.PartyTensorMaps
import Mathlib.Data.List.OfFn

/-!
# Restriction of arbitrary endpoint operators at one party

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355,
409–434 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
open scoped TensorProduct
namespace TNLean
open TNLean.Lattice.PartyCircuit

namespace Lattice.PartyCircuit.SourceInventory
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
    isoL_apply, LinearIsometryEquiv.symm_lTensor]
  rfl

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

/-- Equal endpoint data give the same operator after identifying their layouts.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309. -/
theorem endpointRegisterWord_eval_heq_of_eq
    {D E : List (Sigma (fun r : Reg P ↦ r.space →L[ℂ] r.space))} (h : D = E) :
    HEq (endpointRegisterWord D).eval (endpointRegisterWord E).eval := by
  cases h
  rfl

end Lattice.PartyCircuit.SourceInventory

namespace Lattice.PartyCircuit.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- The ordered endpoint register data at one original source occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309. -/
def endpointDataAt (A : P → Bool) (w : SourceCircuit a b)
    (M : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).1) →L[ℂ]
      euc (Fin (sourceDims w e).1))
    (N : ∀ e : sourceLocations w, euc (Fin (sourceDims w e).2) →L[ℂ]
      euc (Fin (sourceDims w e).2)) (e : sourceLocations w) :
    List (Sigma (fun r : Reg (Option {p : P // A p = true}) ↦ r.space →L[ℂ] r.space)) :=
  [⟨⟨affectedOwner A (endpoints w e).1, euc (Fin (sourceDims w e).1)⟩, M e⟩,
    ⟨⟨affectedOwner A (endpoints w e).2, euc (Fin (sourceDims w e).2)⟩, N e⟩]

/-- The canonical partial slots retain the original ordered endpoint data.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–355. -/
theorem endpointRegisterData_partialSlots (A : P → Bool) (w : SourceCircuit a b)
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
theorem restrict_endpointWord_eval_heq_selectedRegisterWord
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


end Lattice.PartyCircuit.SourceCircuit
end TNLean
