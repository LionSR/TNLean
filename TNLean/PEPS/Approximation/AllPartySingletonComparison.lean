/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentGateLabels
import TNLean.PEPS.Approximation.WordSelectedOwnerLocalPart
import TNLean.PEPS.Approximation.NonincidentAllGateRestriction
import TNLean.PEPS.Approximation.WordOwnerEvaluation

/-!
# A gate in the singleton and all-party partial expansions

The remaining operator selected at one original party is the same in the
all-party expansion and the singleton expansion projected from that very
choice. At an incident gate the original branch label is identical. At a
nonincident gate the singleton expansion retains the whole exterior operation;
its restriction to the selected party is the spectator identity. No label is
chosen at an untouched gate and no source preparation is cancelled.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap

private theorem id_heq_of_memory_eq {E F : HSpace} (h : E = F) :
    HEq (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F) := by
  cases h
  rfl

namespace SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]

/-- The actual remaining operator at one original party agrees for the
all-party choice and its singleton projection. The participant and branch
sets may be empty; no extension of local labels or nonzero scalar is assumed.
This statement compares a single actual gate, including its spectators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
theorem restrict_partialWord_all_gate_localPart_eval_heq_singleton_projection
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    HEq (W.localPart.restrict (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W.sources_localPart).eval
      ((V.localPart.restrict (partySelector q) V.sources_localPart).mapOwner lift).eval := by
  classical
  intro A hp q lift χ W V
  let all := affectedOwner (fun _ : P ↦ true)
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let fa := affectedOwner A
  let sq := partySelector q
  let sp := partySelector p
  have hfAll : ∀ r, all r = qp ↔ r = p := by
    intro r
    simp [all, qp, affectedOwner]
  have hfA : ∀ r, fa r = q ↔ r = p := by
    intro r
    by_cases hr : A r = true
    · simp [fa, q, affectedOwner, hr]
    · have hne : r ≠ p := by
        intro h
        subst r
        exact hr hp
      simp [fa, q, affectedOwner, hr, hne]
  by_cases hincident : ∃ t : C, owner t = p
  · obtain ⟨t, ht⟩ := hincident
    have htA : ∃ t : C, A (owner t) = true := ⟨t, by rw [ht]; exact hp⟩
    have htAll : ∃ _t : C, true = true := ⟨t, rfl⟩
    let eAll : Choices (fun _ : P ↦ true) (.gate owner G tail) ≃ ι :=
      Equiv.cast (by simp only [Choices]; exact if_pos ⟨t, by trivial⟩)
    let eA : Choices A (.gate owner G tail) ≃ ι :=
      Equiv.cast (by simp only [Choices]; exact if_pos htA)
    let i := eAll ξ
    have hi : eA χ = i := by
      exact choiceAt_projectAllChoices A (.gate owner G tail) ξ ()
        ((isTouched_gate_iff A owner G tail).mpr htA)
    let U := ((G.branchWord i).mapOwner owner).appendTail tail
    have hW : W = U.mapOwner all := by
      unfold W partialWord
      rw [dite_eq_left htAll]
      rfl
    have hV : V = U.mapOwner fa := by
      unfold V partialWord
      rw [dite_eq_left htA]
      change (((G.branchWord (eA χ)).mapOwner owner).appendTail tail).mapOwner fa = _
      rw [hi]
    let R := U.localPart.restrict sp U.sources_localPart
    have hAll := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
      all p qp hfAll U
    have hOne := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
      fa p q hfA U
    rw [hW, hV]
    exact hAll.trans ((Word.eval_mapOwner_heq all R).trans
      ((Word.eval_mapOwner_heq fa R).symm.trans
        (hOne.symm.trans
          (Word.eval_mapOwner_heq lift
            ((U.mapOwner fa).localPart.restrict sq (U.mapOwner fa).sources_localPart)).symm)))
  · have howner : ∀ t, owner t ≠ p := by
      intro t ht
      exact hincident ⟨t, ht⟩
    have htA : ¬ ∃ t : C, A (owner t) = true := by
      rintro ⟨t, ht⟩
      have he : owner t = p := by
        simpa only [A, partySelector_affectedOwner_all_apply, partySelector,
          decide_eq_true_eq] using ht
      exact howner t he
    have hV : V = Word.groupedBlockMap fa none
        (Layout.mapOwner owner a) (Layout.mapOwner owner b)
        (Layout.affectedOwner_mapOwner_eq_none A owner htA a)
        (Layout.affectedOwner_mapOwner_eq_none A owner htA b)
        (G.evalAtOwners owner) tail := by
      unfold V partialWord
      rw [dite_eq_right htA]
      rfl
    have hsV : V.sources = [] := by
      rw [hV]
      simp only [Word.groupedBlockMap, Word.sources_castLayouts, Word.sources]
    have hOne : HEq (V.localPart.restrict sq V.sources_localPart).eval
        (Word.id (Layout.atParty q (Layout.mapOwner fa tail))).eval := by
      refine (Word.restrict_localPart_eval_heq_of_sources_nil sq V hsV).trans ?_
      rw [hV]
      unfold Word.groupedBlockMap
      rw [Word.restrict_castLayouts]
      exact (Word.eval_castLayouts_heq _ _ _).trans
        (Word.restrict_localMap_false_eval_heq sq none _ _ _ _
          (by simp [sq, q, partySelector]))
    have hAll := restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident
      owner G tail p howner ξ
    have hsq : (fun r ↦ sq (fa r)) = sp := by
      funext r
      apply Bool.eq_iff_iff.mpr
      simpa only [sq, sp, partySelector, decide_eq_true_eq] using hfA r
    have hsp : (fun r ↦ partySelector qp (all r)) = sp := by
      funext r
      apply Bool.eq_iff_iff.mpr
      simpa only [sp, partySelector, decide_eq_true_eq] using hfAll r
    have htAll : Layout.atParty qp (Layout.mapOwner all tail) =
        Layout.mapOwner all (Layout.restrict sp tail) := by
      change Layout.restrict (partySelector qp) (Layout.mapOwner all tail) = _
      rw [Layout.restrict_mapOwner, hsp]
    have htA : Layout.atParty q (Layout.mapOwner fa tail) =
        Layout.mapOwner fa (Layout.restrict sp tail) := by
      change Layout.restrict sq (Layout.mapOwner fa tail) = _
      rw [Layout.restrict_mapOwner, hsq]
    have hMapped : HEq
        ((V.localPart.restrict sq V.sources_localPart).mapOwner lift).eval
        (Word.id (Layout.atParty q (Layout.mapOwner fa tail))).eval :=
      (Word.eval_mapOwner_heq lift _).trans hOne
    have htailMem : Mem (Layout.atParty qp (Layout.mapOwner all tail)) =
        Mem (Layout.atParty q (Layout.mapOwner fa tail)) :=
      ((congrArg Mem htAll).trans (Layout.mem_mapOwner all _)).trans
        ((congrArg Mem htA).trans (Layout.mem_mapOwner fa _)).symm
    have hid : HEq (Word.id (Layout.atParty qp (Layout.mapOwner all tail))).eval
        (Word.id (Layout.atParty q (Layout.mapOwner fa tail))).eval := by
      exact id_heq_of_memory_eq htailMem
    exact hAll.trans (hid.trans hMapped.symm)

end SourceCircuit
end TNLean.PEPS.PairEffect
