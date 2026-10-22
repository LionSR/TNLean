/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceResidualCoordinates
import TNLean.Lattice.Compression.ActualSourceEmptyOwner
import TNLean.Lattice.Compression.AllPartialGate
import TNLean.Lattice.Compression.NoneResidualOperations
import TNLean.Lattice.Compression.NoneResidualGate
import TNLean.Lattice.Compression.EmptyGateScalar

/-!
# The scalar factor of the all-selected chronological residual

When every original party is selected, no register has the grouped owner `none`.
The operations retained at this owner are exactly the gates with no participating
parties. Their literal chronological restriction contributes the product of their
original coefficient sums, including zero sums from empty branch sets.

Source: polynomial-PEPS, `04-compression.tex`, lines 24–28, 233–251 and 351–417.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean
open TNLean.Lattice.PartyCircuit TNLean.PEPS.PairEffect
variable {P : Type}
namespace PEPS.PairEffect
private theorem restrict_affectedOwner_all (a : Layout P) :
    Layout.restrict Option.isNone (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) a) =
      [] :=
  Layout.restrict_mapOwner_eq_nil _ _ a (by intro p; simp [affectedOwner])

private theorem restrict_allMapped_localPart {a b : Layout P} (w : Word a b) :
    HEq (((w.mapOwner (affectedOwner (fun _ : P ↦ true))).localPart.restrict Option.isNone
      (w.mapOwner (affectedOwner (fun _ : P ↦ true))).sources_localPart).eval)
      (ContinuousLinearMap.id ℂ ℂ) := by
  have h := Word.restrict_localPart_mapOwner_eval_heq_id_of_disjoint
    (affectedOwner (fun _ : P ↦ true)) none w (by intro p; simp [affectedOwner])
  rw [partySelector_none] at h
  exact h

end PEPS.PairEffect
namespace Lattice.PartyCircuit.SourceCircuit
private theorem restrict_sources_partialWord_all_eq_nil {a b : Layout P}
    (w : SourceCircuit a b) (ξ : Choices (fun _ : P ↦ true) w) :
    Layout.restrict Option.isNone (partialWord (fun _ : P ↦ true) w ξ).sources.layout = [] :=
  (congrArg (Layout.restrict Option.isNone)
    (slotLayout_partialSlots_eq (fun _ : P ↦ true) w ξ)).symm.trans
      (restrict_allResidualSourceLayout_isNone w)

/-- The literal restriction of the actual all-party hoisted branch to the grouped
owner `none` is precisely the product of its empty-participant coefficient sums.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28, 246–251 and 351–417. -/
theorem restrict_partialWord_all_localPart_eval_heq_emptyGateScalar
    {a b : Layout P} (w : SourceCircuit a b) (ξ : Choices (fun _ : P ↦ true) w) :
    HEq (((partialWord (fun _ : P ↦ true) w ξ).localPart.restrict Option.isNone
      (partialWord (fun _ : P ↦ true) w ξ).sources_localPart).eval)
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
  induction w with
  | id a =>
      simp only [emptyGateScalar, one_smul]
      exact restrict_allMapped_localPart (Word.id a)
  | @comp a b d w v ihw ihv =>
      exact Word.restrict_localPart_comp_scalar Option.isNone
        (partialWord (fun _ : P ↦ true) w ξ.1) (partialWord (fun _ : P ↦ true) v ξ.2)
        (restrict_affectedOwner_all a) (restrict_affectedOwner_all b)
        (restrict_affectedOwner_all d) (restrict_sources_partialWord_all_eq_nil w ξ.1)
        (restrict_sources_partialWord_all_eq_nil v ξ.2) _ _ (ihw ξ.1) (ihv ξ.2)
  | localMap p ha hb U tail =>
      simp only [emptyGateScalar, one_smul]
      exact restrict_allMapped_localPart (Word.localMap p ha hb U tail)
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases h : Nonempty C
      · simpa only [emptyGateScalar, ite_eq_left h, one_smul] using
          restrict_partialWord_all_gate_localPart_eval_heq_id owner G tail ξ h
      · let : IsEmpty C := not_nonempty_iff.mp h
        simpa only [emptyGateScalar_gate_of_isEmpty] using
          restrict_partialWord_localPart_gate_heq_coeffSum_of_isEmpty owner G tail ξ
  | swap r t tail =>
      simp only [emptyGateScalar, one_smul]
      exact restrict_allMapped_localPart (Word.swap r t tail)
  | @frame r a b w ih =>
      exact Word.restrict_localPart_frame_scalar Option.isNone
        ⟨affectedOwner (fun _ : P ↦ true) r.owner, r.space⟩
        (partialWord (fun _ : P ↦ true) w ξ) (by simp [affectedOwner])
        (restrict_affectedOwner_all a) (restrict_affectedOwner_all b)
        (restrict_sources_partialWord_all_eq_nil w ξ) _ (ih ξ)
/-- The actual all-party residual in the prescribed source coordinates has the
literal empty-gate scalar at the grouped owner `none`. No normalization or
nonemptiness premise is required. Source: polynomial-PEPS, `04-compression.tex`,
lines 24–28, 246–267 and 409–434. -/
theorem restrict_partialResidual_all_eval_heq_emptyGateScalar
    {a b : Layout P} (w : SourceCircuit a b) (ξ : Choices (fun _ : P ↦ true) w) :
    HEq (((partialResidual (fun _ : P ↦ true) w ξ).restrict Option.isNone
      (sources_partialResidual (fun _ : P ↦ true) w ξ)).eval)
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
  unfold partialResidual Word.residualInSlots
  exact (Word.restrict_castInput_eval_heq Option.isNone _ _
    (partialWord (fun _ : P ↦ true) w ξ).sources_localPart).trans
      (restrict_partialWord_all_localPart_eval_heq_emptyGateScalar w ξ)

end Lattice.PartyCircuit.SourceCircuit
end TNLean
