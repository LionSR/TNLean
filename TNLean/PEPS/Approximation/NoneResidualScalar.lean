/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceResidualCoordinates
import TNLean.PEPS.Approximation.AllPartialGate
import TNLean.PEPS.Approximation.NoneResidualOperations
import TNLean.PEPS.Approximation.NoneResidualGate

/-!
# The scalar factor of the all-selected chronological residual

When every original party is selected, no register has the grouped owner `none`.
The operations retained at this owner are exactly the gates with no participating
parties. Their literal chronological restriction contributes the product of their
original coefficient sums, including zero sums from empty branch sets.

Source: polynomial-PEPS, `04-compression.tex`, lines 24–28, 233–251 and 351–417.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-noneresidualscalar-01
TNLean.PEPS.PairEffect.SourceCircuit.restrict_partialResidual_all_eval_heq_emptyGateScalar
Provenance-ID: 8769-chronological-network-noneresidualscalar-02
TNLean.PEPS.PairEffect.SourceCircuit.restrict_partialWord_all_localPart_eval_heq_emptyGateScalar
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}
private theorem restrict_affectedOwner_all (a : Layout P) :
    Layout.restrict Option.isNone (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) a) =
      [] := by
  induction a with
  | nil => rfl
  | cons r a ih => simp [Layout.mapOwner, Layout.restrict, affectedOwner]

private theorem id_mem_heq_of_eq_nil {Q : Type} {a : Layout Q} (h : a = []) :
    HEq (ContinuousLinearMap.id ℂ (Mem a)) (ContinuousLinearMap.id ℂ ℂ) := by
  cases h
  rfl

private theorem restrict_localPart_castLayouts_eval_heq {Q : Type} (f : Q → Bool)
    {a b a' b' : Layout Q} (w : Word a b) (ha : a = a') (hb : b = b') :
    HEq (((w.castLayouts ha hb).localPart.restrict f
      (w.castLayouts ha hb).sources_localPart).eval)
      ((w.localPart.restrict f w.sources_localPart).eval) := by
  cases ha
  cases hb
  rfl

namespace SourceCircuit
set_option maxHeartbeats 800000 in
-- The chronological induction retains dependent source-layout equalities.
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
      change HEq (ContinuousLinearMap.id ℂ
        (Mem (Layout.restrict Option.isNone (Layout.mapOwner (affectedOwner (fun _ ↦ true)) a))))
          (1 • ContinuousLinearMap.id ℂ ℂ)
      simpa only [one_smul] using id_mem_heq_of_eq_nil (restrict_affectedOwner_all a)
  | @comp a b d w v ihw ihv =>
      exact Word.restrict_localPart_comp_scalar Option.isNone
        (partialWord (fun _ : P ↦ true) w ξ.1) (partialWord (fun _ : P ↦ true) v ξ.2)
        (restrict_affectedOwner_all a) (restrict_affectedOwner_all b)
        (restrict_affectedOwner_all d) (restrict_sources_partialWord_all_eq_nil w ξ.1)
        (restrict_sources_partialWord_all_eq_nil v ξ.2) _ _ (ihw ξ.1) (ihv ξ.2)
  | localMap p ha hb U tail =>
      simp only [partialWord, Word.mapOwner, emptyGateScalar, one_smul]
      refine (restrict_localPart_castLayouts_eval_heq Option.isNone _ _ _).trans ?_
      exact (Word.restrict_localMap_false_eval_heq Option.isNone _ _ _ _ _
        (by simp [affectedOwner])).trans (id_mem_heq_of_eq_nil (restrict_affectedOwner_all tail))
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases h : Nonempty C
      · simpa only [emptyGateScalar, ite_eq_left h, one_smul] using
          (restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint
            owner G tail ξ ⟨h.some, rfl⟩ Option.isNone (fun q => by simp [affectedOwner])).trans
              (id_mem_heq_of_eq_nil (restrict_affectedOwner_all tail))
      · let : IsEmpty C := not_nonempty_iff.mp h
        simpa only [emptyGateScalar_gate_of_isEmpty] using
          restrict_partialWord_localPart_gate_heq_coeffSum_of_isEmpty owner G tail ξ
  | swap r t tail =>
      simp only [partialWord, Word.mapOwner, Word.localPart, emptyGateScalar, one_smul]
      exact (Word.restrict_swap_false_false_eval_heq Option.isNone _ _ _
        (by simp [affectedOwner]) (by simp [affectedOwner])).trans
          (id_mem_heq_of_eq_nil (restrict_affectedOwner_all tail))
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

end SourceCircuit
end TNLean.PEPS.PairEffect
