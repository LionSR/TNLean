/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceResidualCoordinates
import TNLean.Lattice.Compression.ZeroPartyGates
import TNLean.Lattice.Compression.LayoutExcludedOwners

/-!
# The exterior restriction of an empty-party gate

A gate with no participating parties remains a scalar operation at the exterior
owner in the all-party expansion. Its scalar is the sum of the original branch
coefficients. The identity includes an empty branch set and a vanishing sum;
no scalar is cancelled.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 24–28, 233–251 and 351–417.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace SourceCircuit
/-- The actual empty-party gate retained at the grouped owner `none` acts by
its original coefficient sum. Source: polynomial-PEPS, `04-compression.tex`,
lines 24–28, 233–251 and 351–417. -/
theorem restrict_partialWord_localPart_gate_heq_coeffSum_of_isEmpty
    {C ι : Type} [IsEmpty C] [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let v := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    HEq ((v.localPart.restrict Option.isNone v.sources_localPart).eval)
      ((∑ i, c i) • ContinuousLinearMap.id ℂ ℂ) := by
  have hn {T : Type} [IsEmpty T] (a : Layout T) : a = [] :=
    List.eq_nil_iff_forall_not_mem.mpr (fun r _ => isEmptyElim r.owner)
  cases hn a
  cases hn b
  have he : ¬ ∃ _ : C, true = true :=
    fun ⟨p, _⟩ => isEmptyElim p
  have hw : partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ =
      Word.groupedBlockMap (affectedOwner (fun _ : P ↦ true)) none [] []
        (fun _ h => False.elim (List.not_mem_nil h))
        (fun _ h => False.elim (List.not_mem_nil h)) (G.evalAtOwners owner) tail := by
    unfold partialWord
    rw [dite_eq_right he]
    rfl
  rw [hw]
  simp only [Word.groupedBlockMap, Layout.mapOwner_nil, Word.castLayouts, Word.localPart]
  refine (Word.restrict_localMap_true_eval_heq Option.isNone none _ _ _ _ rfl).trans ?_
  rw [Layout.restrict_mapOwner_eq_nil (affectedOwner (fun _ : P ↦ true))
    Option.isNone tail (by intro p; simp [affectedOwner])]
  have hG : G.eval = (∑ i, c i) • ContinuousLinearMap.id ℂ ℂ :=
    eq_of_heq G.eval_heq_coeffSum_smul_id_of_isEmpty
  have hO : G.evalAtOwners owner = (∑ i, c i) • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp [PreparedSourceGate.evalAtOwners, hG, isoL_apply, Layout.mapOwnerIso]
  have hF : isoL (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) []) ∘L
      G.evalAtOwners owner ∘L
        isoL (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) []).symm =
      (∑ i, c i) • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp [hO, isoL_apply, Layout.mapOwnerIso]
  rw [hF]
  exact heq_of_eq (by
    ext
    simp only [Word.eval, ContinuousLinearMap.rTensor_smul, ContinuousLinearMap.rTensor_id,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      isoL_apply, map_smul, LinearIsometryEquiv.symm_apply_apply])
end SourceCircuit
end TNLean.PEPS.PairEffect
