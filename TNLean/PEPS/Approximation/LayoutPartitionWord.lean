/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.FrontRegisters
import TNLean.Lattice.PartyCircuit.PartyPartition
import TNLean.Lattice.PartyCircuit.OriginalCircuitLift

/-!
# Collecting the selected registers in front

The canonical partition `Layout.partitionIso` identifies the memory of a layout with the tensor
product of the memories of its selected registers and of the others, each in their original
order. This file realizes it by a word of exchanges of tensor factors: `Layout.partitionWord`
moves the selected registers in front of the others, and `Layout.unpartitionWord` moves them
back. Both are reorderings: they contain no local map and no pair source.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 32–35 (exchanges of tensor factors carry no information), and the partition by parties
  of `eq:compression-source-gate`, lines 233–251.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace Layout

/-- Collect the selected registers of a layout in front of the others, each in their original
order. -/
def partitionWord (f : P → Bool) : (ℓ : Layout P) →
    Word ℓ (restrict f ℓ ++ restrict (fun p ↦ !f p) ℓ)
  | [] => .id []
  | r :: ℓ =>
      if h : f r.owner = true then
        (Word.frame r (partitionWord f ℓ)).castLayouts rfl (by simp [restrict_cons, h])
      else
        (Word.comp (Word.frame r (partitionWord f ℓ))
          (Word.exchangeBlocks [r] (restrict f ℓ) (restrict (fun p ↦ !f p) ℓ))).castLayouts rfl
          (by simp [restrict_cons, h])

/-- Move the selected registers, collected in front, back to their positions in the layout. -/
def unpartitionWord (f : P → Bool) : (ℓ : Layout P) →
    Word (restrict f ℓ ++ restrict (fun p ↦ !f p) ℓ) ℓ
  | [] => .id []
  | r :: ℓ =>
      if h : f r.owner = true then
        (Word.frame r (unpartitionWord f ℓ)).castLayouts (by simp [restrict_cons, h]) rfl
      else
        (Word.comp (Word.moveHead r (restrict f ℓ) (restrict (fun p ↦ !f p) ℓ))
          (Word.frame r (unpartitionWord f ℓ))).castLayouts (by simp [restrict_cons, h]) rfl

theorem isReordering_partitionWord (f : P → Bool) :
    (ℓ : Layout P) → (partitionWord f ℓ).IsReordering
  | [] => Word.isReordering_id _
  | r :: ℓ => by
      have ih := isReordering_partitionWord f ℓ
      simp only [partitionWord]
      split
      · exact Word.isReordering_castLayouts ((Word.isReordering_frame_iff r _).2 ih) _ _
      · exact Word.isReordering_castLayouts
          (((Word.isReordering_frame_iff r _).2 ih).comp (Word.isReordering_exchangeBlocks _ _ _))
          _ _

theorem isReordering_unpartitionWord (f : P → Bool) :
    (ℓ : Layout P) → (unpartitionWord f ℓ).IsReordering
  | [] => Word.isReordering_id _
  | r :: ℓ => by
      have ih := isReordering_unpartitionWord f ℓ
      simp only [unpartitionWord]
      split
      · exact Word.isReordering_castLayouts ((Word.isReordering_frame_iff r _).2 ih) _ _
      · exact Word.isReordering_castLayouts
          ((Word.isReordering_moveHead _ _ _).comp ((Word.isReordering_frame_iff r _).2 ih)) _ _

private theorem memCongr_rfl_symm_apply {a : Layout P} (h : a = a) (x : Mem a) :
    (memCongr h).symm x = x :=
  rfl

private theorem memCongr_rfl_apply' {a : Layout P} (h : a = a) (x : Mem a) :
    memCongr h x = x :=
  rfl

private theorem appendIso_memCongr_heq {X Y X' Y' : Layout P} (hX : X' = X) (hY : Y' = Y)
    (h : X' ++ Y' = X ++ Y) (z : Mem (X' ++ Y')) :
    HEq (appendIso X Y (memCongr h z)) (appendIso X' Y' z) := by
  subst hX
  subst hY
  rfl

private theorem appendIso_symm_memCongr_heq {X Y X' Y' : Layout P} (hX : X' = X) (hY : Y' = Y)
    (h : X ++ Y = X' ++ Y') (z : Mem X ⊗[ℂ] Mem Y) (z' : Mem X' ⊗[ℂ] Mem Y') (hz : HEq z z') :
    HEq (memCongr h ((appendIso X Y).symm z)) ((appendIso X' Y').symm z') := by
  subst hX
  subst hY
  cases hz
  rfl

/-- The partition word realizes the canonical partition of the registers. -/
theorem appendIso_eval_partitionWord (f : P → Bool) :
    (ℓ : Layout P) → (x : Mem ℓ) →
      appendIso (restrict f ℓ) (restrict (fun p ↦ !f p) ℓ) ((partitionWord f ℓ).eval x) =
        partitionIso f ℓ x
  | [], x => rfl
  | r :: ℓ, x => by
      induction x using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul u v =>
          by_cases h : f r.owner = true
          · simp only [partitionWord, dite_eq_left h, Word.eval_castLayouts, comp_apply,
              isoL_apply]
            erw [memCongr_rfl_symm_apply]
            rw [Word.eval_frame, lTensor_tmul]
            apply eq_of_heq
            refine (appendIso_memCongr_heq (X' := r :: restrict f ℓ)
              (Y' := restrict (fun p ↦ !f p) ℓ) (by simp [restrict_cons, h])
              (by simp [restrict_cons, h]) _ _).trans ?_
            refine HEq.trans ?_ (partitionIso_cons_true_tmul f r ℓ h u v).symm
            change HEq ((TensorProduct.assocIsometry ℂ _ _ _).symm
              (u ⊗ₜ appendIso _ _ ((partitionWord f ℓ).eval v))) _
            rw [appendIso_eval_partitionWord f ℓ v]
          · have h' : f r.owner = false := Bool.eq_false_iff.mpr h
            simp only [partitionWord, dite_eq_right h, Word.eval_castLayouts, comp_apply,
              isoL_apply]
            erw [memCongr_rfl_symm_apply]
            rw [Word.eval_comp, comp_apply, Word.eval_frame, lTensor_tmul]
            obtain ⟨z, rfl⟩ := (partitionIso f ℓ).symm.surjective v
            have hv : (partitionWord f ℓ).eval ((partitionIso f ℓ).symm z) =
                (appendIso _ _).symm z := by
              rw [LinearIsometryEquiv.eq_symm_apply, appendIso_eval_partitionWord f ℓ,
                LinearIsometryEquiv.apply_symm_apply]
            rw [hv]
            apply eq_of_heq
            refine (appendIso_memCongr_heq (X' := restrict f ℓ)
              (Y' := r :: restrict (fun p ↦ !f p) ℓ) (by simp [restrict_cons, h'])
              (by simp [restrict_cons, h']) _ _).trans ?_
            refine HEq.trans ?_ (partitionIso_cons_false_tmul f r ℓ h' u _).symm
            rw [LinearIsometryEquiv.apply_symm_apply]
            clear hv
            apply heq_of_eq
            induction z using TensorProduct.inductionOn with
            | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
            | tmul t b =>
                rw [← appendIso_one_symm_tmul r, Word.eval_exchangeBlocks_appendIso_symm,
                  appendIso_one_symm_tmul, leftCommIso_tmul]
                erw [LinearIsometryEquiv.apply_symm_apply]

/-- The unpartition word undoes the canonical partition of the registers. -/
theorem eval_unpartitionWord_appendIso_symm (f : P → Bool) :
    (ℓ : Layout P) → (z : Mem (restrict f ℓ) ⊗[ℂ] Mem (restrict (fun p ↦ !f p) ℓ)) →
      (unpartitionWord f ℓ).eval
          ((appendIso (restrict f ℓ) (restrict (fun p ↦ !f p) ℓ)).symm z) =
        (partitionIso f ℓ).symm z
  | [], z => rfl
  | r :: ℓ, z => by
      obtain ⟨x, rfl⟩ := (partitionIso f (r :: ℓ)).surjective z
      rw [LinearIsometryEquiv.symm_apply_apply]
      induction x using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul u v =>
          obtain ⟨y, rfl⟩ := (partitionIso f ℓ).symm.surjective v
          by_cases h : f r.owner = true
          · simp only [unpartitionWord, dite_eq_left h, Word.eval_castLayouts, comp_apply,
              isoL_apply]
            erw [memCongr_rfl_apply']
            have hc : (memCongr (by simp [restrict_cons, h] :
                r :: (restrict f ℓ ++ restrict (fun p ↦ !f p) ℓ) =
                  restrict f (r :: ℓ) ++ restrict (fun p ↦ !f p) (r :: ℓ))).symm
                ((appendIso _ _).symm (partitionIso f (r :: ℓ)
                  (u ⊗ₜ (partitionIso f ℓ).symm y))) =
                (u ⊗ₜ (appendIso _ _).symm y : Mem (r :: (restrict f ℓ ++
                  restrict (fun p ↦ !f p) ℓ))) := by
              rw [← memCongr_symm]
              apply eq_of_heq
              refine (appendIso_symm_memCongr_heq (X' := r :: restrict f ℓ)
                (Y' := restrict (fun p ↦ !f p) ℓ) (by simp [restrict_cons, h])
                (by simp [restrict_cons, h]) _ _ _
                (partitionIso_cons_true_tmul f r ℓ h u _)).trans ?_
              rw [LinearIsometryEquiv.apply_symm_apply]
              induction y using TensorProduct.inductionOn with
              | add a b ha hb =>
                  simp only [TensorProduct.tmul_add, map_add]
                  exact add_heq rfl ha hb
              | tmul s t => rfl
            rw [hc, Word.eval_frame, lTensor_tmul, eval_unpartitionWord_appendIso_symm f ℓ y]
          · have h' : f r.owner = false := Bool.eq_false_iff.mpr h
            simp only [unpartitionWord, dite_eq_right h, Word.eval_castLayouts, comp_apply,
              isoL_apply]
            erw [memCongr_rfl_apply']
            rw [Word.eval_comp, comp_apply, Word.eval_frame]
            induction y using TensorProduct.inductionOn with
            | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
            | tmul s t =>
                have hc : (memCongr (by simp [restrict_cons, h'] :
                    restrict f ℓ ++ r :: restrict (fun p ↦ !f p) ℓ =
                      restrict f (r :: ℓ) ++ restrict (fun p ↦ !f p) (r :: ℓ))).symm
                    ((appendIso _ _).symm (partitionIso f (r :: ℓ)
                      (u ⊗ₜ (partitionIso f ℓ).symm (s ⊗ₜ t)))) =
                    (appendIso (restrict f ℓ) (r :: restrict (fun p ↦ !f p) ℓ)).symm
                      (s ⊗ₜ (u ⊗ₜ t : Mem (r :: restrict (fun p ↦ !f p) ℓ))) := by
                  rw [← memCongr_symm]
                  apply eq_of_heq
                  exact appendIso_symm_memCongr_heq (X' := restrict f ℓ)
                    (Y' := r :: restrict (fun p ↦ !f p) ℓ) (by simp [restrict_cons, h'])
                    (by simp [restrict_cons, h']) _ _ _
                    ((partitionIso_cons_false_tmul f r ℓ h' u _).trans (heq_of_eq (by
                      rw [LinearIsometryEquiv.apply_symm_apply, leftCommIso_tmul])))
                rw [hc, Word.eval_moveHead_appendIso_symm, lTensor_tmul,
                  eval_unpartitionWord_appendIso_symm f ℓ]

end Layout

end TNLean.PEPS.PairEffect
