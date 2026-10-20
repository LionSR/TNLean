/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.FrameListRestriction

/-!
# Scalar restrictions under composition and framing

When the selected input, output and source registers are empty, the selected
memory is the scalar field. Its scalar operations multiply under chronological
composition. Framing an excluded register preserves the scalar operation,
including the exchanges that move this register past the prepared sources.
The scalars may vanish.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 233–251, 246–267 and 351–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
private theorem scalar_comp_heq {Q : Type} {a b d : Layout Q}
    (A : Mem a →L[ℂ] Mem b) (B : Mem b →L[ℂ] Mem d)
    (ha : a = []) (hb : b = []) (hd : d = []) (α β : ℂ)
    (hA : HEq A (α • ContinuousLinearMap.id ℂ ℂ))
    (hB : HEq B (β • ContinuousLinearMap.id ℂ ℂ)) :
    HEq (B ∘L A) ((α * β) • ContinuousLinearMap.id ℂ ℂ) := by
  cases ha
  cases hb
  cases hd
  apply heq_of_eq
  rw [eq_of_heq hA, eq_of_heq hB]
  ext
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, mul_comm]

/-- Scalar restrictions compose in chronological order when all retained input,
intermediate, output and source registers are empty. Source: polynomial-PEPS,
`04-compression.tex`, lines 246–251 and 351–381. -/
theorem Word.restrict_localPart_comp_scalar {Q : Type} (f : Q → Bool)
    {a b d : Layout Q} (w : Word a b) (v : Word b d)
    (ha : Layout.restrict f a = []) (hb : Layout.restrict f b = [])
    (hd : Layout.restrict f d = [])
    (hw : Layout.restrict f w.sources.layout = [])
    (hv : Layout.restrict f v.sources.layout = []) (α β : ℂ)
    (he : HEq ((w.localPart.restrict f w.sources_localPart).eval)
      (α • ContinuousLinearMap.id ℂ ℂ))
    (he' : HEq ((v.localPart.restrict f v.sources_localPart).eval)
      (β • ContinuousLinearMap.id ℂ ℂ)) :
    HEq ((((Word.comp w v).localPart).restrict f
      (Word.comp w v).sources_localPart).eval)
      ((α * β) • ContinuousLinearMap.id ℂ ℂ) := by
  have hc : ((Word.frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
    simp only [Word.sources, Word.sources_frameList, Word.sources_localPart, List.nil_append]
  unfold Word.localPart
  refine (Word.restrict_castInput_eval_heq f _ _ hc).trans ?_
  exact scalar_comp_heq
    ((Word.frameList v.sources.layout w.localPart).restrict f
      ((Word.sources_frameList _ _).trans w.sources_localPart)).eval
    (v.localPart.restrict f v.sources_localPart).eval
    (by simp only [Layout.restrict_append, hv, hw, ha, List.nil_append])
    (by simp only [Layout.restrict_append, hv, hb, List.nil_append]) hd α β
    ((Word.restrict_frameList_eval_heq_of_eq_nil f _ hv w.localPart w.sources_localPart).trans he)
    he'


private theorem parties_moveHead {Q : Type} [DecidableEq Q] (r : Reg Q) (rs tail : Layout Q) :
    (Word.moveHead r rs tail).parties = ((r :: (rs ++ tail)).map Reg.owner).toFinset := by
  classical
  induction rs with
  | nil =>
      ext p
      simp [Word.moveHead, Word.parties]
  | cons s rs ih =>
      ext p
      simp only [Word.moveHead, Word.parties, ih, List.cons_append, List.map_cons,
        List.map_append, List.toFinset_cons, List.toFinset_append, Finset.mem_insert,
        Finset.mem_union, List.mem_toFinset, List.mem_map, or_self]
      exact or_left_comm

private theorem restrict_moveHead_eval_heq_id_of_eq_nil {Q : Type}
    (f : Q → Bool) (r : Reg Q) (rs tail : Layout Q)
    (h : Layout.restrict f (r :: (rs ++ tail)) = []) :
    HEq (((Word.moveHead r rs tail).restrict f (Word.sources_moveHead _ _ _)).eval)
      (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  have hp : ((Word.moveHead r rs tail).restrict f (Word.sources_moveHead _ _ _)).parties =
      ∅ := by
    rw [Word.parties_restrict, parties_moveHead]
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact (List.filter_eq_nil_iff.mp h) s hs
  exact (Word.eq_nil_and_eval_eq_id_of_parties_eq_empty _ hp).2.2

/-- Framing an unselected register preserves the actual scalar restriction.
Source: polynomial-PEPS, `04-compression.tex`, lines 246–251 and 351–381. -/
theorem Word.restrict_localPart_frame_scalar {Q : Type} (f : Q → Bool)
    (r : Reg Q) {a b : Layout Q} (w : Word a b)
    (hr : f r.owner = false) (ha : Layout.restrict f a = [])
    (hb : Layout.restrict f b = []) (hs : Layout.restrict f w.sources.layout = [])
    (α : ℂ) (he : HEq ((w.localPart.restrict f w.sources_localPart).eval)
      (α • ContinuousLinearMap.id ℂ ℂ)) :
    HEq ((((Word.frame r w).localPart).restrict f (Word.frame r w).sources_localPart).eval)
      (α • ContinuousLinearMap.id ℂ ℂ) := by
  have hm : Layout.restrict f (r :: (w.sources.layout ++ a)) = [] := by
    simp only [Layout.restrict_cons, hr, Bool.false_eq_true, ↓reduceIte,
      Layout.restrict_append, hs, ha, List.nil_append]
  unfold Word.localPart
  change HEq (((Word.frame r w.localPart).restrict f w.sources_localPart).eval ∘L
    ((Word.moveHead r w.sources.layout a).restrict f (Word.sources_moveHead _ _ _)).eval)
      (α • ContinuousLinearMap.id ℂ ℂ)
  simpa only [one_mul] using scalar_comp_heq
    ((Word.moveHead r w.sources.layout a).restrict f (Word.sources_moveHead _ _ _)).eval
    ((Word.frame r w.localPart).restrict f w.sources_localPart).eval
    (by simp only [Layout.restrict_append, Layout.restrict_cons, hr, Bool.false_eq_true,
      ↓reduceIte, hs, ha, List.nil_append]) hm
    (by simp only [Layout.restrict_cons, hr, Bool.false_eq_true, ↓reduceIte, hb]) 1 α
    (by simpa only [one_smul] using restrict_moveHead_eval_heq_id_of_eq_nil f r _ _ hm)
    ((Word.restrict_frame_false_eval_heq f r _ _ hr).trans he)

end TNLean.PEPS.PairEffect
