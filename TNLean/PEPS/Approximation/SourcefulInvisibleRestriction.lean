/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CanonicalPartyFactorization

/-! # Restrictions of hoisted sources beside spectators

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace Word
/-- A word whose sources, local maps and exchanges leave the selected
registers unchanged. This records its operations, rather than an operator identity.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
private def IsInvisibleWithSources (f : P → Bool) : {a b : Layout P} → Word a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsInvisibleWithSources f ∧ v.IsInvisibleWithSources f
  | _, _, .localMap p .. => f p = false
  | _, _, @Word.source _ p q _ _ _ _ _ => f p = false ∧ f q = false
  | _, _, .swap r s _ => f r.owner = false ∨ f s.owner = false
  | _, _, .frame _ w => w.IsInvisibleWithSources f

private theorem isInvisibleWithSources_castLayouts (f : P → Bool) {a b a' b' : Layout P}
    (w : Word a b) (h : a = a') (h' : b = b') :
    (w.castLayouts h h').IsInvisibleWithSources f ↔ w.IsInvisibleWithSources f := by
  cases h
  cases h'
  rfl

private theorem memCongr_comp {a b c : Layout P} (h : a = b) (h' : b = c) :
    isoL (Layout.memCongr h') ∘L isoL (Layout.memCongr h) =
      isoL (Layout.memCongr (h.trans h')) := by
  cases h
  cases h'
  rfl

private theorem eq_memCongr_of_heq {a b a' b' : Layout P}
    (hi : a = a') (ho : b = b') (hm : a' = b') (A : Mem a →L[ℂ] Mem b)
    (hA : HEq A (isoL (Layout.memCongr hm))) :
    A = isoL (Layout.memCongr ((hi.trans hm).trans ho.symm)) := by
  cases hi
  cases ho
  cases hm
  exact eq_of_heq hA

private theorem memCongr_cons_lTensor (r : Reg P) {a b : Layout P} (h : a = b) :
    (isoL (Layout.memCongr h)).lTensor r.space =
      isoL (Layout.memCongr (congrArg (List.cons r) h)) := by
  cases h
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restricting these actual operations yields the canonical identity on the
selected memory, including arbitrary selected spectator registers.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
private theorem restrict_eval_eq_memCongr_of_isInvisibleWithSources (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (hw : w.IsInvisibleWithSources f) :
    ∃ h : Layout.restrict f a = Layout.restrict f b,
      (w.restrict f hs).eval = isoL (Layout.memCongr h) := by
  induction w with
  | id a => exact ⟨rfl, rfl⟩
  | comp w v ihw ihv =>
      obtain ⟨h, he⟩ := ihw (List.append_eq_nil_iff.mp hs).2 hw.1
      obtain ⟨h', he'⟩ := ihv (List.append_eq_nil_iff.mp hs).1 hw.2
      refine ⟨h.trans h', ?_⟩
      change _ ∘L _ = _
      rw [he, he']
      exact memCongr_comp h h'
  | @localMap p a b ha hb A tail =>
      have hi : Layout.restrict f (a ++ tail) = Layout.restrict f tail := by
        rw [Layout.restrict_append, Layout.restrict_eq_nil_of_owner f ha hw, List.nil_append]
      have ho : Layout.restrict f (b ++ tail) = Layout.restrict f tail := by
        rw [Layout.restrict_append, Layout.restrict_eq_nil_of_owner f hb hw, List.nil_append]
      exact ⟨hi.trans ho.symm, eq_memCongr_of_heq hi ho rfl _
        (restrict_localMap_false_eval_heq f p ha hb A tail hw)⟩
  | source => cases hs
  | swap r s tail =>
      by_cases hr : f r.owner = true
      · have hs' : f s.owner = false := hw.resolve_left (by simp [hr])
        have hi : Layout.restrict f (r :: s :: tail) = r :: Layout.restrict f tail := by
          simp only [Layout.restrict_cons, hr, hs', Bool.false_eq_true, ↓reduceIte]
        have ho : Layout.restrict f (s :: r :: tail) = r :: Layout.restrict f tail := by
          simp only [Layout.restrict_cons, hr, hs', Bool.false_eq_true, ↓reduceIte]
        exact ⟨hi.trans ho.symm, eq_memCongr_of_heq hi ho rfl _
          (restrict_swap_true_false_eval_heq f r s tail hr hs')⟩
      · have hr' : f r.owner = false := Bool.eq_false_iff.mpr hr
        by_cases ht : f s.owner = true
        · have hi : Layout.restrict f (r :: s :: tail) = s :: Layout.restrict f tail := by
            simp only [Layout.restrict_cons, hr', ht, Bool.false_eq_true, ↓reduceIte]
          have ho : Layout.restrict f (s :: r :: tail) = s :: Layout.restrict f tail := by
            simp only [Layout.restrict_cons, hr', ht, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hi.trans ho.symm, eq_memCongr_of_heq hi ho rfl _
            (restrict_swap_false_true_eval_heq f r s tail hr' ht)⟩
        · have ht' : f s.owner = false := Bool.eq_false_iff.mpr ht
          have hi : Layout.restrict f (r :: s :: tail) = Layout.restrict f tail := by
            simp only [Layout.restrict_cons, hr', ht', Bool.false_eq_true, ↓reduceIte]
          have ho : Layout.restrict f (s :: r :: tail) = Layout.restrict f tail := by
            simp only [Layout.restrict_cons, hr', ht', Bool.false_eq_true, ↓reduceIte]
          exact ⟨hi.trans ho.symm, eq_memCongr_of_heq hi ho rfl _
            (restrict_swap_false_false_eval_heq f r s tail hr' ht')⟩
  | @frame r a b w ih =>
      obtain ⟨h, he⟩ := ih hs hw
      by_cases hr : f r.owner = true
      · have hi : Layout.restrict f (r :: a) = r :: Layout.restrict f a := by
          simp only [Layout.restrict_cons, hr, ↓reduceIte]
        have ho : Layout.restrict f (r :: b) = r :: Layout.restrict f b := by
          simp only [Layout.restrict_cons, hr, ↓reduceIte]
        have hm := congrArg (List.cons r) h
        refine ⟨(hi.trans hm).trans ho.symm, eq_memCongr_of_heq hi ho hm _ ?_⟩
        exact (restrict_frame_true_eval_heq f r w hs hr).trans
          (heq_of_eq (by rw [he, memCongr_cons_lTensor]))
      · have hr' : f r.owner = false := Bool.eq_false_iff.mpr hr
        have hi : Layout.restrict f (r :: a) = Layout.restrict f a := by
          simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte]
        have ho : Layout.restrict f (r :: b) = Layout.restrict f b := by
          simp only [Layout.restrict_cons, hr', Bool.false_eq_true, ↓reduceIte]
        exact ⟨(hi.trans h).trans ho.symm, eq_memCongr_of_heq hi ho h _
          ((restrict_frame_false_eval_heq f r w hs hr').trans (heq_of_eq he))⟩
private theorem isInvisibleWithSources_frameList (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hw : w.IsInvisibleWithSources f) (rs : Layout P) :
    (w.frameList rs).IsInvisibleWithSources f := by
  induction rs with
  | nil => exact hw
  | cons r rs ih => exact ih

private theorem isInvisibleWithSources_moveHead (f : P → Bool) (r : Reg P) (a tail : Layout P)
    (h : f r.owner = false ∨ ∀ s ∈ a, f s.owner = false) :
    (moveHead r a tail).IsInvisibleWithSources f := by
  induction a with
  | nil => trivial
  | cons s a ih =>
      refine ⟨ih ?_, ?_⟩
      · exact h.imp_right (fun ha q hq => ha q (List.mem_cons_of_mem _ hq))
      · exact h.elim Or.inr (fun ha => Or.inl (ha s List.mem_cons_self))

private theorem isInvisibleWithSources_exchangeBlocks (f : P → Bool) (a b tail : Layout P)
    (h : (∀ s ∈ a, f s.owner = false) ∨ (∀ s ∈ b, f s.owner = false)) :
    (exchangeBlocks a b tail).IsInvisibleWithSources f := by
  induction b with
  | nil => trivial
  | cons r b ih =>
      refine ⟨isInvisibleWithSources_moveHead f r a (b ++ tail) ?_, ih ?_⟩
      · exact h.elim Or.inr (fun hb => Or.inl (hb r List.mem_cons_self))
      · exact h.imp_right (fun hb q hq => hb q (List.mem_cons_of_mem _ hq))

private theorem isInvisibleWithSources_mapOwner {Q : Type} (owner : P → Q) (f : Q → Bool)
    {a b : Layout P} (w : Word a b) (hs : w.sources = [])
    (hf : ∀ p, f (owner p) = false) : (w.mapOwner owner).IsInvisibleWithSources f := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact ⟨ihw (List.append_eq_nil_iff.mp hs).2,
        ihv (List.append_eq_nil_iff.mp hs).1⟩
  | localMap =>
      exact (isInvisibleWithSources_castLayouts f _ _ _).mpr (hf _)
  | source => cases hs
  | swap r s tail => exact Or.inl (hf r.owner)
  | frame r w ih => exact ih hs

private theorem isInvisibleWithSources_appendTail (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hw : w.IsInvisibleWithSources f) (tail : Layout P)
    (ha : ∀ s ∈ a, f s.owner = false) (hb : ∀ s ∈ b, f s.owner = false) :
    (w.appendTail tail).IsInvisibleWithSources f := by
  change (((exchangeBlocks a tail []).castLayouts
    (congrArg (a ++ ·) (List.append_nil tail))
    (congrArg (tail ++ ·) (List.append_nil a))).IsInvisibleWithSources f) ∧
    ((frameList tail w).IsInvisibleWithSources f ∧
      ((exchangeBlocks tail b []).castLayouts
        (congrArg (tail ++ ·) (List.append_nil b))
        (congrArg (b ++ ·) (List.append_nil tail))).IsInvisibleWithSources f)
  exact ⟨(isInvisibleWithSources_castLayouts f _ _ _).mpr
      (isInvisibleWithSources_exchangeBlocks f a tail [] (Or.inl ha)),
    isInvisibleWithSources_frameList f w hw tail,
    (isInvisibleWithSources_castLayouts f _ _ _).mpr
      (isInvisibleWithSources_exchangeBlocks f tail b [] (Or.inr hb))⟩

private theorem restrict_mapOwner_eq_nil {Q : Type} (owner : P → Q) (f : Q → Bool)
    (a : Layout P) (hf : ∀ p, f (owner p) = false) :
    Layout.restrict f (Layout.mapOwner owner a) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨hr, hsel⟩ := List.mem_filter.mp hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  simp only [hf s.owner, Bool.false_eq_true] at hsel

private theorem memCongr_heq_id {a b t : Layout P} (hi : a = t) (ho : b = t)
    (h : a = b) : HEq (isoL (Layout.memCongr h)) (ContinuousLinearMap.id ℂ (Mem t)) := by
  cases hi
  cases ho
  rfl


private theorem isInvisibleWithSources_castInput (f : P → Bool) {a b a' : Layout P}
    (w : Word a b) (h : a = a') :
    (w.castInput h).IsInvisibleWithSources f ↔ w.IsInvisibleWithSources f := by
  cases h
  rfl

private theorem restrict_sources_eq_nil_of_isInvisibleWithSources
    (f : P → Bool) {a b : Layout P} (w : Word a b) (hw : w.IsInvisibleWithSources f) :
    Layout.restrict f w.sources.layout = [] := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      simp only [Word.sources, SourceInventory.layout_append, Layout.restrict_append,
        ihw hw.1, ihv hw.2, List.nil_append]
  | localMap => rfl
  | @source p q hpq U V η tail =>
      simp only [Word.sources, SourceInventory.layout, PairSource.layout, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Layout.restrict_cons, hw.1, hw.2,
        Bool.false_eq_true, ↓reduceIte]
      rfl
  | swap => rfl
  | frame r w ih => exact ih hw

private theorem isInvisibleWithSources_localPart (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hw : w.IsInvisibleWithSources f) : w.localPart.IsInvisibleWithSources f := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact (isInvisibleWithSources_castInput f _ _).mpr
        ⟨isInvisibleWithSources_frameList f _ (ihw hw.1) _, ihv hw.2⟩
  | localMap => exact hw
  | source => trivial
  | swap => exact hw
  | @frame r a b w ih =>
      refine ⟨isInvisibleWithSources_moveHead f r w.sources.layout a (Or.inr ?_), ih hw⟩
      intro s hs
      apply Bool.eq_false_iff.mpr
      intro ht
      have hm : s ∈ Layout.restrict f w.sources.layout := List.mem_filter.mpr ⟨hs, ht⟩
      rw [restrict_sources_eq_nil_of_isInvisibleWithSources f w hw] at hm
      exact List.not_mem_nil hm

private theorem isInvisibleWithSources_mapOwner_preserved {Q : Type}
    (owner : P → Q) (f : Q → Bool) {a b : Layout P} (w : Word a b)
    (hw : w.IsInvisibleWithSources (fun p => f (owner p))) :
    (w.mapOwner owner).IsInvisibleWithSources f := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw hw.1, ihv hw.2⟩
  | localMap => exact (isInvisibleWithSources_castLayouts f _ _ _).mpr hw
  | @source p q hpq U V η tail =>
      classical
      by_cases he : owner p = owner q
      · simp only [Word.mapOwner, dite_eq_left he]
        exact (isInvisibleWithSources_castLayouts f _ _ _).mpr hw.1
      · simp only [Word.mapOwner, dite_eq_right he]
        exact hw
  | swap => exact hw
  | frame r w ih => exact ih hw

private theorem isInvisibleWithSources_of_allOwners (f : P → Bool)
    {a b : Layout P} (w : Word a b) (hf : ∀ p, f p = false) :
    w.IsInvisibleWithSources f := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | localMap => exact hf _
  | @source p q => exact ⟨hf p, hf q⟩
  | swap r s => exact Or.inl (hf r.owner)
  | frame r w ih => exact ih

private theorem restrict_mapOwner_eq_nil_of_mem {Q : Type}
    (owner : P → Q) (f : Q → Bool) (a : Layout P)
    (hf : ∀ r ∈ a, f (owner r.owner) = false) :
    Layout.restrict f (Layout.mapOwner owner a) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro r hr
  obtain ⟨hr, hsel⟩ := List.mem_filter.mp hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  simp only [hf s hs, Bool.false_eq_true] at hsel

set_option maxHeartbeats 800000 in
-- Nested owner transports elaborate the same dependent tensor layout several times.
/-- Hoisting all sources of an actual word owned away from the selected parties,
placing arbitrary spectators, and grouping owners leaves precisely the selected
spectator identity. The statement concerns the actual local part, so source
vectors may be arbitrary and no cancellation of source preparations is used.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_localPart_mapOwner_appendTail_mapOwner_eval_eq_id_of_disjoint
    {Q T : Type} (owner : P → Q) (regroup : Q → T) (f : T → Bool)
    {a b : Layout P} (w : Word a b)
    (hf : ∀ p, f (regroup (owner p)) = false) (tail : Layout Q) :
    let v := (((w.mapOwner owner).appendTail tail).mapOwner regroup)
    HEq ((v.localPart.restrict f v.sources_localPart).eval)
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict f (Layout.mapOwner regroup tail)))) := by
  let v := (((w.mapOwner owner).appendTail tail).mapOwner regroup)
  have hw := isInvisibleWithSources_of_allOwners (fun p => f (regroup (owner p))) w hf
  have hm := isInvisibleWithSources_mapOwner_preserved owner (fun q => f (regroup q)) w hw
  have ha : ∀ r ∈ Layout.mapOwner owner a, f (regroup r.owner) = false := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
    exact hf s.owner
  have hb : ∀ r ∈ Layout.mapOwner owner b, f (regroup r.owner) = false := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
    exact hf s.owner
  have ht := isInvisibleWithSources_appendTail (fun q => f (regroup q)) _ hm tail ha hb
  have hv : v.IsInvisibleWithSources f := isInvisibleWithSources_mapOwner_preserved regroup f _ ht
  have hvs := restrict_sources_eq_nil_of_isInvisibleWithSources f v hv
  obtain ⟨h, he⟩ := restrict_eval_eq_memCongr_of_isInvisibleWithSources f v.localPart
    v.sources_localPart (isInvisibleWithSources_localPart f v hv)
  have hi : Layout.restrict f (v.sources.layout ++
      Layout.mapOwner regroup (Layout.mapOwner owner a ++ tail)) =
        Layout.restrict f (Layout.mapOwner regroup tail) := by
    rw [Layout.restrict_append, hvs, List.nil_append, Layout.mapOwner_append,
      Layout.restrict_append, restrict_mapOwner_eq_nil_of_mem regroup f _ ha, List.nil_append]
  have ho : Layout.restrict f (Layout.mapOwner regroup (Layout.mapOwner owner b ++ tail)) =
      Layout.restrict f (Layout.mapOwner regroup tail) := by
    rw [Layout.mapOwner_append, Layout.restrict_append,
      restrict_mapOwner_eq_nil_of_mem regroup f _ hb, List.nil_append]
  exact (heq_of_eq he).trans (memCongr_heq_id hi ho h)
end Word
end TNLean.PEPS.PairEffect
