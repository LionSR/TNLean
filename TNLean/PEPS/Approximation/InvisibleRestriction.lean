/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.UntouchedResidual

/-! # Restrictions to spectator registers

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
/-- A source-free word whose local maps and exchanges leave the selected
registers unchanged. This records its operations, rather than an operator identity.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
private def IsInvisible (f : P → Bool) : {a b : Layout P} → Word a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsInvisible f ∧ v.IsInvisible f
  | _, _, .localMap p .. => f p = false
  | _, _, .source .. => False
  | _, _, .swap r s _ => f r.owner = false ∨ f s.owner = false
  | _, _, .frame _ w => w.IsInvisible f

private theorem isInvisible_castLayouts (f : P → Bool) {a b a' b' : Layout P}
    (w : Word a b) (h : a = a') (h' : b = b') :
    (w.castLayouts h h').IsInvisible f ↔ w.IsInvisible f := by
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
private theorem restrict_eval_eq_memCongr_of_isInvisible (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (hw : w.IsInvisible f) :
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
  | source => cases hw
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
private theorem isInvisible_frameList (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hw : w.IsInvisible f) (rs : Layout P) :
    (w.frameList rs).IsInvisible f := by
  induction rs with
  | nil => exact hw
  | cons r rs ih => exact ih

private theorem isInvisible_moveHead (f : P → Bool) (r : Reg P) (a tail : Layout P)
    (h : f r.owner = false ∨ ∀ s ∈ a, f s.owner = false) :
    (moveHead r a tail).IsInvisible f := by
  induction a with
  | nil => trivial
  | cons s a ih =>
      refine ⟨ih ?_, ?_⟩
      · exact h.imp_right (fun ha q hq => ha q (List.mem_cons_of_mem _ hq))
      · exact h.elim Or.inr (fun ha => Or.inl (ha s List.mem_cons_self))

private theorem isInvisible_exchangeBlocks (f : P → Bool) (a b tail : Layout P)
    (h : (∀ s ∈ a, f s.owner = false) ∨ (∀ s ∈ b, f s.owner = false)) :
    (exchangeBlocks a b tail).IsInvisible f := by
  induction b with
  | nil => trivial
  | cons r b ih =>
      refine ⟨isInvisible_moveHead f r a (b ++ tail) ?_, ih ?_⟩
      · exact h.elim Or.inr (fun hb => Or.inl (hb r List.mem_cons_self))
      · exact h.imp_right (fun hb q hq => hb q (List.mem_cons_of_mem _ hq))

private theorem isInvisible_mapOwner {Q : Type} (owner : P → Q) (f : Q → Bool)
    {a b : Layout P} (w : Word a b) (hs : w.sources = [])
    (hf : ∀ p, f (owner p) = false) : (w.mapOwner owner).IsInvisible f := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact ⟨ihw (List.append_eq_nil_iff.mp hs).2,
        ihv (List.append_eq_nil_iff.mp hs).1⟩
  | localMap =>
      exact (isInvisible_castLayouts f _ _ _).mpr (hf _)
  | source => cases hs
  | swap r s tail => exact Or.inl (hf r.owner)
  | frame r w ih => exact ih hs

private theorem isInvisible_appendTail (f : P → Bool) {a b : Layout P}
    (w : Word a b) (hw : w.IsInvisible f) (tail : Layout P)
    (ha : ∀ s ∈ a, f s.owner = false) (hb : ∀ s ∈ b, f s.owner = false) :
    (w.appendTail tail).IsInvisible f := by
  change (((exchangeBlocks a tail []).castLayouts
    (congrArg (a ++ ·) (List.append_nil tail))
    (congrArg (tail ++ ·) (List.append_nil a))).IsInvisible f) ∧
    ((frameList tail w).IsInvisible f ∧
      ((exchangeBlocks tail b []).castLayouts
        (congrArg (tail ++ ·) (List.append_nil b))
        (congrArg (b ++ ·) (List.append_nil tail))).IsInvisible f)
  exact ⟨(isInvisible_castLayouts f _ _ _).mpr
      (isInvisible_exchangeBlocks f a tail [] (Or.inl ha)),
    isInvisible_frameList f w hw tail,
    (isInvisible_castLayouts f _ _ _).mpr
      (isInvisible_exchangeBlocks f tail b [] (Or.inr hb))⟩

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

/-- An actual source-free residual placed beside arbitrary spectator registers
leaves the selected spectator memory unchanged when all its owners are unselected.
The identity is derived from the local maps and exchanges used by `appendTail`.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_mapOwner_appendTail_eval_eq_id_of_disjoint {Q : Type}
    (owner : P → Q) (f : Q → Bool) {a b : Layout P} (w : Word a b)
    (hs : w.sources = []) (hf : ∀ p, f (owner p) = false) (tail : Layout Q) :
    HEq (((w.mapOwner owner).appendTail tail).restrict f
      (by simp only [sources_appendTail, sources_mapOwner, hs,
        SourceInventory.mapOwner_nil])).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict f tail))) := by
  have hwi := isInvisible_mapOwner owner f w hs hf
  have ha : ∀ r ∈ Layout.mapOwner owner a, f r.owner = false := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
    exact hf s.owner
  have hb : ∀ r ∈ Layout.mapOwner owner b, f r.owner = false := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
    exact hf s.owner
  obtain ⟨h, he⟩ := restrict_eval_eq_memCongr_of_isInvisible f
    ((w.mapOwner owner).appendTail tail) (by simp [sources_mapOwner, hs])
    (isInvisible_appendTail f _ hwi tail ha hb)
  have hi : Layout.restrict f (Layout.mapOwner owner a ++ tail) =
      Layout.restrict f tail := by
    rw [Layout.restrict_append, restrict_mapOwner_eq_nil owner f a hf, List.nil_append]
  have ho : Layout.restrict f (Layout.mapOwner owner b ++ tail) =
      Layout.restrict f tail := by
    rw [Layout.restrict_append, restrict_mapOwner_eq_nil owner f b hf, List.nil_append]
  exact (heq_of_eq he).trans (memCongr_heq_id hi ho h)
end Word

namespace PreparedSourceGate
/-- The actual residual of a prepared gate, with all its spectators, leaves
any nonparticipating party unchanged. This holds for each actual branch separately.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_remaining_appendTail_eval_eq_id_of_not_participating
    {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b)
    (tail : Layout P) (p : P)
    (hp : p ∉ (SourceCircuit.gate owner G tail).participants ()) (ξ : ι) :
    HEq ((((G.remaining ξ).mapOwner owner).appendTail tail).restrict
      (SourceCircuit.partySelector p) (by simp [Word.sources_mapOwner, G.remaining_sources])).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict (SourceCircuit.partySelector p) tail))) := by
  classical
  refine Word.restrict_mapOwner_appendTail_eval_eq_id_of_disjoint owner
    (SourceCircuit.partySelector p) (G.remaining ξ) (G.remaining_sources ξ) ?_ tail
  intro q
  have hne : owner q ≠ p := by
    intro he
    apply hp
    change p ∈ Finset.univ.map owner
    rw [← he]
    exact Finset.mem_map_of_mem owner (Finset.mem_univ q)
  simp only [SourceCircuit.partySelector, hne, decide_false]

/-- At a nonparticipating party, the actual prepared residual with arbitrary
spectators is independent of every branch label of this gate.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_remaining_appendTail_eq_of_not_participating
    {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b)
    (tail : Layout P) (p : P)
    (hp : p ∉ (SourceCircuit.gate owner G tail).participants ()) (ξ ζ : ι) :
    ((((G.remaining ξ).mapOwner owner).appendTail tail).restrict
      (SourceCircuit.partySelector p) (by simp [Word.sources_mapOwner, G.remaining_sources])).eval =
    ((((G.remaining ζ).mapOwner owner).appendTail tail).restrict
      (SourceCircuit.partySelector p)
        (by simp [Word.sources_mapOwner, G.remaining_sources])).eval := by
  exact eq_of_heq
    ((G.restrict_remaining_appendTail_eval_eq_id_of_not_participating owner tail p hp ξ).trans
      (G.restrict_remaining_appendTail_eval_eq_id_of_not_participating owner tail p hp ζ).symm)
end PreparedSourceGate
end TNLean.PEPS.PairEffect
