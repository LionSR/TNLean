/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyGateCircuit

/-!
# Monomials that leave the other registers in place

A monomial that uses only selected parties may still exchange two registers of unselected
parties, which acts nontrivially on their memory. This file gives a syntactic condition that
excludes this: every exchange of tensor factors moves a selected register
(`Word.SwapsMeet`, `PartyChain.SwapsMeet`). Under it, the complementary part of the monomial
acts as the identity (`PartyChain.fixesOutside_of_swapsMeet`), which is the hypothesis of
`PartyGate.exists_originalCircuit`. Collecting the registers of the participating parties
in front, as the bounded changes of §6 do, satisfies the condition.

## References

* Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
  lines 21–43; the gates of Proposition 7.1, `06-geometry.tex`, lines 574–583.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

namespace Word

/-- Preparing the pair sources first keeps the parties of the local maps. -/
theorem usesOnly_localPart {S : Set P} {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hw : w.UsesOnly S) :
    w.localPart.UsesOnly S := by
  induction w with
  | id => trivial
  | comp w w' ih ih' =>
      have key : ∀ {a b c : Layout P} (v : Word a b) (h : a = c), v.UsesOnly S →
          (v.castInput h).UsesOnly S := by
        intro a b c v h hv
        cases h
        exact hv
      have hfl : ∀ {a b : Layout P} (v : Word a b), v.UsesOnly S → (ℓ₀ : Layout P) →
          (frameList ℓ₀ v).UsesOnly S := by
        intro a b v hv ℓ₀
        induction ℓ₀ with
        | nil => exact hv
        | cons r ℓ₀ ihℓ => exact ihℓ
      exact key _ _ ⟨hfl _ (ih hw.1) _, ih' hw.2⟩
  | localMap => exact hw
  | source => trivial
  | swap => trivial
  | frame r w ih =>
      exact ⟨(isReordering_moveHead r _ _).usesOnly S, ih hw⟩

/-- Every exchange of tensor factors in the word moves a register of a selected party. -/
def SwapsMeet (f : P → Bool) : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → Prop
  | _, _, id _ => True
  | _, _, comp w w' => w.SwapsMeet f ∧ w'.SwapsMeet f
  | _, _, localMap .. => True
  | _, _, source .. => True
  | _, _, swap r r' _ => f r.owner = true ∨ f r'.owner = true
  | _, _, frame _ w => w.SwapsMeet f

theorem swapsMeet_frameList (f : P → Bool) {ℓ ℓ' : Layout P} {w : Word ℓ ℓ'}
    (hw : w.SwapsMeet f) : (ℓ₀ : Layout P) → (frameList ℓ₀ w).SwapsMeet f
  | [] => hw
  | _ :: ℓ₀ => swapsMeet_frameList f hw ℓ₀

theorem swapsMeet_castInput (f : P → Bool) {ℓ ℓ' ℓ₁ : Layout P} {w : Word ℓ ℓ'}
    (hw : w.SwapsMeet f) (h : ℓ = ℓ₁) : (w.castInput h).SwapsMeet f := by
  cases h
  exact hw

/-- Moving a register past selected registers meets the selection at every exchange. -/
theorem swapsMeet_moveHead (f : P → Bool) (r : Reg P) :
    (ℓ₀ tail : Layout P) → (∀ t ∈ ℓ₀, f t.owner = true) → (moveHead r ℓ₀ tail).SwapsMeet f
  | [], _, _ => trivial
  | t :: ℓ₀, tail, h =>
      ⟨swapsMeet_moveHead f r ℓ₀ tail fun t' ht' => h t' (List.mem_cons_of_mem _ ht'),
        Or.inl (h t List.mem_cons_self)⟩

/-- Preparing the pair sources first keeps the condition when the sources join selected
parties: the exchanges added by `localPart` move a register past fresh selected registers. -/
theorem swapsMeet_localPart (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) (hw : w.SwapsMeet f) :
    w.localPart.SwapsMeet f := by
  induction w with
  | id => trivial
  | comp w w' ih ih' =>
      have hS' : ∀ s ∈ w'.sources, f s.left = true ∧ f s.right = true :=
        fun s hs => hS s (List.mem_append_left _ hs)
      have hS₁ : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true :=
        fun s hs => hS s (List.mem_append_right _ hs)
      refine swapsMeet_castInput f ?_ _
      exact ⟨swapsMeet_frameList f (ih hS₁ hw.1) _, ih' hS' hw.2⟩
  | localMap => trivial
  | source => trivial
  | swap => exact hw
  | frame r w ih =>
      exact ⟨swapsMeet_moveHead f r _ _ (SourceInventory.owner_selected_of_mem_layout hS),
        ih hS hw⟩

private theorem id_heq_id {a b : Layout P} (h : a = b) :
    HEq (ContinuousLinearMap.id ℂ (Mem a)) (ContinuousLinearMap.id ℂ (Mem b)) := by
  subst h
  rfl

/-- A composition of two maps, each the identity up to layout identification, is the identity
up to layout identification. -/
theorem comp_heq_id {a b c : Layout P} (hab : a = b) (hbc : b = c)
    (A : Mem a →L[ℂ] Mem b) (B : Mem b →L[ℂ] Mem c)
    (hA : HEq A (ContinuousLinearMap.id ℂ (Mem a)))
    (hB : HEq B (ContinuousLinearMap.id ℂ (Mem b))) :
    HEq (B ∘L A) (ContinuousLinearMap.id ℂ (Mem a)) := by
  subst hab
  subst hbc
  rw [eq_of_heq hA, eq_of_heq hB]
  rfl

private theorem lTensor_heq_id (r : Reg P) {a b : Layout P} (h : a = b) (A : Mem a →L[ℂ] Mem b)
    (hA : HEq A (ContinuousLinearMap.id ℂ (Mem a))) :
    HEq (A.lTensor r.space) (ContinuousLinearMap.id ℂ (Mem (r :: a))) := by
  subst h
  rw [eq_of_heq hA]
  exact heq_of_eq (lTensor_id _)

/-- **The complementary restriction of a word meeting the selection is the identity.** A word
without pair sources whose local maps act at selected parties and whose exchanges move selected
registers restricts, on the unselected registers, to the identity. -/
theorem restrict_not_eval_heq_id (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) (hU : w.UsesOnly {p | f p = true}) (hM : w.SwapsMeet f) :
    Layout.restrict (fun p ↦ !f p) ℓ = Layout.restrict (fun p ↦ !f p) ℓ' ∧
      HEq (w.restrict (fun p ↦ !f p) hs).eval
        (ContinuousLinearMap.id ℂ (Mem (Layout.restrict (fun p ↦ !f p) ℓ))) := by
  induction w with
  | id ℓ => exact ⟨rfl, HEq.rfl⟩
  | comp w w' ih ih' =>
      obtain ⟨h₁, e₁⟩ := ih (List.append_eq_nil_iff.mp hs).2 hU.1 hM.1
      obtain ⟨h₂, e₂⟩ := ih' (List.append_eq_nil_iff.mp hs).1 hU.2 hM.2
      exact ⟨h₁.trans h₂, comp_heq_id h₁ h₂ _ _ e₁ e₂⟩
  | @localMap p ℓ₁ ℓ₂ h₁ h₂ U tail =>
      have hfp : f p = true := hU
      have hp : (fun p ↦ !f p) p = false := by simp [hfp]
      have ha := Layout.restrict_eq_nil_of_owner (fun p ↦ !f p) h₁ hp
      have hb := Layout.restrict_eq_nil_of_owner (fun p ↦ !f p) h₂ hp
      refine ⟨by rw [Layout.restrict_append, Layout.restrict_append, ha, hb], ?_⟩
      exact (restrict_localMap_false_eval_heq _ p h₁ h₂ U tail hp).trans
        (id_heq_id (by rw [Layout.restrict_append, ha, List.nil_append]))
  | source => exact absurd hs (by simp [sources])
  | swap r r' tail =>
      rcases hM with hr | hr'
      · have hr₀ : (fun p ↦ !f p) r.owner = false := by simp [hr]
        cases hr'₀ : (fun p ↦ !f p) r'.owner
        · refine ⟨by simp [Layout.restrict_cons, hr₀, hr'₀], ?_⟩
          exact (restrict_swap_false_false_eval_heq _ r r' tail hr₀ hr'₀).trans
            (id_heq_id (by simp [Layout.restrict_cons, hr₀, hr'₀]))
        · refine ⟨by simp [Layout.restrict_cons, hr₀, hr'₀], ?_⟩
          exact (restrict_swap_false_true_eval_heq _ r r' tail hr₀ hr'₀).trans
            (id_heq_id (by simp [Layout.restrict_cons, hr₀, hr'₀]))
      · have hr'₀ : (fun p ↦ !f p) r'.owner = false := by simp [hr']
        cases hr₀ : (fun p ↦ !f p) r.owner
        · refine ⟨by simp [Layout.restrict_cons, hr₀, hr'₀], ?_⟩
          exact (restrict_swap_false_false_eval_heq _ r r' tail hr₀ hr'₀).trans
            (id_heq_id (by simp [Layout.restrict_cons, hr₀, hr'₀]))
        · refine ⟨by simp [Layout.restrict_cons, hr₀, hr'₀], ?_⟩
          exact (restrict_swap_true_false_eval_heq _ r r' tail hr₀ hr'₀).trans
            (id_heq_id (by simp [Layout.restrict_cons, hr₀, hr'₀]))
  | frame r w ih =>
      obtain ⟨h, e⟩ := ih hs hU hM
      cases hr : (fun p ↦ !f p) r.owner
      · refine ⟨by simp [Layout.restrict_cons, hr, h], ?_⟩
        exact (restrict_frame_false_eval_heq _ r w hs hr).trans
          (e.trans (id_heq_id (by simp [Layout.restrict_cons, hr])))
      · refine ⟨by simp [Layout.restrict_cons, hr, h], ?_⟩
        exact (restrict_frame_true_eval_heq _ r w hs hr).trans
          ((lTensor_heq_id r h _ e).trans (id_heq_id (by simp [Layout.restrict_cons, hr])))

private theorem castInput_eval_heq {ℓ ℓ' ℓ₁ : Layout P} (w : Word ℓ ℓ') (h : ℓ = ℓ₁) :
    HEq (w.castInput h).eval w.eval := by
  cases h
  rfl

/-- The complementary part of a word meeting the selection is the identity. -/
theorem complementPart_eval_heq_id (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hU : w.UsesOnly {p | f p = true}) (hM : w.SwapsMeet f) :
    Layout.restrict (fun p ↦ !f p) ℓ = Layout.restrict (fun p ↦ !f p) ℓ' ∧
      HEq (w.complementPart f (w.sources_selected_of_usesOnly hU)).eval
        (ContinuousLinearMap.id ℂ (Mem (Layout.restrict (fun p ↦ !f p) ℓ))) := by
  have hS := w.sources_selected_of_usesOnly hU
  have hlp := restrict_not_eval_heq_id f w.localPart w.sources_localPart
    (usesOnly_localPart w hU) (swapsMeet_localPart f w hS hM)
  have hin := SourceInventory.restrict_not_layout_append hS ℓ
  refine ⟨hin.symm.trans hlp.1, ?_⟩
  exact (castInput_eval_heq _ _).trans (hlp.2.trans (id_heq_id hin))

end Word

namespace PartyChain

/-- Every exchange of tensor factors in the monomial moves a register of a selected party. -/
def SwapsMeet (f : P → Bool) : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Prop
  | _, _, final w => w.SwapsMeet f
  | _, _, effect _ _ _ _ w _ rest => w.SwapsMeet f ∧ rest.SwapsMeet f

private theorem castLayouts_eval_heq {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ') (h : ℓ = a)
    (h' : ℓ' = b) : HEq (w.castLayouts h h').eval w.eval :=
  Word.eval_castLayouts_heq w h h'

theorem complementPart_eval_heq_id (f : P → Bool) {ℓX ℓY : Layout P} (M : PartyChain ℓX ℓY)
    (hU : M.UsesOnly {p | f p = true}) (hM : M.SwapsMeet f) :
    Layout.restrict (fun p ↦ !f p) ℓX = Layout.restrict (fun p ↦ !f p) ℓY ∧
      HEq (M.complementPart f hU).eval
        (ContinuousLinearMap.id ℂ (Mem (Layout.restrict (fun p ↦ !f p) ℓX))) := by
  induction M with
  | final w => exact w.complementPart_eval_heq_id f hU hM
  | effect hpq α β ℓS w η rest ih =>
      obtain ⟨h₁, e₁⟩ := w.complementPart_eval_heq_id f hU.2.2.1 hM.1
      obtain ⟨h₂, e₂⟩ := ih hU.2.2.2 hM.2
      have hnp := Layout.restrict_not_pair hU.1 hU.2.1 α β ℓS
      refine ⟨h₁.trans (hnp.trans h₂), ?_⟩
      exact Word.comp_heq_id (h₁.trans hnp) h₂ _ _
        ((castLayouts_eval_heq _ _ _).trans e₁) e₂

end PartyChain

/-- A map that is the identity up to a layout identification is that identification. -/
theorem eq_isoL_memCongr_of_heq_id {a b : Layout P} (h : a = b) (F : Mem a →L[ℂ] Mem b)
    (hF : HEq F (ContinuousLinearMap.id ℂ (Mem a))) : F = isoL (Layout.memCongr h) := by
  subst h
  rw [eq_of_heq hF]
  rfl

/-- **Monomials meeting the selection fix the other registers.** A monomial that uses only the
parties of `S` and moves a register of `S` at each exchange of tensor factors leaves the other
registers in place. -/
theorem PartyChain.fixesOutside_of_swapsMeet [DecidableEq P] (S : Finset P) {ℓX ℓY : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓX =
      Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓY)
    (M : PartyChain ℓX ℓY) (hU : M.UsesOnly {p | decide (p ∈ S) = true})
    (hM : M.SwapsMeet fun p ↦ decide (p ∈ S)) : M.FixesOutside S h :=
  ⟨hU, eq_isoL_memCongr_of_heq_id h _ (M.complementPart_eval_heq_id _ hU hM).2⟩

end TNLean.PEPS.PairEffect
