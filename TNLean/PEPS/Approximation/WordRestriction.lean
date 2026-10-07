/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePreparation
import TNLean.PEPS.Approximation.PartyPartition

/-!
# Restricting a word to selected parties

A word without pair sources restricts to any collection of parties: retain their local
maps and their registers, preserving the order of the retained operations. The resulting
word is allowed whenever the original word is allowed.

The finite set of participating parties includes the named party of every local map,
even when its input and output layouts are empty. Thus scalar local operations are
retained in the subsequent tensor product over parties.

Source: polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`,
equation `eq:compression-source-gate`, lines 233–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-wordrestriction-word.castlayouts
Downstream declaration: TNLean.PEPS.PairEffect.Word.castLayouts

Provenance-ID: 8769-wordrestriction-word.sources_castlayouts
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_castLayouts

Provenance-ID: 8769-wordrestriction-word.isallowed_castlayouts
Downstream declaration: TNLean.PEPS.PairEffect.Word.isAllowed_castLayouts

Provenance-ID: 8769-wordrestriction-word.eval_castlayouts_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_castLayouts_heq

Provenance-ID: 8769-wordrestriction-word.eval_castlayouts
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_castLayouts

Provenance-ID: 8769-wordrestriction-word.restrict
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict

Provenance-ID: 8769-wordrestriction-word.sources_restrict
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_restrict

Provenance-ID: 8769-wordrestriction-word.isallowed_restrict
Downstream declaration: TNLean.PEPS.PairEffect.Word.isAllowed_restrict

Provenance-ID: 8769-wordrestriction-word.restrict_localmap_true_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_localMap_true_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_localmap_false_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_localMap_false_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_swap_true_true_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_swap_true_true_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_swap_true_false_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_swap_true_false_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_swap_false_true_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_swap_false_true_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_swap_false_false_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_swap_false_false_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_frame_true_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_frame_true_eval_heq

Provenance-ID: 8769-wordrestriction-word.restrict_frame_false_eval_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.restrict_frame_false_eval_heq

Provenance-ID: 8769-wordrestriction-word.parties
Downstream declaration: TNLean.PEPS.PairEffect.Word.parties

Provenance-ID: 8769-wordrestriction-word.parties_castlayouts
Downstream declaration: TNLean.PEPS.PairEffect.Word.parties_castLayouts

Provenance-ID: 8769-wordrestriction-word.owners_mem_parties
Downstream declaration: TNLean.PEPS.PairEffect.Word.owners_mem_parties

Provenance-ID: 8769-wordrestriction-word.parties_restrict
Downstream declaration: TNLean.PEPS.PairEffect.Word.parties_restrict

Provenance-ID: 8769-wordrestriction-word.eq_nil_and_eval_eq_id_of_parties_eq_empty
Downstream declaration: TNLean.PEPS.PairEffect.Word.eq_nil_and_eval_eq_id_of_parties_eq_empty
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open ContinuousLinearMap

variable {P : Type}

namespace Word

/-- Identify equal input and output layouts without adding an operation. -/
def castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    Word a b := h ▸ h' ▸ w

@[simp] theorem sources_castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').sources = w.sources := by
  cases h
  cases h'
  rfl

@[simp] theorem isAllowed_castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').IsAllowed ↔ w.IsAllowed := by
  cases h
  cases h'
  rfl

theorem eval_castLayouts_heq {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : HEq (w.castLayouts h h').eval w.eval := by
  cases h
  cases h'
  rfl

/-- Identifying equal layouts conjugates the operator by their canonical isometries. -/
theorem eval_castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) :
    (w.castLayouts h h').eval =
      isoL (Layout.memCongr h') ∘L w.eval ∘L isoL (Layout.memCongr h).symm := by
  cases h
  cases h'
  rfl

/-- Retain the registers and chronological local operations of selected parties.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
def restrict (f : P → Bool) : {ℓ ℓ' : Layout P} → (w : Word ℓ ℓ') →
    w.sources = [] → Word (Layout.restrict f ℓ) (Layout.restrict f ℓ')
  | _, _, id ℓ, _ => id (Layout.restrict f ℓ)
  | _, _, comp w w', hs =>
      comp (restrict f w (List.append_eq_nil_iff.mp hs).2)
        (restrict f w' (List.append_eq_nil_iff.mp hs).1)
  | _, _, @localMap _ p ℓ₁ ℓ₂ h₁ h₂ U tail, _ =>
      if hp : f p = true then
        (localMap p h₁ h₂ U (Layout.restrict f tail)).castLayouts
          (by rw [Layout.restrict_append, Layout.restrict_eq_self_of_owner f h₁ hp])
          (by rw [Layout.restrict_append, Layout.restrict_eq_self_of_owner f h₂ hp])
      else
        (id (Layout.restrict f tail)).castLayouts
          (by rw [Layout.restrict_append,
            Layout.restrict_eq_nil_of_owner f h₁ (Bool.eq_false_iff.mpr hp), List.nil_append])
          (by rw [Layout.restrict_append,
            Layout.restrict_eq_nil_of_owner f h₂ (Bool.eq_false_iff.mpr hp), List.nil_append])
  | _, _, source _ _ _ _ _, hs => nomatch hs
  | _, _, swap r r' tail, _ =>
      if hr : f r.owner = true then
        if hr' : f r'.owner = true then
          (swap r r' (Layout.restrict f tail)).castLayouts
            (by simp [Layout.restrict_cons, hr, hr']) (by simp [Layout.restrict_cons, hr, hr'])
        else
          (id (r :: Layout.restrict f tail)).castLayouts
            (by simp [Layout.restrict_cons, hr, hr']) (by simp [Layout.restrict_cons, hr, hr'])
      else
        if hr' : f r'.owner = true then
          (id (r' :: Layout.restrict f tail)).castLayouts
            (by simp [Layout.restrict_cons, hr, hr']) (by simp [Layout.restrict_cons, hr, hr'])
        else
          (id (Layout.restrict f tail)).castLayouts
            (by simp [Layout.restrict_cons, hr, hr']) (by simp [Layout.restrict_cons, hr, hr'])
  | _, _, frame r w, hs =>
      if hr : f r.owner = true then
        (frame r (restrict f w hs)).castLayouts
          (by simp [Layout.restrict_cons, hr]) (by simp [Layout.restrict_cons, hr])
      else
        (restrict f w hs).castLayouts
          (by simp [Layout.restrict_cons, hr]) (by simp [Layout.restrict_cons, hr])


/-- Restriction does not introduce a pair source. -/
@[simp] theorem sources_restrict (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) : (restrict f w hs).sources = [] := by
  induction w with
  | id => rfl
  | comp w w' ih ih' => simp only [restrict, sources, ih, ih', List.append_nil]
  | localMap => simp only [restrict]; split <;> simp [sources]
  | source => contradiction
  | swap => simp only [restrict]; split <;> split <;> simp [sources]
  | frame r w ih =>
      simp only [restrict]
      split <;> simpa only [sources_castLayouts, sources] using ih hs

/-- Restricting to selected parties preserves the contraction bound of every local map.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
theorem isAllowed_restrict (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) (hw : w.IsAllowed) : (restrict f w hs).IsAllowed := by
  induction w with
  | id => trivial
  | comp w w' ih ih' => exact ⟨ih _ hw.1, ih' _ hw.2⟩
  | localMap => simp only [restrict]; split <;> simp_all only [isAllowed_castLayouts, IsAllowed]
  | source => contradiction
  | swap => simp only [restrict]; split <;> split <;> simp [IsAllowed]
  | frame r w ih =>
      simp only [restrict]
      split <;> simpa only [isAllowed_castLayouts, IsAllowed] using ih hs hw


/-- A selected local map remains the same local map on the restricted spectator memory. -/
theorem restrict_localMap_true_eval_heq (f : P → Bool) (p : P) {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (U : Mem a →L[ℂ] Mem b) (tail : Layout P) (hp : f p = true) :
    HEq (restrict f (localMap p ha hb U tail) rfl).eval
      (localMap p ha hb U (Layout.restrict f tail)).eval := by
  simp only [restrict, dite_eq_left hp]
  exact eval_castLayouts_heq _ _ _

/-- An unselected local map leaves the selected memory unchanged. -/
theorem restrict_localMap_false_eval_heq (f : P → Bool) (p : P) {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (U : Mem a →L[ℂ] Mem b) (tail : Layout P) (hp : f p = false) :
    HEq (restrict f (localMap p ha hb U tail) rfl).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict f tail))) := by
  simp only [restrict, dite_eq_right (Bool.eq_false_iff.mp hp)]
  exact eval_castLayouts_heq _ _ _

/-- Exchanging two selected registers remains an exchange. -/
theorem restrict_swap_true_true_eval_heq (f : P → Bool) (r t : Reg P) (tail : Layout P)
    (hr : f r.owner = true) (ht : f t.owner = true) :
    HEq (restrict f (swap r t tail) rfl).eval
      (swap r t (Layout.restrict f tail)).eval := by
  simp only [restrict, dite_eq_left hr, dite_eq_left ht]
  exact eval_castLayouts_heq _ _ _

/-- Exchanging a selected register with an unselected one preserves the selected memory. -/
theorem restrict_swap_true_false_eval_heq (f : P → Bool) (r t : Reg P) (tail : Layout P)
    (hr : f r.owner = true) (ht : f t.owner = false) :
    HEq (restrict f (swap r t tail) rfl).eval
      (ContinuousLinearMap.id ℂ (Mem (r :: Layout.restrict f tail))) := by
  simp only [restrict, dite_eq_left hr, dite_eq_right (Bool.eq_false_iff.mp ht)]
  exact eval_castLayouts_heq _ _ _

/-- Exchanging an unselected register with a selected one preserves the selected memory. -/
theorem restrict_swap_false_true_eval_heq (f : P → Bool) (r t : Reg P) (tail : Layout P)
    (hr : f r.owner = false) (ht : f t.owner = true) :
    HEq (restrict f (swap r t tail) rfl).eval
      (ContinuousLinearMap.id ℂ (Mem (t :: Layout.restrict f tail))) := by
  simp only [restrict, dite_eq_right (Bool.eq_false_iff.mp hr), dite_eq_left ht]
  exact eval_castLayouts_heq _ _ _

/-- Exchanging two unselected registers leaves the selected memory unchanged. -/
theorem restrict_swap_false_false_eval_heq (f : P → Bool) (r t : Reg P) (tail : Layout P)
    (hr : f r.owner = false) (ht : f t.owner = false) :
    HEq (restrict f (swap r t tail) rfl).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.restrict f tail))) := by
  simp only [restrict, dite_eq_right (Bool.eq_false_iff.mp hr),
    dite_eq_right (Bool.eq_false_iff.mp ht)]
  exact eval_castLayouts_heq _ _ _

/-- Restricting a framed word retains a selected register. -/
theorem restrict_frame_true_eval_heq (f : P → Bool) (r : Reg P)
    {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hs : w.sources = []) (hr : f r.owner = true) :
    HEq (restrict f (frame r w) hs).eval ((restrict f w hs).eval.lTensor r.space) := by
  simp only [restrict, dite_eq_left hr]
  exact eval_castLayouts_heq _ _ _

/-- Restricting a framed word removes an unselected register. -/
theorem restrict_frame_false_eval_heq (f : P → Bool) (r : Reg P)
    {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hs : w.sources = []) (hr : f r.owner = false) :
    HEq (restrict f (frame r w) hs).eval (restrict f w hs).eval := by
  simp only [restrict, dite_eq_right (Bool.eq_false_iff.mp hr)]
  exact eval_castLayouts_heq _ _ _

/-- The finite set of parties occurring in registers or named local maps. A local map on
empty layouts still contributes its named party. Source: polynomial-PEPS manuscript,
`eq:compression-source-gate`, lines 233–251. -/
def parties : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → Finset P
  | _, _, id ℓ => by classical exact (ℓ.map Reg.owner).toFinset
  | _, _, comp w w' => by classical exact w.parties ∪ w'.parties
  | _, _, localMap p _ _ _ tail => by
      classical exact insert p (tail.map Reg.owner).toFinset
  | _, _, @source _ p q _ _ _ _ tail => by
      classical exact insert p (insert q (tail.map Reg.owner).toFinset)
  | _, _, swap r r' tail => by
      classical exact insert r.owner (insert r'.owner (tail.map Reg.owner).toFinset)
  | _, _, frame r w => by classical exact insert r.owner w.parties

@[simp] theorem parties_castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').parties = w.parties := by
  cases h
  cases h'
  rfl

/-- Every input or output register belongs to a party occurring in the word. -/
theorem owners_mem_parties {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (∀ r ∈ ℓ, r.owner ∈ w.parties) ∧ (∀ r ∈ ℓ', r.owner ∈ w.parties) := by
  classical
  induction w with
  | id ℓ =>
      constructor <;> intro r hr <;>
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hr)
  | comp w w' ih ih' =>
      exact ⟨fun r hr ↦ Finset.mem_union_left _ (ih.1 r hr),
        fun r hr ↦ Finset.mem_union_right _ (ih'.2 r hr)⟩
  | localMap p h₁ h₂ U tail =>
      constructor
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · simp [parties, h₁ r hr]
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hr))
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · simp [parties, h₂ r hr]
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hr))
  | source hpq U V η tail =>
      constructor
      · intro r hr
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hr)))
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with hr | hr | hr
        · simp [parties, hr]
        · simp [parties, hr]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hr)))
  | swap r r' tail =>
      constructor <;> intro s hs <;> simp only [List.mem_cons] at hs
      · rcases hs with hs | hs | hs
        · simp [parties, hs]
        · simp [parties, hs]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hs)))
      · rcases hs with hs | hs | hs
        · simp [parties, hs]
        · simp [parties, hs]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hs)))
  | frame r w ih =>
      constructor <;> intro s hs <;> simp only [List.mem_cons] at hs
      · rcases hs with hs | hs
        · simp [parties, hs]
        · exact Finset.mem_insert_of_mem (ih.1 s hs)
      · rcases hs with hs | hs
        · simp [parties, hs]
        · exact Finset.mem_insert_of_mem (ih.2 s hs)


private theorem owners_restrict [DecidableEq P] (f : P → Bool) (ℓ : Layout P) :
    (Layout.restrict f ℓ |>.map Reg.owner).toFinset =
      (ℓ.map Reg.owner).toFinset.filter (fun p ↦ f p) := by
  classical
  exact (congrArg List.toFinset (List.filter_map (f := Reg.owner) (p := f)
    (l := ℓ)).symm).trans (List.toFinset_filter _ _)

/-- The parties remaining after restriction are exactly the selected original parties. -/
theorem parties_restrict (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) :
    (restrict f w hs).parties = w.parties.filter (fun p ↦ f p) := by
  classical
  induction w with
  | id ℓ => exact owners_restrict f ℓ
  | comp w w' ih ih' => simp only [restrict, parties, ih, ih', Finset.filter_union]
  | localMap =>
      simp only [restrict]
      split <;> simp_all [parties, owners_restrict, Finset.filter_insert]
  | source => contradiction
  | swap =>
      simp only [restrict]
      split <;> split <;> simp_all [parties, owners_restrict, Finset.filter_insert]
  | frame r w ih =>
      simp only [restrict]
      split <;> simp only [parties_castLayouts, parties, ih hs] <;>
        simp_all [Finset.filter_insert]


/-- A word with no participating party acts as the identity on the empty memory.
The named party of every scalar local operation is included in `parties`. -/
theorem eq_nil_and_eval_eq_id_of_parties_eq_empty {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hp : w.parties = ∅) :
    ℓ = [] ∧ ℓ' = [] ∧ HEq w.eval (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  induction w with
  | id ℓ =>
      have hℓ : ℓ = [] := by simpa [parties] using hp
      subst ℓ
      exact ⟨rfl, rfl, HEq.rfl⟩
  | comp w w' ih ih' =>
      obtain ⟨ha, hb, h⟩ := ih (Finset.union_eq_empty.mp hp).1
      obtain ⟨_, hc, h'⟩ := ih' (Finset.union_eq_empty.mp hp).2
      refine ⟨ha, hc, ?_⟩
      cases ha
      cases hb
      cases hc
      simp only [eval, eq_of_heq h, eq_of_heq h', id_comp, heq_eq_eq]
  | localMap => simp [parties] at hp
  | source => simp [parties] at hp
  | swap => simp [parties] at hp
  | frame => simp [parties] at hp

end Word

end TNLean.PEPS.PairEffect
