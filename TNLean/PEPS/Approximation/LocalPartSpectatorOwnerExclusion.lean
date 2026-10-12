/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LocalPartFrameListRestriction
import TNLean.PEPS.Approximation.SourceFreeLocalPart
import TNLean.PEPS.Approximation.WordAppendTailRestriction
import TNLean.PEPS.Approximation.SourceWordParties
import TNLean.PEPS.Approximation.PartyTensorMaps
import TNLean.PEPS.Approximation.LayoutExcludedOwners
import TNLean.PEPS.Approximation.WordEvaluationTransport

/-!
# Spectators at an owner excluded from the remaining operations

Let a composition, possibly containing pair sources, have no participating
operation at a given party. After adjoining arbitrary spectator registers, the
remaining operations restrict to the identity on that party's spectators.
The proof restricts the actual source-register exchanges and chronological
operations separately. No source vector is cancelled.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 351–381, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word
open ContinuousLinearMap
variable {P : Type}

private theorem restrict_localPart_comp_id (f : P → Bool) {a b c : Layout P}
    (w : Word a b) (v : Word b c) (T : Layout P)
    (ha : Layout.restrict f a = T) (hb : Layout.restrict f b = T)
    (hc : Layout.restrict f c = T)
    (hw : Layout.restrict f w.sources.layout = [])
    (hv : Layout.restrict f v.sources.layout = [])
    (hew : HEq (w.localPart.restrict f w.sources_localPart).eval (Word.id T).eval)
    (hev : HEq (v.localPart.restrict f v.sources_localPart).eval (Word.id T).eval) :
    HEq ((w.comp v).localPart.restrict f (w.comp v).sources_localPart).eval
      (Word.id T).eval := by
  have hraw : ((frameList v.sources.layout w.localPart).comp v.localPart).sources = [] := by
    simp only [sources, sources_frameList, sources_localPart, List.nil_append]
  have hleft := (restrict_frameList_eval_heq_of_eq_nil f v.sources.layout hv
    w.localPart w.sources_localPart).trans hew
  have hcomp := eval_comp_heq
    ((frameList v.sources.layout w.localPart).restrict f
      ((sources_frameList w.localPart v.sources.layout).trans w.sources_localPart))
    (v.localPart.restrict f v.sources_localPart) (Word.id T) (Word.id T)
    (by simp only [Layout.restrict_append, hv, hw, ha, List.nil_append])
    (by simp only [Layout.restrict_append, hv, hb, List.nil_append]) hc hleft hev
  unfold localPart
  exact (restrict_castInput_eval_heq f _ _ hraw).trans
    (hcomp.trans (heq_of_eq (ContinuousLinearMap.comp_id (Word.id T).eval)))

private theorem frameList_eval_heq_id_of_empty {a b : Layout P} (w : Word a b)
    (ha : a = []) (hb : b = []) (he : HEq w.eval (Word.id (P := P) []).eval)
    (tail : Layout P) : HEq (frameList tail w).eval (Word.id tail).eval := by
  cases ha
  cases hb
  induction tail with
  | nil => exact he
  | cons r tail ih =>
      have h := eval_frame_heq r (frameList tail w) (Word.id tail)
        (List.append_nil tail) (List.append_nil tail) ih
      exact h.trans (heq_of_eq (ContinuousLinearMap.lTensor_id r.space))

private def twoBlockExchange (a b : Layout P) : Word (a ++ b) (b ++ a) :=
  (exchangeBlocks a b []).castLayouts (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a))

private theorem sources_twoBlockExchange (a b : Layout P) :
    (twoBlockExchange a b).sources = [] := by
  simp only [twoBlockExchange, sources_castLayouts, sources_exchangeBlocks]

private theorem restrict_twoBlockExchange_eval_heq (f : P → Bool) (a b : Layout P) :
    HEq ((twoBlockExchange a b).restrict f (sources_twoBlockExchange a b)).eval
      (twoBlockExchange (Layout.restrict f a) (Layout.restrict f b)).eval := by
  unfold twoBlockExchange
  rw [restrict_castLayouts f (exchangeBlocks a b [])
    (congrArg (a ++ ·) (List.append_nil b))
    (congrArg (b ++ ·) (List.append_nil a)) (sources_exchangeBlocks a b [])]
  exact (eval_castLayouts_heq
    ((exchangeBlocks a b []).restrict f (sources_exchangeBlocks a b [])) _ _).trans
      ((restrict_exchangeBlocks_eval_heq f a b []).trans
        (eval_castLayouts_heq
          (exchangeBlocks (Layout.restrict f a) (Layout.restrict f b) [])
          (congrArg (Layout.restrict f a ++ ·) (List.append_nil (Layout.restrict f b)))
          (congrArg (Layout.restrict f b ++ ·) (List.append_nil (Layout.restrict f a)))).symm)

private theorem exchangeBlocks_nil_left_eval (b tail : Layout P) :
    (exchangeBlocks [] b tail).eval = (Word.id (b ++ tail)).eval := by
  induction b with
  | nil => rfl
  | cons r b ih =>
      have ih' : (exchangeBlocks [] b tail).eval =
          ContinuousLinearMap.id ℂ (Mem (b ++ tail)) := ih
      change ((exchangeBlocks [] b tail).eval).lTensor r.space ∘L
        ContinuousLinearMap.id ℂ (Mem (r :: (b ++ tail))) =
          ContinuousLinearMap.id ℂ (Mem (r :: (b ++ tail)))
      rw [ContinuousLinearMap.comp_id, ih']
      exact ContinuousLinearMap.lTensor_id (𝕜 := ℂ) (E := Mem (b ++ tail)) r.space

private theorem twoBlockExchange_nil_left_eval_heq (b : Layout P) :
    HEq (twoBlockExchange [] b).eval (Word.id b).eval := by
  unfold twoBlockExchange
  exact (eval_castLayouts_heq _ _ _).trans
    ((heq_of_eq (exchangeBlocks_nil_left_eval b [])).trans
      (eval_id_heq (List.append_nil b)))

private theorem twoBlockExchange_nil_right_eval_heq (a : Layout P) :
    HEq (twoBlockExchange a []).eval (Word.id a).eval := by
  unfold twoBlockExchange
  exact (eval_castLayouts_heq _ _ _).trans (eval_id_heq (List.append_nil a))

/-- A party absent from the participating parties of a word retains only its
spectator registers. The actual remaining operations restrict to the identity
on these spectators, for arbitrary pair sources and spectator memories.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_localPart_appendTail_eval_heq_id_of_not_mem_parties {a b : Layout P}
    (u : Word a b) (p : P) (hp : p ∉ u.parties) (tail : Layout P) :
    HEq (((u.appendTail tail).localPart.restrict (partySelector p)
      (u.appendTail tail).sources_localPart).eval)
      (ContinuousLinearMap.id ℂ (Mem (Layout.atParty p tail))) := by
  classical
  let f := partySelector p
  let T := Layout.restrict f tail
  have hretained (L : Layout P) (hL : ∀ r ∈ L, r.owner ∈ u.parties) :
      Layout.restrict f L = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    have hne : r.owner ≠ p := fun h => hp (h ▸ hL r hr)
    simpa only [f, partySelector, decide_eq_true_eq] using hne
  have ha : Layout.restrict f a = [] := hretained a u.owners_mem_parties.1
  have hb : Layout.restrict f b = [] := hretained b u.owners_mem_parties.2
  have hinput : Layout.restrict f (u.sources.layout ++ a) = [] :=
    hretained _ (by
      intro r hr
      simpa only [parties_localPart] using u.localPart.owners_mem_parties.1 r hr)
  have hs : Layout.restrict f u.sources.layout = [] := by
    exact (List.append_eq_nil_iff.mp
      (by simpa only [Layout.restrict_append] using hinput)).1
  have hparties : (u.localPart.restrict f u.sources_localPart).parties = ∅ := by
    rw [parties_restrict, parties_localPart]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hq, hsel⟩ := Finset.mem_filter.mp hq
    have hqp : q = p := by simpa only [f, partySelector, decide_eq_true_eq] using hsel
    exact hp (hqp ▸ hq)
  have hcore : HEq (u.localPart.restrict f u.sources_localPart).eval (Word.id (P := P) []).eval :=
    (eq_nil_and_eval_eq_id_of_parties_eq_empty _ hparties).2.2
  let A := twoBlockExchange a tail
  let V := frameList tail u
  let Z := twoBlockExchange tail b
  have hA : HEq (A.localPart.restrict f A.sources_localPart).eval (Word.id T).eval := by
    have h := (restrict_localPart_eval_heq_of_sources_nil f A
      (sources_twoBlockExchange _ _)).trans (restrict_twoBlockExchange_eval_heq f _ _)
    rw [ha] at h
    exact h.trans (twoBlockExchange_nil_left_eval_heq T)
  have hZ : HEq (Z.localPart.restrict f Z.sources_localPart).eval (Word.id T).eval := by
    have h := (restrict_localPart_eval_heq_of_sources_nil f Z
      (sources_twoBlockExchange _ _)).trans (restrict_twoBlockExchange_eval_heq f _ _)
    rw [hb] at h
    exact h.trans (twoBlockExchange_nil_right_eval_heq T)
  have hV : HEq (V.localPart.restrict f V.sources_localPart).eval (Word.id T).eval :=
    (restrict_localPart_frameList_eval_heq f tail u hs).trans
      (frameList_eval_heq_id_of_empty (u.localPart.restrict f u.sources_localPart)
        hinput hb hcore T)
  have hsA : Layout.restrict f A.sources.layout = [] := by
    rw [sources_twoBlockExchange]; rfl
  have hsV : Layout.restrict f V.sources.layout = [] := by
    simpa only [V, sources_frameList] using hs
  have hsZ : Layout.restrict f Z.sources.layout = [] := by
    rw [sources_twoBlockExchange]; rfl
  have hVZ := restrict_localPart_comp_id f V Z T
    (by simp only [T, Layout.restrict_append, ha, List.append_nil])
    (by simp only [T, Layout.restrict_append, hb, List.append_nil])
    (by simp only [T, Layout.restrict_append, hb, List.nil_append]) hsV hsZ hV hZ
  have hsVZ : Layout.restrict f (V.comp Z).sources.layout = [] := by
    simp only [sources, SourceInventory.layout_append, Layout.restrict_append,
      hsZ, hsV, List.nil_append]
  have h := restrict_localPart_comp_id f A (V.comp Z) T
    (by simp only [T, Layout.restrict_append, ha, List.nil_append])
    (by simp only [T, Layout.restrict_append, ha, List.append_nil])
    (by simp only [T, Layout.restrict_append, hb, List.nil_append]) hsA hsVZ hA hVZ
  change HEq ((A.comp (V.comp Z)).localPart.restrict f
    (A.comp (V.comp Z)).sources_localPart).eval (Word.id T).eval
  exact h

/-- A party outside the range of a core owner map retains only its spectator
registers. The restriction of the actual remaining operations is the identity
there, for arbitrary pair sources and arbitrary spectator memories.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_localPart_mapOwner_appendTail_eval_heq_id_of_disjoint {C : Type}
    (owner : C → P) (p : P) {a b : Layout C} (u : Word a b)
    (howner : ∀ c, owner c ≠ p) (tail : Layout P) :
    HEq ((((u.mapOwner owner).appendTail tail).localPart.restrict (partySelector p)
      ((u.mapOwner owner).appendTail tail).sources_localPart).eval)
      (ContinuousLinearMap.id ℂ (Mem (Layout.atParty p tail))) := by
  classical
  apply restrict_localPart_appendTail_eval_heq_id_of_not_mem_parties (u.mapOwner owner) p
    ?_ tail
  intro hp
  rw [parties_mapOwner] at hp
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hp
  exact howner c hc

end TNLean.PEPS.PairEffect.Word
