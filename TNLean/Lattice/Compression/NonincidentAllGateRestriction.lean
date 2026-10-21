/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.DistributedSourceComposition
import TNLean.Lattice.Compression.LocalPartSpectatorOwnerExclusion
import TNLean.Lattice.Compression.WordOwnerAppendTailTransport

/-!
# The restriction of a gate away from its participating parties

In the all-party expansion, the remaining operations of a gate restrict to the
identity at any original party outside its participant set. Precisely that
party's spectator registers remain. If the participant set is empty, the whole
gate is retained at the exterior owner and no branch label is requested. This
includes an empty branch set and a vanishing coefficient sum.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 351–381, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]

private theorem restrict_localPart_eval_heq_of_word_heq {Q : Type} (f : Q → Bool)
    {a b a' b' : Layout Q} (w : Word a b) (v : Word a' b')
    (ha : a = a') (hb : b = b') (h : HEq w v) :
    HEq (w.localPart.restrict f w.sources_localPart).eval
      (v.localPart.restrict f v.sources_localPart).eval := by
  cases ha
  cases hb
  cases h
  rfl

/-- The exact retained-spectator operator identity, formed on arbitrary word
layouts before owner maps and branch data are substituted.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381,
409–434 and 565–588. -/
private def selectedSpectatorIdentity {Q : Type} {a b : Layout Q}
    (v : Word a b) (q : Q) (spectators : Layout Q) : Prop :=
  HEq (v.localPart.restrict (partySelector q) v.sources_localPart).eval
    (ContinuousLinearMap.id ℂ (Mem (Layout.atParty q spectators)))

/-- The retained-spectator identity after relabelling a spectator extension.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381,
409–434 and 565–588. -/
private abbrev relabelledSpectatorsIdentity {R Q : Type}
    (g : R → Q) {a b : Layout R} (u : Word a b) (tail : Layout R) (q : Q) : Prop :=
  selectedSpectatorIdentity ((u.appendTail tail).mapOwner g) q (Layout.mapOwner g tail)

/-- Restrict a relabelled spectator extension after comparing its constructed
words. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 351–381, 409–434 and 565–588. -/
private theorem restrict_relabelled_spectators_eval_heq_id {R Q : Type}
    (g : R → Q) {a b : Layout R} (u : Word a b) (tail : Layout R) (q : Q)
    (hu : q ∉ (u.mapOwner g).parties) :
    relabelledSpectatorsIdentity g u tail q := by
  have h := restrict_localPart_eval_heq_of_word_heq (partySelector q)
    ((u.appendTail tail).mapOwner g)
    ((u.mapOwner g).appendTail (Layout.mapOwner g tail))
    (Layout.mapOwner_append g a tail) (Layout.mapOwner_append g b tail)
    (Word.mapOwner_appendTail_heq g u tail)
  exact h.trans
    (Word.restrict_localPart_appendTail_eval_heq_id_of_not_mem_parties
      (u.mapOwner g) q hu (Layout.mapOwner g tail))

omit [Fintype C] in
/-- Every original party outside the image of a participant embedding retains
only its spectators, for an arbitrary branch word. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 351–381, 409–434 and 565–588. -/
private theorem restrict_embedded_branch_spectators_eval_heq_id
    (owner : C ↪ P) {a b : Layout C} (u : Word a b) (tail : Layout P) (p : P)
    (howner : ∀ t, owner t ≠ p) :
    let all := affectedOwner (fun _ : P => true)
    let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
    relabelledSpectatorsIdentity all (u.mapOwner owner) tail q := by
  classical
  intro all q
  have hcore : q ∉ ((u.mapOwner owner).mapOwner all).parties := by
    intro hq
    rw [Word.parties_mapOwner, Word.parties_mapOwner] at hq
    simp only [Finset.mem_image] at hq
    obtain ⟨z, ⟨t, _, htz⟩, hzq⟩ := hq
    have he : all (owner t) = q := htz.symm ▸ hzq
    exact howner t (by simpa [all, q, affectedOwner] using he)
  exact restrict_relabelled_spectators_eval_heq_id
    (R := P) (Q := Option {_p : P // true = true})
    (a := Layout.mapOwner owner a) (b := Layout.mapOwner owner b)
    all (u.mapOwner owner) tail q hcore

omit [Fintype C] in
/-- A structural equality with an embedded spectator extension gives the same
restricted remaining operator. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–381, 409–434 and 565–588. -/
private theorem restrict_embedded_branch_spectators_eval_heq_id_of_eq
    (owner : C ↪ P) {a b : Layout C} (u : Word a b) (tail : Layout P) (p : P)
    (howner : ∀ t, owner t ≠ p)
    (v : Word
      (Layout.mapOwner (affectedOwner (fun _ : P => true))
        (Layout.mapOwner owner a ++ tail))
      (Layout.mapOwner (affectedOwner (fun _ : P => true))
        (Layout.mapOwner owner b ++ tail)))
    (hv : v = (((u.mapOwner owner).appendTail tail).mapOwner
      (affectedOwner (fun _ : P => true)))) :
    let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
    selectedSpectatorIdentity v q
      (Layout.mapOwner (affectedOwner (fun _ : P => true)) tail) := by
  classical
  intro q
  exact Eq.mpr (congrArg (fun z ↦ selectedSpectatorIdentity z q
    (Layout.mapOwner (affectedOwner (fun _ : P => true)) tail)) hv)
    (restrict_embedded_branch_spectators_eval_heq_id
    (P := P) (C := C) (a := a) (b := b) owner u tail p howner)

/-- An original party outside a gate's participants retains only its mapped
spectator registers in the actual all-party branch. The restriction of the
remaining operations is the identity on those spectators. No label is chosen
when the participant set is empty.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381,
409–434 and 565–588. -/
theorem restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (howner : ∀ t, owner t ≠ p)
    (ξ : Choices (fun _ : P => true) (.gate owner G tail)) :
    let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
    let v := partialWord (fun _ : P => true) (.gate owner G tail) ξ
    HEq (v.localPart.restrict (partySelector q) v.sources_localPart).eval
      (ContinuousLinearMap.id ℂ
        (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P => true)) tail)))) := by
  classical
  let all := affectedOwner (fun _ : P => true)
  let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
  let f := partySelector q
  by_cases ht : ∃ _t : C, true = true
  · let e : Choices (fun _ : P => true) (.gate owner G tail) ≃ ι :=
      Equiv.cast (by simp only [Choices]; exact ite_eq_left ⟨ht.choose, by trivial⟩)
    let i := e ξ
    have hw : partialWord (fun _ : P => true) (.gate owner G tail) ξ =
        (((G.branchWord i).mapOwner owner).appendTail tail).mapOwner all := by
      unfold partialWord
      rw [dite_eq_left ht]
      rfl
    exact restrict_embedded_branch_spectators_eval_heq_id_of_eq
      (P := P) (C := C) (a := a) (b := b) owner (G.branchWord i) tail p howner
      (partialWord (fun _ : P => true) (.gate owner G tail) ξ) hw
  · have hw : partialWord (fun _ : P => true) (.gate owner G tail) ξ =
        Word.groupedBlockMap all none (Layout.mapOwner owner a) (Layout.mapOwner owner b)
          (Layout.affectedOwner_mapOwner_eq_none (fun _ : P => true) owner ht a)
          (Layout.affectedOwner_mapOwner_eq_none (fun _ : P => true) owner ht b)
          (G.evalAtOwners owner) tail := by
      unfold partialWord
      rw [dite_eq_right ht]
    rw [hw]
    have hs : (Word.groupedBlockMap all none (Layout.mapOwner owner a)
        (Layout.mapOwner owner b)
        (Layout.affectedOwner_mapOwner_eq_none (fun _ : P => true) owner ht a)
        (Layout.affectedOwner_mapOwner_eq_none (fun _ : P => true) owner ht b)
        (G.evalAtOwners owner) tail).sources = [] := by
      simp only [Word.groupedBlockMap, Word.sources_castLayouts, Word.sources]
    refine (Word.restrict_localPart_eval_heq_of_sources_nil f _ hs).trans ?_
    unfold Word.groupedBlockMap
    rw [Word.restrict_castLayouts f _ _ _ rfl]
    exact (Word.eval_castLayouts_heq _ _ _).trans
      (Word.restrict_localMap_false_eval_heq f none _ _ _ _
        (by simp [f, q, partySelector]))

end TNLean.PEPS.PairEffect.SourceCircuit
