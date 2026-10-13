/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentGateLabels
import TNLean.PEPS.Approximation.WordSelectedOwnerLocalPart
import TNLean.PEPS.Approximation.NonincidentAllGateRestriction
import TNLean.PEPS.Approximation.WordOwnerEvaluation

/-!
# A gate in the singleton and all-party partial expansions

The remaining operator selected at one original party is the same in the
all-party expansion and the singleton expansion projected from that very
choice. At an incident gate the original branch label is identical. At a
nonincident gate the singleton expansion retains the whole exterior operation;
its restriction to the selected party is the spectator identity. No label is
chosen at an untouched gate and no source preparation is cancelled.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap

private theorem id_heq_of_memory_eq {E F : HSpace} (h : E = F) :
    HEq (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F) := by
  cases h
  rfl

/-- Two words have the same selected remaining evaluation, with the source
proof supplied by each word. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–434 and 565–588. -/
def Word.IsSelectedLocalPartComparison {Q : Type}
    {a b c d : Layout Q} (f : Q → Bool) (u : Word a b) (v : Word c d) : Prop :=
  HEq (u.localPart.restrict f u.sources_localPart).eval
    (v.localPart.restrict f v.sources_localPart).eval

/-- The comparison of the two selected remaining words, with each source
proof supplied by its word argument. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–434 and 565–588. -/
private def selectedRemainingComparison {Q R S : Type} {a b : Layout Q} {c d : Layout R}
    (W : Word a b) (V : Word c d) (q : Q) (r : R) (lift : R → S) : Prop :=
  HEq (W.localPart.restrict (partySelector q) W.sources_localPart).eval
    ((V.localPart.restrict (partySelector r) V.sources_localPart).mapOwner lift).eval

/-- A canonical comparison of selected words also compares the second
word after changing its owners, provided the selected owner has one preimage.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434
and 565–588. -/
private theorem isSelectedLocalPartComparison_of_selectedRemainingComparison {Q R : Type}
    (lift : R → Q) (r : R) (q : Q) (hlift : ∀ z, lift z = q ↔ z = r)
    {a b : Layout Q} {c d : Layout R} (u : Word a b) (v : Word c d)
    (h : selectedRemainingComparison u v q r lift) :
    Word.IsSelectedLocalPartComparison (partySelector q) u (v.mapOwner lift) := by
  have hLift := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber
    lift r q hlift v
  exact h.trans hLift.symm

/-- Two relabellings with the same singleton original fibre give the same
selected remaining operation, after any further relabelling of the second
selected word. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 351–434 and 565–588. -/
private theorem selectedRemainingComparison_mapOwner {P Q R S : Type}
    (f : P → Q) (g : P → R) (lift : R → S) (p : P) (q : Q) (r : R)
    (hf : ∀ z, f z = q ↔ z = p) (hg : ∀ z, g z = r ↔ z = p)
    {a b : Layout P} (u : Word a b) :
    selectedRemainingComparison (u.mapOwner f) (u.mapOwner g) q r lift := by
  unfold selectedRemainingComparison
  let T := u.localPart.restrict (partySelector p) u.sources_localPart
  have hfWord := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber f p q hf u
  have hgWord := Word.restrict_localPart_mapOwner_eval_heq_of_singleton_fiber g p r hg u
  exact hfWord.trans ((Word.eval_mapOwner_heq f T).trans
    ((Word.eval_mapOwner_heq g T).symm.trans
      (hgWord.symm.trans (Word.eval_mapOwner_heq lift
        ((u.mapOwner g).localPart.restrict (partySelector r)
          (u.mapOwner g).sources_localPart)).symm)))

/-- Structural word equalities specialize the singleton-fibre comparison
without unfolding the branch construction in its operator comparison.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedRemainingComparison_of_mapOwner_eq {P Q R S : Type}
    (f : P → Q) (g : P → R) (lift : R → S) (p : P) (q : Q) (r : R)
    (hf : ∀ z, f z = q ↔ z = p) (hg : ∀ z, g z = r ↔ z = p)
    {a b : Layout P} (u : Word a b)
    (W : Word (Layout.mapOwner f a) (Layout.mapOwner f b))
    (V : Word (Layout.mapOwner g a) (Layout.mapOwner g b))
    (hW : W = u.mapOwner f) (hV : V = u.mapOwner g) :
    selectedRemainingComparison W V q r lift := by
  exact Eq.mpr (congrArg₂ (fun w v ↦ selectedRemainingComparison w v q r lift) hW hV)
    (selectedRemainingComparison_mapOwner f g lift p q r hf hg u)

/-- The same selected spectator memory gives the same identity operation
under two owner maps with one common singleton original fibre.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedRemainingComparison_of_spectator_id {P Q R S : Type}
    (f : P → Q) (g : P → R) (lift : R → S) (p : P) (q : Q) (r : R)
    (hf : ∀ z, f z = q ↔ z = p) (hg : ∀ z, g z = r ↔ z = p)
    (tail : Layout P) {a b : Layout Q} {c d : Layout R} (W : Word a b) (V : Word c d)
    (hW : HEq (W.localPart.restrict (partySelector q) W.sources_localPart).eval
      (Word.id (Layout.atParty q (Layout.mapOwner f tail))).eval)
    (hV : HEq (V.localPart.restrict (partySelector r) V.sources_localPart).eval
      (Word.id (Layout.atParty r (Layout.mapOwner g tail))).eval) :
    selectedRemainingComparison W V q r lift := by
  classical
  unfold selectedRemainingComparison
  have hsF : (fun z ↦ partySelector q (f z)) = partySelector p := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simpa only [partySelector, decide_eq_true_eq] using hf z
  have hsG : (fun z ↦ partySelector r (g z)) = partySelector p := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simpa only [partySelector, decide_eq_true_eq] using hg z
  have htF : Layout.atParty q (Layout.mapOwner f tail) =
      Layout.mapOwner f (Layout.restrict (partySelector p) tail) := by
    change Layout.restrict (partySelector q) (Layout.mapOwner f tail) = _
    rw [Layout.restrict_mapOwner, hsF]
  have htG : Layout.atParty r (Layout.mapOwner g tail) =
      Layout.mapOwner g (Layout.restrict (partySelector p) tail) := by
    change Layout.restrict (partySelector r) (Layout.mapOwner g tail) = _
    rw [Layout.restrict_mapOwner, hsG]
  have hMapped : HEq
      ((V.localPart.restrict (partySelector r) V.sources_localPart).mapOwner lift).eval
      (Word.id (Layout.atParty r (Layout.mapOwner g tail))).eval :=
    (Word.eval_mapOwner_heq lift _).trans hV
  have htailMem : Mem (Layout.atParty q (Layout.mapOwner f tail)) =
      Mem (Layout.atParty r (Layout.mapOwner g tail)) :=
    ((congrArg Mem htF).trans (Layout.mem_mapOwner f _)).trans
      ((congrArg Mem htG).trans (Layout.mem_mapOwner g _)).symm
  have hid : HEq (Word.id (Layout.atParty q (Layout.mapOwner f tail))).eval
      (Word.id (Layout.atParty r (Layout.mapOwner g tail))).eval :=
    id_heq_of_memory_eq htailMem
  exact hW.trans (hid.trans hMapped.symm)

/-- The selected spectator identity with the source-free local-part proof
supplied by the word itself. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–434 and 565–588. -/
private def selectedSpectatorIdentity {Q : Type} {a b : Layout Q}
    (v : Word a b) (q : Q) (tail : Layout Q) : Prop :=
  HEq (v.localPart.restrict (partySelector q) v.sources_localPart).eval
    (Word.id (Layout.atParty q tail)).eval

/-- Canonical selected-spectator identities imply the remaining comparison;
their heterogeneous operator equalities are used before any gate expansion is
substituted. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 351–434 and 565–588. -/
private theorem selectedRemainingComparison_of_selectedSpectatorIdentity {P Q R S : Type}
    (f : P → Q) (g : P → R) (lift : R → S) (p : P) (q : Q) (r : R)
    (hf : ∀ z, f z = q ↔ z = p) (hg : ∀ z, g z = r ↔ z = p)
    (tail : Layout P) {a b : Layout Q} {c d : Layout R} (W : Word a b) (V : Word c d)
    (hW : selectedSpectatorIdentity W q (Layout.mapOwner f tail))
    (hV : selectedSpectatorIdentity V r (Layout.mapOwner g tail)) :
    selectedRemainingComparison W V q r lift := by
  unfold selectedSpectatorIdentity at hW hV
  exact selectedRemainingComparison_of_spectator_id f g lift p q r
    hf hg tail W V hW hV

/-- An aggregate map at an excluded owner leaves precisely the selected
spectator identity. Its operator and register spaces are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedSpectatorIdentity_groupedBlockMap {P Q : Type}
    (f : P → Q) (r q : Q) (hrq : r ≠ q) (a b : Layout P)
    (ha : ∀ z ∈ a, f z.owner = r) (hb : ∀ z ∈ b, f z.owner = r)
    (A : Mem a →L[ℂ] Mem b) (tail : Layout P) :
    selectedSpectatorIdentity (Word.groupedBlockMap f r a b ha hb A tail)
      q (Layout.mapOwner f tail) := by
  classical
  unfold selectedSpectatorIdentity
  have hs : (Word.groupedBlockMap f r a b ha hb A tail).sources = [] := by
    simp only [Word.groupedBlockMap, Word.sources_castLayouts, Word.sources]
  refine (Word.restrict_localPart_eval_heq_of_sources_nil
    (partySelector q) _ hs).trans ?_
  unfold Word.groupedBlockMap
  rw [Word.restrict_castLayouts (partySelector q) _ _ _ rfl]
  exact (Word.eval_castLayouts_heq _ _ _).trans
    (Word.restrict_localMap_false_eval_heq (partySelector q) r _ _ _ _
      (by simp [partySelector, hrq]))

/-- A structural equality with an excluded aggregate map gives the selected
spectator identity without rewriting a fixed source proof.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedSpectatorIdentity_of_groupedBlockMap_eq {P Q : Type}
    (f : P → Q) (r q : Q) (hrq : r ≠ q) (a b : Layout P)
    (ha : ∀ z ∈ a, f z.owner = r) (hb : ∀ z ∈ b, f z.owner = r)
    (A : Mem a →L[ℂ] Mem b) (tail : Layout P)
    (v : Word (Layout.mapOwner f (a ++ tail)) (Layout.mapOwner f (b ++ tail)))
    (hv : v = Word.groupedBlockMap f r a b ha hb A tail) :
    selectedSpectatorIdentity v q (Layout.mapOwner f tail) := by
  exact Eq.mpr (congrArg (fun z ↦ selectedSpectatorIdentity z q
    (Layout.mapOwner f tail)) hv)
    (selectedSpectatorIdentity_groupedBlockMap f r q hrq a b ha hb A tail)

namespace SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]

/-- At an incident party, the all-party and singleton expansions use the
same original gate label and the same selected remaining operation.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedRemainingComparison_of_incident_gate
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail))
    (hincident : ∃ t : C, owner t = p) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    HEq (W.localPart.restrict (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W.sources_localPart).eval
      ((V.localPart.restrict (partySelector q) V.sources_localPart).mapOwner lift).eval := by
  classical
  intro A hp q lift χ W V
  let all := affectedOwner (fun _ : P ↦ true)
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let fa := affectedOwner A
  change selectedRemainingComparison W V qp q lift
  have hfAll : ∀ r, all r = qp ↔ r = p := by
    intro r
    simp [all, qp, affectedOwner]
  have hfA : ∀ r, fa r = q ↔ r = p := by
    intro r
    simpa only [fa, q, affectedOwner, hp, ↓reduceDIte,
      Bool.true_eq_false, and_false, or_false] using affectedOwner_eq_iff A r p
  obtain ⟨t, ht⟩ := hincident
  have htA : ∃ t : C, A (owner t) = true := ⟨t, by rw [ht]; exact hp⟩
  have htAll : ∃ _t : C, true = true := ⟨t, rfl⟩
  let eAll : Choices (fun _ : P ↦ true) (.gate owner G tail) ≃ ι :=
    Equiv.cast (by simp only [Choices]; exact ite_eq_left ⟨t, by trivial⟩)
  let eA : Choices A (.gate owner G tail) ≃ ι :=
    Equiv.cast (by simp only [Choices]; exact ite_eq_left htA)
  let i := eAll ξ
  have hi : eA χ = i := by
    exact choiceAt_projectAllChoices A (.gate owner G tail) ξ ()
      ((isTouched_gate_iff A owner G tail).mpr htA)
  let U := ((G.branchWord i).mapOwner owner).appendTail tail
  have hW : W = U.mapOwner all := by
    unfold W partialWord
    rw [dite_eq_left htAll]
    rfl
  have hV : V = U.mapOwner fa := by
    unfold V partialWord
    rw [dite_eq_left htA]
    change (((G.branchWord (eA χ)).mapOwner owner).appendTail tail).mapOwner fa = _
    rw [hi]
  exact selectedRemainingComparison_of_mapOwner_eq all fa lift p qp q hfAll hfA U W V hW hV

/-- Outside the original participating set, both selected remaining
operations retain precisely the same spectator identity.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedRemainingComparison_of_nonincident_gate
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail))
    (hincident : ¬ ∃ t : C, owner t = p) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    selectedRemainingComparison W V
      (some (⟨p, rfl⟩ : {_p : P // true = true})) q lift := by
  classical
  intro A hp q lift χ W V
  let all := affectedOwner (fun _ : P ↦ true)
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  let fa := affectedOwner A
  have hfAll : ∀ r, all r = qp ↔ r = p := by
    intro r
    simp [all, qp, affectedOwner]
  have hfA : ∀ r, fa r = q ↔ r = p := by
    intro r
    simpa only [fa, q, affectedOwner, hp, ↓reduceDIte,
      Bool.true_eq_false, and_false, or_false] using affectedOwner_eq_iff A r p
  have howner : ∀ t, owner t ≠ p := by
    intro t ht
    exact hincident ⟨t, ht⟩
  have htA : ¬ ∃ t : C, A (owner t) = true := by
    rintro ⟨t, ht⟩
    have he : all (owner t) = qp := by
      simpa only [A, partySelector, decide_eq_true_eq] using ht
    exact howner t ((hfAll (owner t)).mp he)
  have hV : V = Word.groupedBlockMap fa none
      (Layout.mapOwner owner a) (Layout.mapOwner owner b)
      (Layout.affectedOwner_mapOwner_eq_none A owner htA a)
      (Layout.affectedOwner_mapOwner_eq_none A owner htA b)
      (G.evalAtOwners owner) tail := by
    unfold V partialWord
    rw [dite_eq_right htA]
  have hOne : selectedSpectatorIdentity V q (Layout.mapOwner fa tail) :=
    selectedSpectatorIdentity_of_groupedBlockMap_eq fa none q (by simp [q])
      (Layout.mapOwner owner a) (Layout.mapOwner owner b)
      (Layout.affectedOwner_mapOwner_eq_none A owner htA a)
      (Layout.affectedOwner_mapOwner_eq_none A owner htA b)
      (G.evalAtOwners owner) tail V hV
  have hAll : selectedSpectatorIdentity W qp (Layout.mapOwner all tail) :=
    restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident owner G tail p howner ξ
  exact selectedRemainingComparison_of_selectedSpectatorIdentity all fa lift p qp q
    hfAll hfA tail W V hAll hOne

/-- The actual remaining operator at one original party agrees for the
all-party choice and its singleton projection. The participant and branch
sets may be empty; no extension of local labels or nonzero scalar is assumed.
This statement compares a single actual gate, including its spectators.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
theorem restrict_partialWord_all_gate_localPart_eval_heq_singleton_projection
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    HEq (W.localPart.restrict (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true})))
      W.sources_localPart).eval
      ((V.localPart.restrict (partySelector q) V.sources_localPart).mapOwner lift).eval := by
  classical
  by_cases hincident : ∃ t : C, owner t = p
  · exact selectedRemainingComparison_of_incident_gate owner G tail p ξ hincident
  · exact selectedRemainingComparison_of_nonincident_gate owner G tail p ξ hincident

/-- The gate comparison is retained as a comparison of arbitrary word
arguments before changing the singleton owners.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
private theorem selectedRemainingComparison_of_gate_projection
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    selectedRemainingComparison W V
      (some (⟨p, rfl⟩ : {_p : P // true = true})) q lift := by
  classical
  by_cases hincident : ∃ t : C, owner t = p
  · exact selectedRemainingComparison_of_incident_gate owner G tail p ξ hincident
  · exact selectedRemainingComparison_of_nonincident_gate owner G tail p ξ hincident

/-- The selected remaining evaluation of the all-party branch equals
that of the lifted singleton branch, retaining every original gate occurrence,
source dimension and spectator register.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–434
and 565–588. -/
theorem isSelectedLocalPartComparison_partialWord_all_gate
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (p : P)
    (ξ : Choices (fun _ : P ↦ true) (.gate owner G tail)) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    let χ := projectAllChoices A (.gate owner G tail) ξ
    let W := partialWord (fun _ : P ↦ true) (.gate owner G tail) ξ
    let V := partialWord A (.gate owner G tail) χ
    Word.IsSelectedLocalPartComparison
      (partySelector (some (⟨p, rfl⟩ : {_p : P // true = true}))) W (V.mapOwner lift) := by
  classical
  intro A hp q lift χ W V
  have hlift : ∀ o, lift o = some (⟨p, rfl⟩ : {_p : P // true = true}) ↔ o = q := by
    intro o
    cases o with
    | none => simp [lift, q]
    | some z => simp [lift, q, Subtype.ext_iff]
  exact isSelectedLocalPartComparison_of_selectedRemainingComparison lift q
    (some (⟨p, rfl⟩ : {_p : P // true = true})) hlift W V
    (selectedRemainingComparison_of_gate_projection owner G tail p ξ)

end SourceCircuit
end TNLean.PEPS.PairEffect
