/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.IncidentGateLabels
import TNLean.Lattice.Compression.SourceResidualCoordinates
import TNLean.Lattice.Compression.LocalPartRestrictionCongruence
import TNLean.Lattice.Compression.NonincidentAllGateRestriction
/-!
# Dependence of an actual branch on incident gate choices

For two supplied choices in the all-party expansion, the remaining operator at
an original party is the same whenever their projected incident choices agree.
The argument compares the actual chronological constructors. Gates away from
that party retain the spectator identity, including gates with no participants.
No extension of an incident choice to unused gate labels is selected.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 246–267, 351–381, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Equality of the already selected remaining operators, formed before
concrete circuit words are substituted. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 351–381, 409–434 and 565–588. -/
private def selectedRemainingEvalHEq {Q : Type} (f : Q → Bool)
    {a b a' b' : Layout Q} (u : Word a b) (v : Word a' b') : Prop :=
  HEq (u.localPart.restrict f u.sources_localPart).eval
    (v.localPart.restrict f v.sources_localPart).eval

/-- Two selected remaining operators equal to the same spectator identity
are equal, even when their original source lists differ. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381 and 409–434. -/
private theorem selectedRemainingEvalHEq_of_identity {Q : Type} (f : Q → Bool)
    {a b a' b' : Layout Q} (u : Word a b) (v : Word a' b') (spectators : Layout Q)
    (hu : HEq (u.localPart.restrict f u.sources_localPart).eval
      (ContinuousLinearMap.id ℂ (Mem spectators)))
    (hv : HEq (v.localPart.restrict f v.sources_localPart).eval
      (ContinuousLinearMap.id ℂ (Mem spectators))) :
    selectedRemainingEvalHEq f u v := by
  exact hu.trans hv.symm

/-- Any two supplied branches of a nonincident gate retain the same spectator
identity. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 351–381, 409–434 and 565–588. -/
private theorem selectedRemainingEvalHEq_nonincident_gate
    {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b)
    (tail : Layout P) (p : P) (howner : ∀ t, owner t ≠ p)
    (ξ ζ : Choices (fun _ : P => true) (.gate owner G tail)) :
    let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
    selectedRemainingEvalHEq (partySelector q)
      (partialWord (fun _ : P => true) (.gate owner G tail) ξ)
      (partialWord (fun _ : P => true) (.gate owner G tail) ζ) := by
  classical
  intro q
  exact selectedRemainingEvalHEq_of_identity (partySelector q)
    (partialWord (fun _ : P => true) (.gate owner G tail) ξ)
    (partialWord (fun _ : P => true) (.gate owner G tail) ζ)
    (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P => true)) tail))
    (restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident
      owner G tail p howner ξ)
    (restrict_partialWord_all_gate_localPart_eval_heq_id_of_nonincident
      owner G tail p howner ζ)

/-- Chronological composition preserves the selected operator equality under
the existing selected-layout identifications. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 246–267 and 409–434. -/
private theorem selectedRemainingEvalHEq_comp {Q : Type} (f : Q → Bool)
    {a b c a' b' c' : Layout Q}
    (u : Word a b) (v : Word b c) (u' : Word a' b') (v' : Word b' c')
    (ha : Layout.restrict f a = Layout.restrict f a')
    (hb : Layout.restrict f b = Layout.restrict f b')
    (hc : Layout.restrict f c = Layout.restrict f c')
    (hu : Layout.restrict f u.sources.layout = Layout.restrict f u'.sources.layout)
    (hv : Layout.restrict f v.sources.layout = Layout.restrict f v'.sources.layout)
    (heu : selectedRemainingEvalHEq f u u') (hev : selectedRemainingEvalHEq f v v') :
    selectedRemainingEvalHEq f (u.comp v) (u'.comp v') := by
  exact Word.restrict_localPart_comp_eval_heq f u v u' v' ha hb hc hu hv heu hev

/-- Framing preserves the selected operator equality under the existing
selected-layout identifications. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267 and 409–434. -/
private theorem selectedRemainingEvalHEq_frame {Q : Type} (f : Q → Bool) (r : Reg Q)
    {a b a' b' : Layout Q} (u : Word a b) (v : Word a' b')
    (ha : Layout.restrict f a = Layout.restrict f a')
    (hb : Layout.restrict f b = Layout.restrict f b')
    (hs : Layout.restrict f u.sources.layout = Layout.restrict f v.sources.layout)
    (he : selectedRemainingEvalHEq f u v) :
    selectedRemainingEvalHEq f (Word.frame r u) (Word.frame r v) := by
  exact Word.restrict_localPart_frame_eval_heq f r u v ha hb hs he

private theorem selected_sources_partialWord_all_eq {a b : Layout P}
    (w : SourceCircuit a b)
    (f : Option {t : P // (fun _ : P => true) t = true} → Bool)
    (ξ ζ : Choices (fun _ : P => true) w) :
    Layout.restrict f (partialWord (fun _ : P => true) w ξ).sources.layout =
      Layout.restrict f (partialWord (fun _ : P => true) w ζ).sources.layout :=
  congrArg (Layout.restrict f)
    ((slotLayout_partialSlots_eq (fun _ : P => true) w ξ).symm.trans
      (slotLayout_partialSlots_eq (fun _ : P => true) w ζ))

/-- The singleton restriction of the actual all-party remaining operations
depends only on the projected choices at the original party. Both full choices
are supplied, and no unused branch label is chosen.
The conclusion abbreviates exactly the equality of the two selected remaining
operators, preserving their original word constructions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267,
351–381, 409–434 and 565–588. -/
theorem restrict_partialWord_all_localPart_eval_heq_of_projectAllChoices_eq
    {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ξ ζ : Choices (fun _ : P => true) w)
    (h : projectAllChoices (fun t => partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P => true) t)) w ξ =
      projectAllChoices (fun t => partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P => true) t)) w ζ) :
    let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
    selectedRemainingEvalHEq (partySelector q)
      (partialWord (fun _ : P => true) w ξ)
      (partialWord (fun _ : P => true) w ζ) := by
  classical
  let q := some (⟨p, rfl⟩ : {t : P // (fun _ : P => true) t = true})
  let f := partySelector q
  let A := fun t : P => f (affectedOwner (fun _ : P => true) t)
  change projectAllChoices A w ξ = projectAllChoices A w ζ at h
  change selectedRemainingEvalHEq f (partialWord (fun _ : P => true) w ξ)
    (partialWord (fun _ : P => true) w ζ)
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      have hcomp := selectedRemainingEvalHEq_comp f
        (partialWord (fun _ : P => true) w ξ.1) (partialWord (fun _ : P => true) v ξ.2)
        (partialWord (fun _ : P => true) w ζ.1) (partialWord (fun _ : P => true) v ζ.2)
        rfl rfl rfl
        (selected_sources_partialWord_all_eq w f ξ.1 ζ.1)
        (selected_sources_partialWord_all_eq v f ξ.2 ζ.2)
        (ihw ξ.1 ζ.1 (congrArg Prod.fst h)) (ihv ξ.2 ζ.2 (congrArg Prod.snd h))
      exact hcomp
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      by_cases hf : ∃ t : C, A (owner t) = true
      · have hg := (isTouched_gate_iff A owner G tail).mpr hf
        have he := congrArg (fun η => choiceAt A (.gate owner G tail) η () hg) h
        have heAll := (choiceAt_projectAllChoices A (.gate owner G tail) ξ () hg).symm.trans
          (he.trans (choiceAt_projectAllChoices A (.gate owner G tail) ζ () hg))
        have hξζ : ξ = ζ := by
          dsimp only [choiceAt] at heAll
          exact Equiv.injective _ heAll
        cases hξζ
        rfl
      · have howner : ∀ t : C, owner t ≠ p := by
          intro t htp
          apply hf
          refine ⟨t, ?_⟩
          rw [htp]
          exact (partySelector_affectedOwner_all_apply p p).trans
            (by simp only [partySelector, decide_true])
        exact selectedRemainingEvalHEq_nonincident_gate owner G tail p howner ξ ζ
  | swap => rfl
  | frame r w ih =>
      exact selectedRemainingEvalHEq_frame f
        ⟨affectedOwner (fun _ : P => true) r.owner, r.space⟩
        (partialWord (fun _ : P => true) w ξ) (partialWord (fun _ : P => true) w ζ)
        rfl rfl (selected_sources_partialWord_all_eq w f ξ ζ) (ih ξ ζ h)

end TNLean.PEPS.PairEffect.SourceCircuit
