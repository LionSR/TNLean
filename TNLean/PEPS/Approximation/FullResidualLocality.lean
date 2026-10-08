/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.InvisibleRestriction

/-! # Local dependence of the actual complete residual

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-fullresiduallocality-01
TNLean.PEPS.PairEffect.SourceCircuit.fixedSourceLayout
Provenance-ID: 8769-chronological-network-fullresiduallocality-02
TNLean.PEPS.PairEffect.SourceCircuit.fullRemainingWord
Provenance-ID: 8769-chronological-network-fullresiduallocality-03
TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_fullRemainingWord
Provenance-ID: 8769-chronological-network-fullresiduallocality-04
TNLean.PEPS.PairEffect.SourceCircuit.localRemainingMap
Provenance-ID: 8769-chronological-network-fullresiduallocality-05
TNLean.PEPS.PairEffect.SourceCircuit.norm_localRemainingMap_le_one
Provenance-ID: 8769-chronological-network-fullresiduallocality-06
TNLean.PEPS.PairEffect.SourceCircuit.restrict_fullRemainingWord_eq_localRemainingMap
Provenance-ID: 8769-chronological-network-fullresiduallocality-07
TNLean.PEPS.PairEffect.SourceCircuit.restrict_fullRemainingWord_eq_of_agree
Provenance-ID: 8769-chronological-network-fullresiduallocality-08
TNLean.PEPS.PairEffect.SourceCircuit.restrict_fullRemainingWord_eq_of_choices_eq
Provenance-ID: 8769-chronological-network-fullresiduallocality-09
TNLean.PEPS.PairEffect.SourceCircuit.sources_fullRemainingWord
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem restrict_castInput_congr (f : P → Bool) {a b a' : Layout P}
    (w v : Word a b) (h : a = a') (hw : w.sources = []) (hv : v.sources = [])
    (he : (w.restrict f hw).eval = (v.restrict f hv).eval) :
    ((w.castInput h).restrict f ((Word.sources_castInput _ _).trans hw)).eval =
      ((v.castInput h).restrict f ((Word.sources_castInput _ _).trans hv)).eval := by
  cases h
  exact he

private theorem restrict_comp_congr (f : P → Bool) {a b d : Layout P}
    (w w' : Word a b) (v v' : Word b d)
    (hw : w.sources = []) (hw' : w'.sources = [])
    (hv : v.sources = []) (hv' : v'.sources = [])
    (he : (w.restrict f hw).eval = (w'.restrict f hw').eval)
    (he' : (v.restrict f hv).eval = (v'.restrict f hv').eval) :
    ((Word.comp w v).restrict f (by simp only [Word.sources, hw, hv, List.nil_append])).eval =
      ((Word.comp w' v').restrict f
        (by simp only [Word.sources, hw', hv', List.nil_append])).eval := by
  exact congrArg₂ ContinuousLinearMap.comp he' he

private theorem restrict_frame_congr (f : P → Bool) (r : Reg P) {a b : Layout P}
    (w v : Word a b) (hw : w.sources = []) (hv : v.sources = [])
    (he : (w.restrict f hw).eval = (v.restrict f hv).eval) :
    ((Word.frame r w).restrict f hw).eval = ((Word.frame r v).restrict f hv).eval := by
  by_cases hr : f r.owner = true
  · exact eq_of_heq ((Word.restrict_frame_true_eval_heq f r w hw hr).trans
      ((heq_of_eq (congrArg (fun A => A.lTensor r.space) he)).trans
        (Word.restrict_frame_true_eval_heq f r v hv hr).symm))
  · have hr' := Bool.eq_false_iff.mpr hr
    exact eq_of_heq ((Word.restrict_frame_false_eval_heq f r w hw hr').trans
      ((heq_of_eq he).trans (Word.restrict_frame_false_eval_heq f r v hv hr').symm))

private theorem restrict_frameList_congr (f : P → Bool) {a b : Layout P}
    (w v : Word a b) (hw : w.sources = []) (hv : v.sources = [])
    (he : (w.restrict f hw).eval = (v.restrict f hv).eval) (rs : Layout P) :
    ((Word.frameList rs w).restrict f ((Word.sources_frameList _ _).trans hw)).eval =
      ((Word.frameList rs v).restrict f ((Word.sources_frameList _ _).trans hv)).eval := by
  induction rs with
  | nil => exact he
  | cons r rs ih => exact restrict_frame_congr f r _ _ _ _ ih

/-- The fixed source-register layout of the full chronology, ordered with the
later preparations first. It does not depend on any monomial labels.
Source: polynomial-PEPS 04-compression.tex, lines 233–267 and 342–355. -/
def fixedSourceLayout : {a b : Layout P} → SourceCircuit a b → Layout P
  | _, _, .id _ => []
  | _, _, .comp w v => fixedSourceLayout v ++ fixedSourceLayout w
  | _, _, .localMap .. => []
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G _ =>
      Layout.mapOwner owner (SourceInventory.slotLayout G.slots
        (fun i => euc (Fin (G.leftDim i))) (fun i => euc (Fin (G.rightDim i))))
  | _, _, .swap .. => []
  | _, _, .frame _ w => fixedSourceLayout w

/-- The actual source-free residual constructed from the complete chronological
labels after placing each gate's fixed source registers at the beginning.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
def fullRemainingWord : {a b : Layout P} → (w : SourceCircuit a b) →
    FullLabels w → Word (w.fixedSourceLayout ++ a) b
  | _, _, .id a, _ => .id a
  | _, _, .comp w v, ξ =>
      (Word.comp (Word.frameList v.fixedSourceLayout
        (fullRemainingWord w (fun g => ξ (.inl g))))
        (fullRemainingWord v (fun g => ξ (.inr g)))).castInput
          (List.append_assoc _ _ _).symm
  | _, _, .localMap p ha hb A tail, _ => .localMap p ha hb A tail
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G tail, ξ =>
      (((G.remaining (ξ ())).mapOwner owner).appendTail tail).castInput (by
        rw [Layout.mapOwner_append, List.append_assoc]
        rfl)
  | _, _, .swap r s tail, _ => .swap r s tail
  | _, _, .frame r w, ξ =>
      Word.comp (Word.moveHead r w.fixedSourceLayout _) (.frame r (fullRemainingWord w ξ))

/-- The constructed full residual contains no source preparations.
Source: polynomial-PEPS 04-compression.tex, lines 233–251. -/
theorem sources_fullRemainingWord {a b : Layout P} (w : SourceCircuit a b)
    (ξ : FullLabels w) : (w.fullRemainingWord ξ).sources = [] := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      let ξw : FullLabels w := fun g => ξ (.inl g)
      let ξv : FullLabels v := fun g => ξ (.inr g)
      exact (Word.sources_castInput _ _).trans
        ((congrArg₂ (fun S T : SourceInventory P => S ++ T) (ihv ξv)
          ((Word.sources_frameList _ _).trans (ihw ξw))).trans rfl)
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      exact (Word.sources_castInput _ _).trans <|
        (Word.sources_appendTail _ _).trans <|
          (Word.sources_mapOwner owner _).trans <|
            (congrArg (SourceInventory.mapOwner owner) (G.remaining_sources (ξ ()))).trans
              (SourceInventory.mapOwner_nil owner)
  | swap => rfl
  | frame r w ih =>
      exact (congrArg₂ (fun S T : SourceInventory P => S ++ T) (ih ξ)
        (Word.sources_moveHead _ _ _)).trans rfl

/-- The actual full residual is allowed whenever the chronological private
operations are allowed. Source: polynomial-PEPS 04-compression.tex, lines 233–251. -/
theorem isAllowed_fullRemainingWord {a b : Layout P} (w : SourceCircuit a b)
    (hw : w.IsAllowed) (ξ : FullLabels w) : (w.fullRemainingWord ξ).IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv =>
      exact (Word.isAllowed_castInput _ _).mpr
        ⟨Word.isAllowed_frameList _ (ihw hw.1 _) _, ihv hw.2 _⟩
  | localMap => exact hw
  | @gate C ι _ _ owner a b c G tail =>
      exact (Word.isAllowed_castInput _ _).mpr
        (Word.isAllowed_appendTail _
          (Word.isAllowed_mapOwner owner _ (G.remaining_allowed _)) tail)
  | swap => trivial
  | frame r w ih => exact ⟨Word.isAllowed_moveHead _ _ _, ih hw ξ⟩
/-- The restriction of the actual full chronological residual at a party depends
only on labels of gates in which that party participates.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_fullRemainingWord_eq_of_agree {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ ζ : FullLabels w)
    (h : ∀ g, p ∈ w.participants g → ξ g = ζ g) :
    ((w.fullRemainingWord ξ).restrict (partySelector p)
      (w.sources_fullRemainingWord ξ)).eval =
    ((w.fullRemainingWord ζ).restrict (partySelector p)
      (w.sources_fullRemainingWord ζ)).eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      let ξw : FullLabels w := fun g => ξ (.inl g)
      let ζw : FullLabels w := fun g => ζ (.inl g)
      let ξv : FullLabels v := fun g => ξ (.inr g)
      let ζv : FullLabels v := fun g => ζ (.inr g)
      have hew := ihw ξw ζw (fun g hg => h (.inl g) hg)
      have hev := ihv ξv ζv (fun g hg => h (.inr g) hg)
      have hef := restrict_frameList_congr (partySelector p) _ _ _ _ hew v.fixedSourceLayout
      have hec := restrict_comp_congr (partySelector p) _ _ _ _ _ _ _ _ hef hev
      exact restrict_castInput_congr (partySelector p) _ _ _ _ _ hec
  | localMap => rfl
  | @gate C ι _ _ owner a b c G tail =>
      by_cases hp : p ∈ (SourceCircuit.gate owner G tail).participants ()
      · have hl := h () hp
        change Unit → ι at ξ ζ
        simp only [fullRemainingWord, hl]
      · exact restrict_castInput_congr (partySelector p) _ _ _ _ _
          (G.restrict_remaining_appendTail_eq_of_not_participating owner tail p hp (ξ ()) (ζ ()))
  | swap => rfl
  | frame r w ih =>
      have he := restrict_frame_congr (partySelector p) r _ _ _ _ (ih ξ ζ h)
      exact restrict_comp_congr (partySelector p) _ _ _ _
        (Word.sources_moveHead _ _ _) (Word.sources_moveHead _ _ _) _ _ rfl he
/-- The actual restricted full residual is determined by the incident partial
choices recovered from its chronological labels.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem restrict_fullRemainingWord_eq_of_choices_eq {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ ζ : FullLabels w)
    (he : choicesOfFullLabels (partySelector p) w ξ =
      choicesOfFullLabels (partySelector p) w ζ) :
    ((w.fullRemainingWord ξ).restrict (partySelector p)
      (w.sources_fullRemainingWord ξ)).eval =
    ((w.fullRemainingWord ζ).restrict (partySelector p)
      (w.sources_fullRemainingWord ζ)).eval := by
  apply restrict_fullRemainingWord_eq_of_agree
  intro g hg
  have ht : w.IsTouched (partySelector p) g :=
    ⟨p, hg, by simp only [partySelector, decide_true]⟩
  calc
    ξ g = choiceAt (partySelector p) w (choicesOfFullLabels (partySelector p) w ξ) g ht :=
      (choiceAt_choicesOfFullLabels (partySelector p) w ξ g ht).symm
    _ = choiceAt (partySelector p) w (choicesOfFullLabels (partySelector p) w ζ) g ht :=
      congrArg (fun η => choiceAt (partySelector p) w η g ht) he
    _ = ζ g := choiceAt_choicesOfFullLabels (partySelector p) w ζ g ht

/-- A local residual on the actual incident-choice type. If a local choice has
no full chronological extension, its value is zero; every genuine full branch
is compared to its actual party restriction below.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
def localRemainingMap {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (η : Choices (partySelector p) w) :
    Mem (Layout.restrict (partySelector p) (w.fixedSourceLayout ++ a)) →L[ℂ]
      Mem (Layout.restrict (partySelector p) b) := by
  classical
  exact if h : ∃ ξ : FullLabels w, choicesOfFullLabels (partySelector p) w ξ = η then
    ((w.fullRemainingWord (Classical.choose h)).restrict (partySelector p)
      (w.sources_fullRemainingWord (Classical.choose h))).eval
  else 0

/-- The local residual is exactly the restriction of the actual full residual
for each genuine chronological label choice. No label type is assumed inhabited.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_fullRemainingWord_eq_localRemainingMap {a b : Layout P}
    (w : SourceCircuit a b) (p : P) (ξ : FullLabels w) :
    ((w.fullRemainingWord ξ).restrict (partySelector p)
      (w.sources_fullRemainingWord ξ)).eval =
      w.localRemainingMap p (choicesOfFullLabels (partySelector p) w ξ) := by
  unfold localRemainingMap
  split
  · rename_i h
    exact restrict_fullRemainingWord_eq_of_choices_eq w p ξ (Classical.choose h)
      (Classical.choose_spec h).symm
  · rename_i h
    exact (h ⟨ξ, rfl⟩).elim

/-- Each local residual obtained from the actual circuit is a contraction.
Unextendable choices contribute zero and require no additional label assumptions.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem norm_localRemainingMap_le_one {a b : Layout P} (w : SourceCircuit a b)
    (hw : w.IsAllowed) (p : P) (η : Choices (partySelector p) w) :
    ‖w.localRemainingMap p η‖ ≤ 1 := by
  unfold localRemainingMap
  split
  · exact Word.norm_eval_le_one _
      (Word.isAllowed_restrict _ _ _ (w.isAllowed_fullRemainingWord hw _))
  · simp only [norm_zero, zero_le_one]
end TNLean.PEPS.PairEffect.SourceCircuit
