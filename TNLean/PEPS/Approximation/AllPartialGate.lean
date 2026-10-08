/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AllChoicesProjection
import TNLean.PEPS.Approximation.SourceResidualCoordinates

/-! # All-party branches at actual gate occurrences

These identities describe the selected branch and its action away from the
original participants. Source: polynomial-PEPS, `04-compression.tex`, lines 233–251
and 351–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-chronological-network-allpartialgate-01
TNLean.PEPS.PairEffect.SourceCircuit.partialWord_all_gate_eq_of_touched
Provenance-ID: 8769-chronological-network-allpartialgate-02
TNLean.PEPS.PairEffect.SourceCircuit.partialWord_all_gate_eq_of_untouched
Provenance-ID: 8769-chronological-network-allpartialgate-03
TNLean.PEPS.PairEffect.SourceCircuit.restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P C ι : Type} [Fintype C] [Fintype ι]

/-- The actual all-party branch at a nonempty participant occurrence is its
original prepared gate branch, placed in the stated spectators.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem partialWord_all_gate_eq_of_touched (owner : C ↪ P) {a b : Layout C}
    {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P)
    (ξ : Choices (fun _ => true) (.gate owner G tail))
    (ht : ∃ _q : C, true = true) :
    partialWord (fun _ => true) (.gate owner G tail) ξ =
      (((G.branchWord (choiceAt (fun _ => true) (.gate owner G tail) ξ ()
        ((isTouched_gate_iff _ owner G tail).mpr ht))).mapOwner owner).appendTail tail).mapOwner
          (affectedOwner (fun _ => true)) := by
  unfold partialWord
  rw [dite_eq_left ht]
  rfl

/-- An untouched occurrence retains its whole operation and is independent
of the choice supplied to the all-party expansion.
Source: polynomial-PEPS 04-compression.tex, lines 351–381. -/
theorem partialWord_all_gate_eq_of_untouched (owner : C ↪ P) {a b : Layout C}
    {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P)
    (ξ ζ : Choices (fun _ => true) (.gate owner G tail))
    (ht : ¬∃ _q : C, true = true) :
    partialWord (fun _ => true) (.gate owner G tail) ξ =
      partialWord (fun _ => true) (.gate owner G tail) ζ := by
  unfold partialWord
  rw [dite_eq_right ht, dite_eq_right ht]

private theorem localPart_restrict_eval_heq_of_eq {Q : Type} (f : Q → Bool)
    {a b : Layout Q} (w v : Word a b) (h : w = v) :
    HEq ((w.localPart.restrict f w.sources_localPart).eval)
      ((v.localPart.restrict f v.sources_localPart).eval) := by
  cases h
  rfl

set_option maxHeartbeats 800000 in
-- Nested owner transports in the actual branch use dependent source layouts.
/-- The actual hoisted all-party gate branch acts as the selected spectator
identity away from its original participants. Source: polynomial-PEPS
04-compression.tex, lines 233–251 and 351–381. -/
theorem restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P)
    (ξ : Choices (fun _ => true) (.gate owner G tail))
    (ht : ∃ _q : C, true = true)
    (f : Option {p : P // (fun _ : P => true) p = true} → Bool)
    (hf : ∀ q, f (affectedOwner (fun _ => true) (owner q)) = false) :
    HEq (((partialWord (fun _ => true) (.gate owner G tail) ξ).localPart.restrict f
      (partialWord (fun _ => true) (.gate owner G tail) ξ).sources_localPart).eval)
      (ContinuousLinearMap.id ℂ
        (Mem (Layout.restrict f (Layout.mapOwner (affectedOwner (fun _ => true)) tail)))) := by
  have hg := (isTouched_gate_iff (fun _ => true) owner G tail).mpr ht
  let i : ι := choiceAt (fun _ => true) (.gate owner G tail) ξ () hg
  exact (localPart_restrict_eval_heq_of_eq f _ _
    (partialWord_all_gate_eq_of_touched owner G tail ξ ht)).trans
      (Word.restrict_localPart_mapOwner_appendTail_mapOwner_eval_eq_id_of_disjoint
        owner (affectedOwner (fun _ => true)) f (G.branchWord i) hf tail)

end TNLean.PEPS.PairEffect.SourceCircuit
