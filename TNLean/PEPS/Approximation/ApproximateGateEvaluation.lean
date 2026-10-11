/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceOnlyReduction

/-!
# Original operators and approximate monomial expansions

The existing chronological circuit records the approximate monomial lists.
A separate family assigns the original operator to each of these same gate
occurrences. Evaluation uses the original private operations, participant
embeddings and spectator registers. Thus an approximation of one local gate
is compared before its extension to the full memory.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600;
the gate and participant conventions are in lines 21–36.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P : Type}

/-- Original gate operators, one for each occurrence of the chronology.
Composition keeps repeated occurrences distinct. -/
@[reducible] def GateMaps : {a b : Layout P} → EffectCircuit a b → Type
  | _, _, .id _ => PUnit
  | _, _, .comp w v => GateMaps w × GateMaps v
  | _, _, .localMap .. => PUnit
  | _, _, @EffectCircuit.gate _ _ _ _ a b _ _ => Mem a →L[ℂ] Mem b
  | _, _, .swap .. => PUnit
  | _, _, .frame _ w => GateMaps w

/-- Evaluate the original operators on the recorded chronology, with the
same participant embeddings and spectator identities as the approximate sums. -/
def evalWithGateMaps : {a b : Layout P} → (w : EffectCircuit a b) →
    w.GateMaps → Mem a →L[ℂ] Mem b
  | _, _, .id _, _ => .id ℂ _
  | _, _, .comp w v, G => v.evalWithGateMaps G.2 ∘L w.evalWithGateMaps G.1
  | _, _, .localMap p ha hb A tail, _ => (Word.localMap p ha hb A tail).eval
  | _, _, @EffectCircuit.gate _ _ _ owner a b _ tail, G =>
      gateMemoryMap owner a b tail G
  | _, _, .swap r s tail, _ => (Word.swap r s tail).eval
  | _, _, .frame r w, G => (w.evalWithGateMaps G).lTensor r.space

/-- The local hypotheses for an approximate expansion: private operations and
original gates are contractions, each monomial is allowed, each gate has its
prescribed nonprivate participant set, and its actual sum has operator error
at most the stated budget. No comparison of whole circuits is assumed. -/
def IsGateApproximation (δ : ℝ) : {a b : Layout P} → (w : EffectCircuit a b) →
    w.GateMaps → Prop
  | _, _, .id _, _ => True
  | _, _, .comp w v, G => w.IsGateApproximation δ G.1 ∧ v.IsGateApproximation δ G.2
  | _, _, .localMap _ _ _ A _, _ => ‖A‖ ≤ 1
  | _, _, @EffectCircuit.gate _ C _ _ a b L _, G =>
      Fintype.card C ≠ 1 ∧ (∀ q ∈ L, q.2.IsAllowed) ∧ ‖(G : Mem a →L[ℂ] Mem b)‖ ≤ 1 ∧
        ‖PairEffect.gate (toGate L) - (G : Mem a →L[ℂ] Mem b)‖ ≤ δ
  | _, _, .swap .., _ => True
  | _, _, .frame _ w, G => w.IsGateApproximation δ G

/-- The original chronological operator is a contraction, proved from the
local gate hypotheses and the exact spectator isometries. -/
theorem norm_evalWithGateMaps_le_one {a b : Layout P} (w : EffectCircuit a b)
    (G : w.GateMaps) {δ : ℝ} (h : w.IsGateApproximation δ G) :
    ‖w.evalWithGateMaps G‖ ≤ 1 := by
  induction w with
  | id => exact norm_id_le
  | comp w v ihw ihv => exact norm_comp_le_one (ihv G.2 h.2) (ihw G.1 h.1)
  | localMap p ha hb A tail => exact Word.norm_eval_le_one (.localMap p ha hb A tail) h
  | gate owner L tail => exact (norm_gateMemoryMap_le _ _ _ _ G).trans h.2.2.1
  | swap r s tail => exact Word.norm_eval_le_one (.swap r s tail) trivial
  | frame r w ih => exact (norm_lTensor_le _ _).trans (ih G h)

end TNLean.PEPS.PairEffect.EffectCircuit
