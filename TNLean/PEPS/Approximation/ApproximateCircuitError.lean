/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitResources

/-!
# Chronological error of approximate gate expansions

After rescaling each approximate gate to a contraction, its local error is
at most twice the prescribed approximation budget. Telescoping along the
actual chronology gives the same bound multiplied by the number of original
nonprivate occurrences. Arbitrary spectator memories do not change the bound.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-approximatecircuiterror-01
TNLean.PEPS.PairEffect.EffectCircuit.norm_rescaledOriginal_sub_evalWithGateMaps_le
Provenance-ID: 8769-approximate-physical-approximatecircuiterror-02
TNLean.PEPS.PairEffect.OriginalCircuit.norm_eval_le_one
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- Every original circuit is a contraction by its actual gate hypotheses. -/
theorem OriginalCircuit.norm_eval_le_one {a b : Layout P} (w : OriginalCircuit a b) :
    ‖w.eval‖ ≤ 1 := by
  simpa only [w.eval_produce] using w.produce.norm_eval_le_one w.isAllowed_produce

namespace EffectCircuit
/-- The actual rescaled chronological operator differs from the original
operator by at most twice the local budget times the original gate count. -/
theorem norm_rescaledOriginal_sub_evalWithGateMaps_le {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G) :
    ‖(w.rescaledOriginal hδ G h).eval - w.evalWithGateMaps G‖ ≤
      2 * δ * w.expandedGateCount := by
  induction w with
  | id => simp only [rescaledOriginal, OriginalCircuit.eval, evalWithGateMaps,
      sub_self, norm_zero, expandedGateCount, Nat.cast_zero, mul_zero, le_refl]
  | @comp a b d w v ihw ihv =>
      have hc := norm_comp_sub_comp_le_one (Mem a) (Mem b) (Mem d)
        (w.rescaledOriginal hδ G.1 h.1).eval (w.evalWithGateMaps G.1)
        (v.rescaledOriginal hδ G.2 h.2).eval (v.evalWithGateMaps G.2)
        (OriginalCircuit.norm_eval_le_one _) (w.norm_evalWithGateMaps_le_one G.1 h.1)
      exact hc.trans ((add_le_add (ihw G.1 h.1) (ihv G.2 h.2)).trans_eq
        (by simp only [expandedGateCount, Nat.cast_add, mul_add]))
  | localMap => simp only [rescaledOriginal, OriginalCircuit.eval, evalWithGateMaps,
      Word.eval, sub_self, norm_zero, expandedGateCount, Nat.cast_zero, mul_zero, le_refl]
  | @gate C _ owner a b L tail =>
      dsimp only [rescaledOriginal, OriginalCircuit.eval, evalWithGateMaps, expandedGateCount]
      have he : ‖gateMemoryMap owner a b tail
          (PairEffect.gate (toGate (rescalePartyGate δ L))) -
          gateMemoryMap owner a b tail G‖ ≤ 2 * δ := by
        rw [← gateMemoryMap_sub, gate_rescalePartyGate]
        exact (norm_gateMemoryMap_le _ _ _ _ _).trans
          (norm_inv_one_add_smul_sub_le hδ h.2.2.1 h.2.2.2)
      simpa only [gateMemoryMap, Nat.cast_one, mul_one] using he
  | swap => simp only [rescaledOriginal, OriginalCircuit.eval, evalWithGateMaps,
      Word.eval, sub_self, norm_zero, expandedGateCount, Nat.cast_zero, mul_zero, le_refl]
  | frame r w ih =>
      change ‖(w.rescaledOriginal hδ G h).eval.lTensor r.space -
        (w.evalWithGateMaps G).lTensor r.space‖ ≤ _
      rw [← lTensor_sub]
      exact (norm_lTensor_le _ _).trans (ih G h)
end EffectCircuit
end TNLean.PEPS.PairEffect
