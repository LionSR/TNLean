/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitError

/-!
# Physical density error for approximate original gates

The comparison is between the actual original gate maps and the contraction
circuit constructed by rescaling their approximate monomial sums. Both use
the same physical readout and retain the same discarded registers. The
trace-norm error is at most four times the local approximation budget times
the original gate count. The estimate concerns subnormalized densities and
does not divide by an output norm.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600,
and the absolute-error convention following the proof.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-approximatecircuitdensity-01
TNLean.PEPS.PairEffect.EffectCircuit.physicalDensityWithGateMaps
Provenance-ID: 8769-approximate-physical-approximatecircuitdensity-02
TNLean.PEPS.PairEffect.EffectCircuit.rectangularTraceNorm_rescaledOriginal_density_sub_le
Provenance-ID: 8769-approximate-physical-approximatecircuitdensity-03
TNLean.PEPS.PairEffect.EffectCircuit.rectangularTraceNorm_rescaledOriginal_density_sub_le_budget
-/


noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P Phys Env : Type} [Fintype Phys] [Fintype Env] [DecidableEq Phys]

/-- The original physical density, computed from the original gate operators
rather than their approximate monomial sums. -/
def physicalDensityWithGateMaps {a b : Layout P} (w : EffectCircuit a b)
    (G : w.GateMaps) (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env)) (x : Mem a) :=
  Matrix.partialTraceRight (Matrix.euclideanOuterProduct
    (K (w.evalWithGateMaps G x)) (K (w.evalWithGateMaps G x)))

/-- The actual physical density error is bounded by the accumulated local
operator error, with no discarded-dimension factor. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le {δ : ℝ} (hδ : 0 ≤ δ)
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (h : w.IsGateApproximation δ G)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (K ((w.rescaledOriginal hδ G h).eval x))
        (K ((w.rescaledOriginal hδ G h).eval x))) -
        w.physicalDensityWithGateMaps G K x) ≤ 4 * δ * w.expandedGateCount := by
  have h₁ : ‖K ((w.rescaledOriginal hδ G h).eval x)‖ ≤ 1 := by
    rw [K.norm_map]
    exact ((w.rescaledOriginal hδ G h).eval.le_opNorm_of_le hx).trans
      (by simpa only [mul_one] using (w.rescaledOriginal hδ G h).norm_eval_le_one)
  have h₂ : ‖K (w.evalWithGateMaps G x)‖ ≤ 1 := by
    rw [K.norm_map]
    exact ((w.evalWithGateMaps G).le_opNorm_of_le hx).trans
      (by simpa only [mul_one] using w.norm_evalWithGateMaps_le_one G h)
  have hd : ‖K ((w.rescaledOriginal hδ G h).eval x) -
      K (w.evalWithGateMaps G x)‖ ≤ 2 * δ * w.expandedGateCount := by
    rw [← map_sub K, K.norm_map, ← sub_apply]
    exact (((w.rescaledOriginal hδ G h).eval - w.evalWithGateMaps G).le_opNorm_of_le hx).trans
      (by simpa only [mul_one] using w.norm_rescaledOriginal_sub_evalWithGateMaps_le hδ G h)
  exact (Matrix.rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two _ _ h₁ h₂).trans
    ((mul_le_mul_of_nonneg_left hd (by norm_num)).trans_eq (by ring))

/-- A gate budget chosen from any upper bound on the original gate count
consumes at most half of its supplied physical error budget. In particular,
supplying `ε / 2` reserves `ε / 4` for approximate gate expansions. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_budget
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    {ε : ℝ} (hε : 0 < ε) {M : ℕ} (hM : w.expandedGateCount ≤ M)
    (h : w.IsGateApproximation (sourceGateBudget ε M) G)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (K ((w.rescaledOriginal (sourceGateBudget_pos hε M).le G h).eval x))
        (K ((w.rescaledOriginal (sourceGateBudget_pos hε M).le G h).eval x))) -
        w.physicalDensityWithGateMaps G K x) ≤ ε / 2 := by
  have hc : (w.expandedGateCount : ℝ) ≤ M := by exact_mod_cast hM
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le
    (sourceGateBudget_pos hε M).le G h K x hx).trans
      ((mul_le_mul_of_nonneg_left hc
        (mul_nonneg (by norm_num) (sourceGateBudget_pos hε M).le)).trans
          (sourceGateBudget_spec hε.le M))

end TNLean.PEPS.PairEffect.EffectCircuit
