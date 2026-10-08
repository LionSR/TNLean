/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitDensity

/-!
# Inverse-polynomial accuracy of the original gate approximations

If the number of nonprivate gates is at most `C L^n`, approximation of each
gate to accuracy `L^(-(n+p+1))` leaves physical-density error at most
`L^(-p)/4` once `L ≥ max(1,16C)`. Thus one fixed higher accuracy exponent
absorbs the polynomial gate count. Coefficient rescaling does not increase
the monomial or coefficient bounds of the selected approximation.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-approximatecircuitpolynomial-01
TNLean.PEPS.PairEffect.EffectCircuit.rectangularTraceNorm_rescaledOriginal_density_sub_le_inv_pow
Provenance-ID: 8769-approximate-physical-approximatecircuitpolynomial-02
TNLean.PEPS.PairEffect.gateApproximation_error_inv_pow_le
-/


noncomputable section
namespace TNLean.PEPS.PairEffect

/-- One additional inverse power absorbs the fixed coefficient of a polynomial
gate-count bound, with an explicit threshold independent of private dimensions. -/
theorem gateApproximation_error_inv_pow_le (L C : ℝ) (N n p : ℕ)
    (hL : 1 ≤ L) (hC : 16 * C ≤ L) (hN : (N : ℝ) ≤ C * L ^ n) :
    4 * (L ^ (n + p + 1))⁻¹ * N ≤ (L ^ p)⁻¹ / 4 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    _ ≤ 4 * (L ^ (n + p + 1))⁻¹ * (C * L ^ n) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (16 * C / L) * ((L ^ p)⁻¹ / 4) := by
      rw [pow_succ, pow_add]
      field_simp
      ring
    _ ≤ 1 * ((L ^ p)⁻¹ / 4) := mul_le_mul_of_nonneg_right
      ((div_le_one hLp).mpr hC) (by positivity)
    _ = (L ^ p)⁻¹ / 4 := one_mul _

namespace EffectCircuit
variable {P Phys Env : Type} [Fintype Phys] [Fintype Env] [DecidableEq Phys]

/-- Actual gate approximations at a fixed higher inverse-polynomial accuracy
produce a contraction circuit within one quarter of the requested physical
error. The original arbitrary gate maps remain the comparison operator. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_inv_pow
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (L C : ℝ) (n p : ℕ) (hL : 1 ≤ L) (hC : 16 * C ≤ L)
    (hN : (w.expandedGateCount : ℝ) ≤ C * L ^ n)
    (h : w.IsGateApproximation (L ^ (n + p + 1))⁻¹ G)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    let hδ : 0 ≤ (L ^ (n + p + 1))⁻¹ := by positivity
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (K ((w.rescaledOriginal hδ G h).eval x))
        (K ((w.rescaledOriginal hδ G h).eval x))) -
        w.physicalDensityWithGateMaps G K x) ≤ (L ^ p)⁻¹ / 4 := by
  intro hδ
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le hδ G h K x hx).trans
    (gateApproximation_error_inv_pow_le L C _ n p hL hC hN)

end EffectCircuit
end TNLean.PEPS.PairEffect
