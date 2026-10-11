/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitPolynomial

/-!
# A uniform accuracy exponent for approximate gates

For every real target exponent, an explicit fixed integer accuracy exponent
absorbs the polynomial number of gates for every size `L ≥ 2`. The coefficient
of the gate-count polynomial is absorbed in the exponent, so no further
lower bound on the size is required. The resulting density estimate concerns
the actual original gate operators and their rescaled monomial expansions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175 and 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect

/-- A polynomial gate count is absorbed at every size at least two by a
fixed higher accuracy exponent, for an arbitrary real target exponent. -/
theorem gateApproximation_error_real_pow_le (L C p : ℝ) (N n : ℕ)
    (hL : 2 ≤ L) (hN : (N : ℝ) ≤ C * L ^ n) :
    4 * (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ * N ≤ L ^ (-p) / 4 := by
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hC : 16 * C ≤ L ^ ⌈16 * C⌉₊ := by
    calc
      _ ≤ (⌈16 * C⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (2 : ℝ) ^ ⌈16 * C⌉₊ := by
        exact_mod_cast (Nat.lt_pow_self (by decide : 1 < 2) (n := ⌈16 * C⌉₊)).le
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hsmall : (L ^ ⌈p⌉₊)⁻¹ ≤ L ^ (-p) := by
    calc
      _ = L ^ (-(⌈p⌉₊ : ℝ)) := by rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hLone (neg_le_neg (Nat.le_ceil p))
  calc
    _ ≤ 4 * (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ * (C * L ^ n) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (16 * C / L ^ ⌈16 * C⌉₊) * ((L ^ ⌈p⌉₊)⁻¹ / 4) := by
      rw [pow_add, pow_add]
      field_simp
      ring
    _ ≤ 1 * ((L ^ ⌈p⌉₊)⁻¹ / 4) := mul_le_mul_of_nonneg_right
      ((div_le_one (by positivity)).mpr hC) (by positivity)
    _ ≤ L ^ (-p) / 4 := by
      rw [one_mul]
      exact div_le_div_of_nonneg_right hsmall (by norm_num)

namespace EffectCircuit
variable {P Phys Env : Type} [Fintype Phys] [Fintype Env] [DecidableEq Phys]

/-- Actual gate approximations at one fixed integer accuracy exponent give
one quarter of the requested real inverse-power density error, uniformly
for all `L ≥ 2` and independently of private dimensions. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_real_pow
    {a b : Layout P} (w : EffectCircuit a b) (G : w.GateMaps)
    (L C p : ℝ) (n : ℕ) (hL : 2 ≤ L)
    (hN : (w.expandedGateCount : ℝ) ≤ C * L ^ n)
    (h : w.IsGateApproximation (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ G)
    (K : Mem b ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Phys × Env))
    (x : Mem a) (hx : ‖x‖ ≤ 1) :
    let hδ : 0 ≤ (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ := by positivity
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (K ((w.rescaledOriginal hδ G h).eval x))
        (K ((w.rescaledOriginal hδ G h).eval x))) -
        w.physicalDensityWithGateMaps G K x) ≤ L ^ (-p) / 4 := by
  intro hδ
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le hδ G h K x hx).trans
    (gateApproximation_error_real_pow_le L C p _ n hL hN)

end EffectCircuit
end TNLean.PEPS.PairEffect
