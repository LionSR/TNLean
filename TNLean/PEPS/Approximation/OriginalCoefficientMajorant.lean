/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GateCoefficientBounds

/-!
# A positive coefficient majorant from the original polynomial bounds

The sampling estimate uses an absolute coefficient-sum bound at least one.
This condition is obtained from the original monomial count and individual
coefficient bounds. The resulting polynomial has uniform constants and no
dependence on private dimensions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–208 and 342–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped NNReal
namespace TNLean.PEPS.PairEffect.OriginalCircuit
variable {P : Type} {a b : Layout P}

/-- Original polynomial monomial and individual coefficient bounds yield a
nonnegative-real coefficient-sum bound at least one. Its displayed polynomial
depends only on the original constants and exponents.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 143–175. -/
theorem exists_one_le_isExpansionBounded_of_termwise_power_bounds
    (w : OriginalCircuit a b) {r K : ℕ} (L C_K C_C : ℝ) (u v : ℕ)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCC : 0 ≤ C_C)
    (hK : w.IsMonomialBounded K) (ht : w.IsTermwiseBounded r (C_C * L ^ v))
    (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    ∃ B : ℝ≥0, 1 ≤ B ∧ w.IsExpansionBounded r (B : ℝ) ∧
      (B : ℝ) ≤ (1 + C_K * C_C) * L ^ (u + v) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB1 : 1 ≤ (1 + C_K * C_C) * L ^ (u + v) :=
    one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right (mul_nonneg hCK hCC)) (one_le_pow₀ hL)
  refine ⟨⟨(1 + C_K * C_C) * L ^ (u + v), zero_le_one.trans hB1⟩,
    hB1, ?_, le_rfl⟩
  apply w.isExpansionBounded_of_isTermwiseBounded hK ht (by positivity)
  calc
    (K : ℝ) * (C_C * L ^ v) ≤ (C_K * L ^ u) * (C_C * L ^ v) :=
      mul_le_mul_of_nonneg_right hKbound (by positivity)
    _ = C_K * C_C * L ^ (u + v) := by rw [pow_add]; ring
    _ ≤ (1 + C_K * C_C) * L ^ (u + v) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

end TNLean.PEPS.PairEffect.OriginalCircuit
