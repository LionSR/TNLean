/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceSamplingPolynomial
import TNLean.PEPS.Approximation.SourceCircuitResourceBounds

/-!
# Uniform polynomial bounds for effect elimination

The stack length is chosen from the original coefficient sum and number of
gates. At inverse-power accuracy its explicit power bound gives the same type
of bound for every branch-label set of the constructed source-only circuit.
No private dimension or source rank enters these estimates.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175,
199–229 and 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
open TNLean.PEPS.Approximation

/-- The stack count at the actual per-gate error budget has the same explicit
ceiling formula as the source sample count, with cost equal to `r * S`. -/
theorem stackLength_sourceGateBudget_eq (r N : ℕ) (S ε : ℝ) :
    stackLength r S (sourceGateBudget ε N) = sourceSamplingCount N (r * S) ε := by
  unfold stackLength sourceGateBudget sourceSamplingCount
  congr 2
  rw [div_div_eq_mul_div]
  ring

/-- Original power bounds give a uniform power bound for the actual chosen
stack length, including when there are no nonprivate gate occurrences. -/
theorem stackLength_sourceGateBudget_lt_of_power_bounds (r N : ℕ)
    (S L C_N C_S : ℝ) (n s p : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s) :
    (stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) : ℝ) <
      (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) * L ^ (2 * (n + s + p)) := by
  rw [stackLength_sourceGateBudget_eq]
  apply sourceSamplingCount_lt_inv_pow N ((r : ℝ) * S) L C_N (r * C_S)
    n s p hL hCN (by positivity) (by positivity) hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hSbound (Nat.cast_nonneg r)

/-- The actual replacement monomial bound is polynomial in the original
uniform bounds. The effect count is a fixed exponent, not a private dimension. -/
theorem replacementMonomialBound_le_of_power_bounds (K r N : ℕ)
    (S L C_K C_N C_S : ℝ) (a n s p : ℕ)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hK : (K : ℝ) ≤ C_K * L ^ a)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s) :
    ((K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r : ℕ) : ℝ) ≤
      C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) ^ r *
        L ^ (a + 2 * r * (n + s + p)) := by
  have hm := (stackLength_sourceGateBudget_lt_of_power_bounds r N S L C_N C_S
    n s p hL hCN hCS hS hN hSbound).le
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ (C_K * L ^ a) *
        ((64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) * L ^ (2 * (n + s + p))) ^ r := by
      gcongr
    _ = _ := by
      rw [mul_pow, ← pow_mul, pow_add]
      have he : 2 * (n + s + p) * r = 2 * r * (n + s + p) := by ring
      rw [he]
      ring

namespace OriginalCircuit

/-- Every chronological gate of the actual replacement has a uniform polynomial
branch count, obtained from the original circuit's monomial and effect bounds. -/
theorem card_branchLabels_replacement_le_power
    {P : Type} {a b : Layout P} (w : OriginalCircuit a b)
    (K r N : ℕ) (S L C_K C_N C_S : ℝ) (u n s p : ℕ)
    (hw : w.IsExpansionBounded r S) (hmonomial : w.IsMonomialBounded K)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hK : (K : ℝ) ≤ C_K * L ^ u)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s)
    (hδ : 0 < sourceGateBudget (L ^ p)⁻¹ N)
    (j : (w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hw)).gateLocations) :
      (Fintype.card ((w.produce.replacement hδ w.isAllowed_produce
        ((w.isExpansionBounded_produce_iff r S).mpr hw)).branchLabels j) : ℝ) ≤
        C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) ^ r *
          L ^ (u + 2 * r * (n + s + p)) := by
  have h := (isExpansionBounded_replacement hδ w hw hmonomial).at_gate j
  have hc : (Fintype.card ((w.produce.replacement hδ w.isAllowed_produce
      ((w.isExpansionBounded_produce_iff r S).mpr hw)).branchLabels j) : ℝ) ≤
      ((K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r : ℕ) : ℝ) := by
    exact_mod_cast h.1
  exact hc.trans (replacementMonomialBound_le_of_power_bounds K r N S L C_K C_N C_S
    u n s p hL hCK hCN hCS hS hK hN hSbound)

end OriginalCircuit

end TNLean.PEPS.PairEffect
