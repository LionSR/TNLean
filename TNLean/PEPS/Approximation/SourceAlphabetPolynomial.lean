/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitLocations
import TNLean.PEPS.Approximation.DistributedOperatorContraction

/-!
# Polynomial dimensions of the actual source-network alphabets

A star link carries the ordered pair of actual ket and bra branch labels of
its gate occurrence. A sample link carries one of the actual sample indices.
Polynomial bounds on these branch counts and on the sample count therefore
give a polynomial bound on every such virtual dimension, without a ceiling
or a bound on any private memory or source Schmidt rank.

This is a resource bound for the constructed alphabets. Identifying a sampled
physical density with a contraction of local tensors is a separate result.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type} [DecidableEq P] {a b : Layout P}

open Classical in
/-- The actual star and sample alphabets have uniformly polynomial cardinality
when actual gate branch counts and the sample count do. The exact per-link
cardinality is used, so no integral upper bound on a global branch count is
introduced. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem card_sourceNetworkAlphabet_le_of_power_bounds (w : SourceCircuit a b)
    (gates : Finset w.gateLocations) (root : w.gateLocations → P) (k : ℕ)
    (L C_M C_k : ℝ) (u v : ℕ) (hL : 1 ≤ L) (hM0 : 0 ≤ C_M) (hk0 : 0 ≤ C_k)
    (hM : ∀ g ∈ gates, (Fintype.card (w.branchLabels g) : ℝ) ≤ C_M * L ^ u)
    (hk : (k : ℝ) ≤ C_k * L ^ v)
    (e : DistributedOperatorContraction.Link gates w.participants root) :
    (Fintype.card (DistributedOperatorContraction.alphabet gates w.participants root
      (fun g ↦ w.branchLabels g × w.branchLabels g) k e) : ℝ) ≤
        (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) := by
  rw [DistributedOperatorContraction.card_alphabet]
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl p =>
      have hg := ((mem_distributedLinks gates w.participants root _).mp he).1
      change (Fintype.card (w.branchLabels g × w.branchLabels g) : ℝ) ≤ _
      rw [Fintype.card_prod, Nat.cast_mul]
      calc
        _ ≤ (C_M * L ^ u) * (C_M * L ^ u) :=
          mul_le_mul (hM g hg) (hM g hg) (Nat.cast_nonneg _)
            (mul_nonneg hM0 (pow_nonneg (zero_le_one.trans hL) _))
        _ = C_M ^ 2 * L ^ (2 * u) := by rw [Nat.mul_comm 2 u, pow_mul]; ring
        _ ≤ C_M ^ 2 * L ^ (max (2 * u) v) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.le_max_left _ _)) (sq_nonneg C_M)
        _ ≤ (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hk0) (by positivity)
  | inr pair =>
      change (k : ℝ) ≤ _
      calc
        _ ≤ C_k * L ^ v := hk
        _ ≤ C_k * L ^ (max (2 * u) v) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (Nat.le_max_right _ _)) hk0
        _ ≤ (C_M ^ 2 + C_k) * L ^ (max (2 * u) v) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg C_M)) (by positivity)

end TNLean.PEPS.PairEffect.SourceCircuit
