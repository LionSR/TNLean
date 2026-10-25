/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.RenyiApproximation

/-! # Axioms of smooth Rényi family approximation -/

open TNLean.MPS.AreaLaw

-- Order zero with a constant smoothed-entropy bound is included in the family theorem.
example {q : ℕ} {lengths : Set ℕ}
    (ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q))
    (hψ : ∀ N, ‖ψ N‖ = 1) {c' : ℝ}
    (hS : ∀ (N : lengths) (k : ℕ), k ∈ Finset.Ico 1 N.val →
      smoothRenyiEntropy (Entropy.regionState (leftBlock N.val k) (ψ N)) 0
        ((N.val : ℝ) ^ (-2 : ℝ)) ≤ c') :
    IsEfficientlyApproximableByMPS ψ := by
  apply isEfficientlyApproximableByMPS_of_smoothRenyiEntropy_le ψ hψ
    (a := 0) (c := 0) (c' := c') (ε := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  intro N k hk
  convert hS N k hk using 1 <;> norm_num

set_option linter.hashCommand false

/-- info: 'TNLean.MPS.AreaLaw.norm_sequentialTruncation_leadingEigenprojection_sub_sq_le_of_smoothing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_sequentialTruncation_leadingEigenprojection_sub_sq_le_of_smoothing

/-- info: 'TNLean.MPS.AreaLaw.exists_normalized_isOpenMPS_of_smoothRenyiEntropy_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_normalized_isOpenMPS_of_smoothRenyiEntropy_lt

/-- info: 'TNLean.MPS.AreaLaw.isEfficientlyApproximableByMPS_of_smoothRenyiEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isEfficientlyApproximableByMPS_of_smoothRenyiEntropy_le
