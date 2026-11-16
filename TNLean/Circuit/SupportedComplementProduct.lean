/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DetectabilityLemma
import TNLean.Circuit.EntropySupport

/-!
# Support of ordered complementary products

Products of complements retain a common support. No commutativity,
projection or positivity assumption is needed. This is the support
argument for the regional parity products in ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1568.
-/

namespace QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι → Fin q)

/-- An ordered complementary product belongs to the same supported-operator
algebra as each selected term. ALVV, arXiv:1602.08828v2,
`def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1568. -/
theorem mem_supportedOperators_complementProd
    (h : ℕ → EuclideanSpace ℂ (ι → Fin q) →L[ℂ] EuclideanSpace ℂ (ι → Fin q))
    (S : Set ι) (n : ℕ)
    (hh : ∀ k, k < n → (T).symm (h k) ∈ supportedOperators q S) :
    (T).symm (ContinuousLinearMap.complementProd h n) ∈ supportedOperators q S := by
  induction n with
  | zero =>
    simpa only [ContinuousLinearMap.complementProd_zero, map_one] using
      one_mem_supportedOperators (d := q) S
  | succ n ih =>
    rw [ContinuousLinearMap.complementProd_succ, map_mul, map_sub, map_one]
    exact mul_mem_supportedOperators
      ((supportedOperators q S).sub_mem (one_mem_supportedOperators S)
        (hh n (Nat.lt_succ_self n))) (ih fun k hk ↦ hh k (Nat.lt_succ_of_lt hk))

end QuantumCircuit
