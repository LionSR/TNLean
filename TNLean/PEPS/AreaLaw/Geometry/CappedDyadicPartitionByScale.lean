/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartition
import Mathlib.Basic.Real.Basic

/-!
# Summation of a capped dyadic partition by scale

A real weight that depends only on the side-length exponent can be summed
over the selected dyadic squares by counting the squares at each scale.
The identity holds for every finite lattice set, including the empty set,
and every cap, including cap zero. No sign condition on the weight is needed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, the finite geometric summation in the covering argument
of Lemma 9.4, `08-scanner.tex`, lines 656–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the finite summation identity used before the weighted estimate.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A scale-dependent weight sums to the weighted cardinalities of the
actual scale classes in the capped partition. Source: Lemma 9.4,
`08-scanner.tex`, lines 656–664. -/
theorem sum_cappedDyadicPartition_by_scale
    (S : Finset (ℤ × ℤ)) (K : ℕ) (f : ℕ → ℝ) :
    (∑ c ∈ cappedDyadicPartition S K, f c.1) =
      ∑ k ∈ Finset.range (K + 1),
        (((cappedDyadicPartition S K).filter (fun c ↦ c.1 = k)).card : ℝ) * f k := by
  have hmap : ∀ c ∈ cappedDyadicPartition S K, c.1 ∈ Finset.range (K + 1) :=
    fun c hc ↦ Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((mem_cappedDyadicPartition S K c.1 c.2).mp hc).1)
  have h := Finset.sum_fiberwise_of_maps_to' (g := Prod.fst)
    (s := cappedDyadicPartition S K) (t := Finset.range (K + 1)) hmap f
  simpa only [Finset.sum_const, nsmul_eq_mul] using h.symm

end TNLean.PEPS.AreaLaw.Geometry
