/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateCoreCounts
import TNLean.PEPS.AreaLaw.Geometry.DyadicWeightedSum

/-!
# Weighted dyadic covering of the actual template core

The actual capped partition of a template has a bounded sum of side lengths
to every power `1 + e`, for `e > 0`. The cap and lower-scale counts come from
`TemplateCoreCounts`; the finite arithmetic comes from `DyadicWeightedSum`.
No counting bound, separation or entropy conclusion is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 662–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The weighted sum over the actual capped template core partition, with an
explicit exponent-dependent constant. Source: Lemma 9.4, lines 662–664. -/
theorem Template.sum_rpow_cappedDyadicPartition_core_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (K : ℕ)
    (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1)) (e : ℝ) (he : 0 < e) :
    ∑ c ∈ cappedDyadicPartition T.points K, ((2 : ℝ) ^ c.1) ^ (1 + e) ≤
      (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by
  classical
  let P := cappedDyadicPartition T.points K
  let a (k : ℕ) : ℝ := ((P.filter fun c ↦ c.1 = k).card : ℝ)
  have hgroup : (∑ c ∈ P, ((2 : ℝ) ^ c.1) ^ (1 + e)) =
      ∑ k ∈ Finset.range (K + 1), a k * ((2 : ℝ) ^ k) ^ (1 + e) := by
    symm
    convert Finset.sum_fiberwise_of_maps_to' (g := Prod.fst)
      (s := P) (t := Finset.range (K + 1))
      (fun c hc ↦ Finset.mem_range.mpr
        (Nat.lt_succ_of_le ((mem_cappedDyadicPartition _ _ _ _).mp hc).1))
      (fun k ↦ ((2 : ℝ) ^ k) ^ (1 + e)) using 1 <;> simp [a]
  have hcap : (2 : ℝ) ^ K * a K ≤ 18 * n := by
    dsimp [a, P]
    exact_mod_cast T.card_cappedDyadicPartition_at_cap_le (by linarith) K hhi
  have hsmall (k : ℕ) (hk : k < K) : (2 : ℝ) ^ k * a k ≤ 4 * n := by
    dsimp [a, P]
    exact_mod_cast T.card_cappedDyadicPartition_below_cap_le hC K k hlo hk
  have hsum := sum_weighted_dyadic_rpow_le a K he (by positivity) hcap hsmall
  have hpower : ((2 : ℝ) ^ K) ^ e ≤ (s₀ : ℝ) ^ e :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) he.le
  have hden : 0 < (2 : ℝ) ^ e - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) he)
  change (∑ c ∈ P, ((2 : ℝ) ^ c.1) ^ (1 + e)) ≤ _
  rw [hgroup]
  calc
    _ ≤ (18 * n + (4 * n) / ((2 : ℝ) ^ e - 1)) * ((2 : ℝ) ^ K) ^ e := hsum
    _ = (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * ((2 : ℝ) ^ K) ^ e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

end TNLean.PEPS.AreaLaw.Geometry
