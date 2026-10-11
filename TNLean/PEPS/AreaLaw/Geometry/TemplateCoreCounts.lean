/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateMixedSquares

/-!
# Selected dyadic squares of the template core

For a cap comparable to the template scale, the actual capped partition of
`T.points` has at most `18*n/u` selected squares at the cap and `4*n/u` below it.
These estimates use the template area and mixed-parent counts, respectively.
They require no cut, separation, Hamiltonian, or supplied counting hypotheses.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 662–664, revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
The weighted sum and entropy conclusions are separate results.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- At a cap whose doubled side exceeds the template scale, area controls the
selected core squares. This also includes cap zero. -/
theorem Template.card_cappedDyadicPartition_at_cap_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 1 ≤ Ctpl) (K : ℕ) (hs : s₀ < 2 ^ (K + 1)) :
    2 ^ K * ((cappedDyadicPartition T.points K).filter (fun c ↦ c.1 = K)).card ≤
      18 * n := by
  have harea := (Geometry.card_cappedDyadicPartition_at_cap_le T.points K).trans
    (template_card_le T hC)
  have hpow : 4 ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  rw [hpow] at harea
  have hsize := Nat.mul_le_mul_left (9 * n) (Nat.le_of_lt hs)
  rw [pow_succ] at hsize
  apply le_of_mul_le_mul_left (a := 2 ^ K) _ (by positivity)
  nlinarith

/-- Below a cap of side at most the template scale, a selected square has a
mixed parent of side at most that scale. The resulting constant `4` is stronger
than the `6` obtained by bounding only the child side. -/
theorem Template.card_cappedDyadicPartition_below_cap_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (K k : ℕ)
    (hK : 2 ^ K ≤ s₀) (hk : k < K) :
    2 ^ k * ((cappedDyadicPartition T.points K).filter (fun c ↦ c.1 = k)).card ≤
      4 * n := by
  have hparent := T.card_mixedDyadicIndices_le hC (k + 1)
  have hchildren := Nat.mul_le_mul_left (2 ^ k)
    (Geometry.card_cappedDyadicPartition_below_cap_le T.points K k hk)
  have hscale : (24 : ℝ) * T.pieceCount * (s₀ + 1) ≤ n := by
    calc
      _ ≤ Ctpl * T.pieceCount * (s₀ + 1) := by gcongr
      _ ≤ n := T.scale
  have hn : 24 * T.pieceCount * (s₀ + 1) ≤ n := by exact_mod_cast hscale
  have hside : 2 ^ (k + 1) ≤ s₀ :=
    (pow_le_pow_right₀ (by decide) (by omega)).trans hK
  have hsize := Nat.mul_le_mul_left (24 * T.pieceCount) hside
  rw [pow_succ] at hparent hsize
  nlinarith

end TNLean.PEPS.AreaLaw.Geometry
