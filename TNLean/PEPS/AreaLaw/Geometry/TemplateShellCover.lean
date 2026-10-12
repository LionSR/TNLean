/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateMixedSquares
import TNLean.PEPS.AreaLaw.Geometry.DyadicWeightedSum
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartitionByScale
import Mathlib.Algebra.Field.GeomSum

/-!
# Weighted dyadic coverings of template shells

The actual capped dyadic partition of a template shell has a controlled sum of
side lengths to the power `1 + e`. The cap contribution follows from shell area;
the smaller scales use the proved mixed-square counts and a geometric sum.
This is the covering estimate in Lemma 9.4, not its entropy conclusion.

Original proofs from OpenAI, *A two-dimensional area law from a global spectral
gap*, September 24, 2026, `08-scanner.tex`, lines 641–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Summing the actual depth layers bounds the shell area, including radius zero.
Source: Lemma 9.4, the cap-scale counting step. -/
theorem Template.card_shell_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j : ℕ) (hj : j ≤ s₀) :
    (ambientDilation T.points j \ T.points).card ≤ n * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcover : ambientDilation T.points (j + 1) \ T.points ⊆
        (ambientDilation T.points j \ T.points) ∪
          (ambientDilation T.points (j + 1) \ ambientDilation T.points j) := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
      tauto
    have hlayer := template_layer_card_le T hC (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hlayer
    calc
      _ ≤ (ambientDilation T.points j \ T.points).card +
          (ambientDilation T.points (j + 1) \ ambientDilation T.points j).card :=
        (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
      _ ≤ n * j + n := Nat.add_le_add (ih (by omega)) hlayer
      _ = n * (j + 1) := (Nat.mul_succ n j).symm

/-- At a cap comparable to `L`, the selected cap squares have total side at
most `2*n`. Source: Lemma 9.4, lines 644–646. -/
theorem Template.card_cappedDyadicPartition_shell_at_cap_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j L K : ℕ)
    (hj : j ≤ L) (hL : L ≤ s₀) (hcap : L < 2 ^ (K + 1)) :
    2 ^ K * ((cappedDyadicPartition (ambientDilation T.points j \ T.points) K).filter
      (fun c ↦ c.1 = K)).card ≤ 2 * n := by
  have ha := Geometry.card_cappedDyadicPartition_at_cap_le
    (ambientDilation T.points j \ T.points) K
  have hs := T.card_shell_le hC j (hj.trans hL)
  have hp : 4 ^ K = 2 ^ K * 2 ^ K := by
    rw [← mul_pow]
    norm_num
  rw [hp] at ha
  rw [pow_succ] at hcap
  have harea : 2 ^ K * (2 ^ K *
      ((cappedDyadicPartition (ambientDilation T.points j \ T.points) K).filter
        (fun c ↦ c.1 = K)).card) ≤ 2 ^ K * (2 * n) := by
    nlinarith [Nat.mul_le_mul_left n hj, Nat.mul_le_mul_left n (Nat.le_of_lt hcap)]
  exact Nat.le_of_mul_le_mul_left harea (by positivity)

/-- The weighted actual shell partition bound. The exponent need only be positive
for this geometric step; the entropy application uses `0 < e < 1`.
Source: Lemma 9.4, lines 641–660. -/
theorem Template.sum_rpow_cappedDyadicPartition_shell_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j L K : ℕ)
    (hj : j ≤ L) (hL : L ≤ s₀) (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (e : ℝ) (he : 0 < e) :
    ∑ c ∈ cappedDyadicPartition (ambientDilation T.points j \ T.points) K,
      ((2 : ℝ) ^ c.1) ^ (1 + e) ≤
        (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by
  exact (sum_rpow_cappedDyadicPartition_le _ K L he (A := 2 * n) (B := 14 * n)
    (by positivity) hlo
    (by exact_mod_cast T.card_cappedDyadicPartition_shell_at_cap_le hC j L K hj hL hhi)
    fun k hk ↦ by
      exact_mod_cast T.card_cappedDyadicPartition_shell_below_cap_le hC j K k (hj.trans hL) hk
        ((Nat.pow_le_pow_right (by omega) hk.le).trans (hlo.trans hL))).trans_eq (by ring)

end TNLean.PEPS.AreaLaw.Geometry
