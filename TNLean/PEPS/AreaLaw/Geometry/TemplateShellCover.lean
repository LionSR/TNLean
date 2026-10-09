/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateMixedSquares
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
      _ ≤ ((ambientDilation T.points j \ T.points) ∪
          (ambientDilation T.points (j + 1) \ ambientDilation T.points j)).card :=
        Finset.card_le_card hcover
      _ ≤ (ambientDilation T.points j \ T.points).card +
          (ambientDilation T.points (j + 1) \ ambientDilation T.points j).card :=
        Finset.card_union_le _ _
      _ ≤ n * j + n := Nat.add_le_add (ih (by omega)) hlayer
      _ = n * (j + 1) := (Nat.mul_succ n j).symm

/-- At a cap comparable to `L`, the selected cap squares have total side at
most `2*n`. Source: Lemma 9.4, lines 644–646. -/
theorem Template.card_cappedDyadicPartition_shell_at_cap_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) (j L K : ℕ)
    (hj : j ≤ L) (hL : L ≤ s₀) (hcap : L < 2 ^ (K + 1)) :
    2 ^ K * ((cappedDyadicPartition (ambientDilation T.points j \ T.points) K).filter
      (fun c ↦ c.1 = K)).card ≤ 2 * n := by
  have ha := card_cappedDyadicPartition_at_cap_le
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
  classical
  let P := cappedDyadicPartition (ambientDilation T.points j \ T.points) K
  let a (k : ℕ) : ℝ := ((P.filter fun c ↦ c.1 = k).card : ℝ)
  have hgroup : (∑ c ∈ P, ((2 : ℝ) ^ c.1) ^ (1 + e)) =
      ∑ k ∈ Finset.range (K + 1), a k * ((2 : ℝ) ^ k) ^ (1 + e) := by
    symm
    convert Finset.sum_fiberwise_of_maps_to' (g := Prod.fst)
      (s := P) (t := Finset.range (K + 1))
      (fun c hc ↦ Finset.mem_range.mpr
        (Nat.lt_succ_of_le ((mem_cappedDyadicPartition _ _ _ _).mp hc).1))
      (fun k ↦ ((2 : ℝ) ^ k) ^ (1 + e)) using 1 <;> simp [a]
  have hfactor (k : ℕ) : a k * ((2 : ℝ) ^ k) ^ (1 + e) =
      ((2 : ℝ) ^ k * a k) * ((2 : ℝ) ^ k) ^ e := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    ring
  have hcap : (2 : ℝ) ^ K * a K ≤ 2 * n := by
    dsimp [a, P]
    exact_mod_cast T.card_cappedDyadicPartition_shell_at_cap_le hC j L K hj hL hhi
  have hsmall (k : ℕ) (hk : k < K) : (2 : ℝ) ^ k * a k ≤ 14 * n := by
    have hsize : 2 ^ k ≤ s₀ :=
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hk)).trans (hlo.trans hL)
    dsimp [a, P]
    exact_mod_cast T.card_cappedDyadicPartition_shell_below_cap_le
      hC j K k (hj.trans hL) hk hsize
  have htwo : 1 < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he
  have hden : 0 < (2 : ℝ) ^ e - 1 := sub_pos.mpr htwo
  have hgeom : (∑ k ∈ Finset.range K, ((2 : ℝ) ^ k) ^ e) ≤
      ((2 : ℝ) ^ K) ^ e / ((2 : ℝ) ^ e - 1) := by
    simp_rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    rw [geom_sum_eq (ne_of_gt htwo)]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hpower : ((2 : ℝ) ^ K) ^ e ≤ (L : ℝ) ^ e :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) he.le
  change (∑ c ∈ P, ((2 : ℝ) ^ c.1) ^ (1 + e)) ≤ _
  rw [hgroup, Finset.sum_range_succ]
  calc
    _ ≤ (∑ k ∈ Finset.range K, (14 * n) * ((2 : ℝ) ^ k) ^ e) +
        (2 * n) * ((2 : ℝ) ^ K) ^ e := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k hk
        rw [hfactor]
        exact mul_le_mul_of_nonneg_right (hsmall k (Finset.mem_range.mp hk))
          (Real.rpow_nonneg (by positivity) _)
      · rw [hfactor]
        exact mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg (by positivity) _)
    _ = (14 * n) * (∑ k ∈ Finset.range K, ((2 : ℝ) ^ k) ^ e) +
        (2 * n) * ((2 : ℝ) ^ K) ^ e := by rw [Finset.mul_sum]
    _ ≤ (14 * n) * (((2 : ℝ) ^ K) ^ e / ((2 : ℝ) ^ e - 1)) +
        (2 * n) * ((2 : ℝ) ^ K) ^ e :=
      add_le_add
        (mul_le_mul_of_nonneg_left hgeom (by positivity : (0 : ℝ) ≤ 14 * n)) le_rfl
    _ = (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * ((2 : ℝ) ^ K) ^ e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

end TNLean.PEPS.AreaLaw.Geometry
