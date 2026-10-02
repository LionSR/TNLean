/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Module.NatInt

/-!
# Polynomial correction of an approximate idempotent

The Newton correction x ↦ 3x²−2x³ replaces the idempotency defect d=x²−x
by d²(4d−3). This quadratic reduction is the algebraic ingredient of a
continuous selection of a nearby idempotent. If the initial defect has norm
at most 1/16, the corrections converge in every complete normed ring with ‖1‖ ≤ 1.
The resulting limit is idempotent.
No local triviality of varying matrix algebras is asserted here.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

/-- The Newton idempotent correction squares the old defect. -/
theorem idempotent_newton_defect {A : Type*} [Ring A] (x : A) :
    (3 * x ^ 2 - 2 * x ^ 3) ^ 2 - (3 * x ^ 2 - 2 * x ^ 3) =
      (x ^ 2 - x) ^ 2 * (4 * (x ^ 2 - x) - 3) := by
  noncomm_ring [smul_smul]

/-- The Newton correction differs from the original element by its defect
multiplied by twice the original element minus one. -/
theorem idempotent_newton_sub {A : Type*} [Ring A] (x : A) :
    (3 * x ^ 2 - 2 * x ^ 3) - x = -(2 * x - 1) * (x ^ 2 - x) := by
  noncomm_ring [smul_smul]

/-- Twice the corrected element minus one factors through twice the original
element minus one and one minus twice its defect. -/
theorem idempotent_newton_twice_sub_one {A : Type*} [Ring A] (x : A) :
    2 * (3 * x ^ 2 - 2 * x ^ 3) - 1 =
      (2 * x - 1) * (1 - 2 * (x ^ 2 - x)) := by
  noncomm_ring [smul_smul]

open Filter Topology

private theorem norm_natCast_bound {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (n : ℕ) : ‖(n : A)‖ ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖(↑(n + 1) : A)‖ = ‖(n : A) + 1‖ := by simp
      _ ≤ ‖(n : A)‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) + 1 := add_le_add ih hOne
      _ = ↑(n + 1) := by simp

private theorem newton_defect_bound {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) :
    ‖(3 * x ^ 2 - 2 * x ^ 3) ^ 2 - (3 * x ^ 2 - 2 * x ^ 3)‖ ≤
      ‖x ^ 2 - x‖ ^ 2 * (4 * ‖x ^ 2 - x‖ + 3) := by
  rw [idempotent_newton_defect]
  have h4 : ‖(4 : A) * (x ^ 2 - x) - 3‖ ≤ 4 * ‖x ^ 2 - x‖ + 3 := by
    calc
      _ ≤ ‖(4 : A) * (x ^ 2 - x)‖ + ‖(3 : A)‖ := norm_sub_le _ _
      _ ≤ ‖(4 : A)‖ * ‖x ^ 2 - x‖ + ‖(3 : A)‖ :=
        add_le_add (norm_mul_le _ _) le_rfl
      _ ≤ 4 * ‖x ^ 2 - x‖ + 3 := add_le_add
        (mul_le_mul_of_nonneg_right (norm_natCast_bound hOne 4) (norm_nonneg _))
        (norm_natCast_bound hOne 3)
  have hsq : ‖(x ^ 2 - x) ^ 2‖ ≤ ‖x ^ 2 - x‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact (norm_mul_le (x * x - x) (x * x - x)).trans_eq (pow_two _).symm
  exact (norm_mul_le _ _).trans
    (mul_le_mul hsq h4 (norm_nonneg _) (sq_nonneg _))

private theorem newton_defect_contract {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) (h : ‖x ^ 2 - x‖ ≤ 1 / 16) :
    ‖(3 * x ^ 2 - 2 * x ^ 3) ^ 2 - (3 * x ^ 2 - 2 * x ^ 3)‖ ≤ (1 / 4 : ℝ) * ‖x ^ 2 - x‖ := by
  refine (newton_defect_bound hOne x).trans ?_
  have hm : ‖x ^ 2 - x‖ * (4 * ‖x ^ 2 - x‖ + 3) ≤ 1 / 4 := by
    calc
      _ ≤ (1 / 16 : ℝ) * 4 := mul_le_mul h (by linarith)
        (by positivity) (by norm_num)
      _ = 1 / 4 := by norm_num
  calc
    _ = ‖x ^ 2 - x‖ * (‖x ^ 2 - x‖ * (4 * ‖x ^ 2 - x‖ + 3)) := by ring
    _ ≤ ‖x ^ 2 - x‖ * (1 / 4) := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = (1 / 4) * ‖x ^ 2 - x‖ := by ring

private theorem newton_center_bound {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) (h : ‖x ^ 2 - x‖ ≤ 1 / 16) :
    ‖2 * (3 * x ^ 2 - 2 * x ^ 3) - 1‖ ≤ 2 * ‖2 * x - 1‖ := by
  rw [idempotent_newton_twice_sub_one]
  have hk : ‖(1 : A) - 2 * (x ^ 2 - x)‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : A)‖ + ‖(2 : A) * (x ^ 2 - x)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 * ‖x ^ 2 - x‖ := add_le_add hOne
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_natCast_bound hOne 2) (norm_nonneg _)))
      _ ≤ 2 := by linarith
  exact ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left hk (norm_nonneg _))).trans_eq (mul_comm _ _)

private theorem newton_iterate_bounds {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) (h : ‖x ^ 2 - x‖ ≤ 1 / 16) (n : ℕ) :
    ‖((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x ^ 2 -
        ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x‖ ≤ (1 / 4 : ℝ) ^ n * ‖x ^ 2 - x‖ ∧
    ‖2 * ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x - 1‖ ≤ (2 : ℝ) ^ n * ‖2 * x - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsmall : ‖((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x ^ 2 -
        ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x‖ ≤ 1 / 16 := by
      calc
        _ ≤ (1 / 4 : ℝ) ^ n * ‖x ^ 2 - x‖ := ih.1
        _ ≤ 1 * ‖x ^ 2 - x‖ := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (by norm_num) (by norm_num)) (norm_nonneg _)
        _ ≤ 1 / 16 := by simpa using h
    simp only [Function.iterate_succ_apply']
    constructor
    · exact ((newton_defect_contract hOne _ hsmall).trans
        (mul_le_mul_of_nonneg_left ih.1 (by norm_num))).trans_eq (by
          rw [pow_succ]
          ring)
    · exact ((newton_center_bound hOne _ hsmall).trans
        (mul_le_mul_of_nonneg_left ih.2 (by norm_num))).trans_eq (by
          rw [pow_succ]
          ring)

/-- For an initial defect at most 1 / 16, successive Newton corrections have
geometrically summable increments. The estimate needs only norm submultiplicativity
and the bound ‖1‖≤1; it also applies to the zero algebra. -/
theorem idempotent_newton_increment_bound {A : Type*} [NormedRing A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) (h : ‖x ^ 2 - x‖ ≤ 1 / 16) (n : ℕ) :
    ‖((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n + 1]) x -
      ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x‖ ≤
      (‖2 * x - 1‖ * ‖x ^ 2 - x‖) * (1 / 2 : ℝ) ^ n := by
  rw [Function.iterate_succ_apply', idempotent_newton_sub, neg_mul, norm_neg]
  have hb := newton_iterate_bounds hOne x h n
  refine (norm_mul_le _ _).trans
    ((mul_le_mul hb.2 hb.1 (norm_nonneg _) (by positivity)).trans_eq ?_)
  calc
    _ = (‖2 * x - 1‖ * ‖x ^ 2 - x‖) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

/-- Newton correction converges to an idempotent when its initial defect is at
most 1 / 16. Completeness is used only after the geometric increment estimate. -/
theorem idempotent_newton_tendsto_of_small_defect {A : Type*}
    [NormedRing A] [CompleteSpace A]
    (hOne : ‖(1 : A)‖ ≤ 1) (x : A) (hDef : ‖x ^ 2 - x‖ ≤ 1 / 16) :
    ∃ p : A, Tendsto (fun n => ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x)
      atTop (𝓝 p) ∧ p ^ 2 = p := by
  have hC : CauchySeq (fun n => ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x) :=
    SeminormedAddCommGroup.cauchySeq_of_le_geometric (by norm_num : (1 / 2 : ℝ) < 1)
      (fun n => by
        rw [norm_sub_rev]
        exact idempotent_newton_increment_bound hOne x hDef n)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hC
  have hzero : Tendsto (fun n => (1 / 4 : ℝ) ^ n * ‖x ^ 2 - x‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).mul_const ‖x ^ 2 - x‖
  have hnorm : Tendsto (fun n =>
      ‖((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x ^ 2 -
        ((fun x : A => 3 * x ^ 2 - 2 * x ^ 3)^[n]) x‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (newton_iterate_bounds hOne x hDef n).1) hzero
  have hlimit : p ^ 2 - p = 0 := tendsto_nhds_unique
    ((hp.pow 2).sub hp) (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm)
  exact ⟨p, hp, sub_eq_zero.mp hlimit⟩
