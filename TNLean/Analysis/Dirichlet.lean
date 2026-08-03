/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Dirichlet's simultaneous approximation theorem

**Wolf Lemma 6.1**: Given $m$ real numbers $x_1,\dots,x_m$ and an integer $q>1$,
there exist integers $n,p_1,\dots,p_m$ such that
$$
1 \le n \le q^m \quad\text{and}\quad |x_k n - p_k| \le \frac{1}{q}\quad \forall k.
$$

The proof uses the pigeonhole principle.

## Main result

* `exists_int_near_mul_simultaneous`: the full Wolf Lemma 6.1 statement.
-/

open Finset

namespace Dirichlet

variable {m : ℕ}

private lemma int_toNat_lt_of_nonneg_lt {z : ℤ} {q : ℕ} (hz_nonneg : 0 ≤ z) (hz_lt : z < (q : ℤ)) :
    z.toNat < q := by
  rw [Int.toNat_lt hz_nonneg]
  exact hz_lt

/-- **Wolf Lemma 6.1** (Dirichlet's simultaneous approximation theorem). -/
theorem exists_int_near_mul_simultaneous (x : Fin m → ℝ) (q : ℕ) (hq1 : 1 < q) :
    ∃ (n : ℕ) (p : Fin m → ℤ), 1 ≤ n ∧ n ≤ q ^ m ∧
      ∀ k : Fin m, |(x k) * (n : ℝ) - (p k : ℝ)| ≤ 1 / (q : ℝ) := by
  have hqpos : q > 0 := by omega
  -- Floor cell index: ⌊q·{n·xₖ}⌋
  let z (n : ℕ) (k : Fin m) : ℤ := ⌊(q : ℝ) * Int.fract ((x k) * (n : ℝ))⌋
  have hz_nonneg (n : ℕ) (k : Fin m) : 0 ≤ z n k :=
    Int.floor_nonneg.mpr (by nlinarith [Int.fract_nonneg ((x k) * (n : ℝ))])
  have hz_lt (n : ℕ) (k : Fin m) : z n k < (q : ℤ) := by
    dsimp [z]
    have h : (⌊(q : ℝ) * Int.fract ((x k) * (n : ℝ))⌋ : ℝ) < (q : ℝ) := by
      calc
        _ ≤ (q : ℝ) * Int.fract ((x k) * (n : ℝ)) := Int.floor_le _
        _ < (q : ℝ) * 1 := by gcongr; exact Int.fract_lt_one _
        _ = (q : ℝ) := by simp
    exact_mod_cast h
  let cellIdx (n : ℕ) (k : Fin m) : Fin q :=
    ⟨(z n k).toNat, int_toNat_lt_of_nonneg_lt (hz_nonneg n k) (hz_lt n k)⟩
  let f : Fin (q ^ m + 1) → Fin m → Fin q := fun i => cellIdx i.val
  -- Pigeonhole
  have card_lt : Fintype.card (Fin m → Fin q) < Fintype.card (Fin (q ^ m + 1)) := by simp
  obtain ⟨n₁, n₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f card_lt
  -- heq gives cell equality
  have hcell (k : Fin m) : cellIdx n₁.val k = cellIdx n₂.val k := by
    simpa [f] using congrFun heq k
  have h_toNat_eq (k : Fin m) : (z n₁.val k).toNat = (z n₂.val k).toNat := by
    simpa [cellIdx] using congrArg Fin.val (hcell k)
  have h_floor_eq (k : Fin m) : z n₁.val k = z n₂.val k := by
    calc
      z n₁.val k = ((z n₁.val k).toNat : ℤ) := (Int.toNat_of_nonneg (hz_nonneg _ _)).symm
      _ = ((z n₂.val k).toNat : ℤ) := by simp [h_toNat_eq k]
      _ = z n₂.val k := Int.toNat_of_nonneg (hz_nonneg _ _)
  have h_floor_eq_real (k : Fin m) :
      (⌊(q : ℝ) * Int.fract ((x k) * (n₁.val : ℝ))⌋ : ℝ) =
      (⌊(q : ℝ) * Int.fract ((x k) * (n₂.val : ℝ))⌋ : ℝ) := by exact_mod_cast h_floor_eq k

  -- Key lemma: equal floors => |fract a - fract b| ≤ 1/q
  have hqpos' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have fract_bound_lemma (a b : ℝ) (hab : (⌊(q : ℝ) * a⌋ : ℝ) = (⌊(q : ℝ) * b⌋ : ℝ)) :
      |a - b| ≤ 1 / (q : ℝ) := by
    have h_floor_a : (⌊(q : ℝ) * a⌋ : ℝ) ≤ (q : ℝ) * a := Int.floor_le _
    have h_floor_b : (⌊(q : ℝ) * b⌋ : ℝ) ≤ (q : ℝ) * b := Int.floor_le _
    have h_add_a : (q : ℝ) * a < (⌊(q : ℝ) * a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h_add_b : (q : ℝ) * b < (⌊(q : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have ha_lt : (q : ℝ) * a - (q : ℝ) * b < 1 := by linarith
    have hb_lt : (q : ℝ) * b - (q : ℝ) * a < 1 := by linarith
    have habs_lt_one : |(q : ℝ) * a - (q : ℝ) * b| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have habs_factor : |(q : ℝ) * a - (q : ℝ) * b| = (q : ℝ) * |a - b| := by
      have h_eq : (q : ℝ) * a - (q : ℝ) * b = (q : ℝ) * (a - b) := by ring
      rw [h_eq, abs_mul, abs_of_nonneg (by exact_mod_cast hqpos.le)]
    rw [habs_factor] at habs_lt_one
    have h_bound : |a - b| < 1 / (q : ℝ) := by
      calc
        |a - b| = ((q : ℝ) * |a - b|) / (q : ℝ) := by field_simp [hqpos'.ne']
        _ < 1 / (q : ℝ) := div_lt_div_of_pos_right habs_lt_one hqpos'
    exact h_bound.le

  -- Determine ordering
  have h_vals_ne : (n₁ : ℕ) ≠ (n₂ : ℕ) := by
    intro h_eq; apply hne; exact Fin.ext h_eq
  rcases Nat.lt_or_gt_of_ne h_vals_ne with (hlt | hgt)
  · -- n₁.val < n₂.val
    set n := n₂.val - n₁.val with hn_def
    have hn_pos : 1 ≤ n := by
      have hpos : 0 < n := Nat.sub_pos_of_lt hlt
      omega
    have hmax_n₂ : n₂.val ≤ q ^ m := by
      have h := Fin.is_lt n₂; exact Nat.le_of_lt_succ h
    have hn_le : n ≤ q ^ m := Nat.le_trans (Nat.sub_le _ _) hmax_n₂
    refine ⟨n, fun k => ⌊(x k) * (n₂.val : ℝ)⌋ - ⌊(x k) * (n₁.val : ℝ)⌋, hn_pos, hn_le, ?_⟩
    intro k
    have hn_eq_real : (n : ℝ) = (n₂.val : ℝ) - (n₁.val : ℝ) := by
      rw [hn_def, Nat.cast_sub (Nat.le_of_lt hlt)]
    have hb := fract_bound_lemma (Int.fract ((x k) * (n₁.val : ℝ)))
      (Int.fract ((x k) * (n₂.val : ℝ))) (h_floor_eq_real k)
    -- Need to relate (x k)*(n₂-n₁) - (⌊xₖ·n₂⌋ - ⌊xₖ·n₁⌋) to fract(n₁) - fract(n₂)
    have hcalc : (x k) * ((n₂.val : ℝ) - (n₁.val : ℝ)) =
        ((⌊(x k) * (n₂.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₁.val : ℝ)⌋ : ℝ)) +
        (Int.fract ((x k) * (n₂.val : ℝ)) - Int.fract ((x k) * (n₁.val : ℝ))) := by
      calc
        (x k) * ((n₂.val : ℝ) - (n₁.val : ℝ))
            = ((x k) * (n₂.val : ℝ)) - ((x k) * (n₁.val : ℝ)) := by ring
        _ = (((⌊(x k) * (n₂.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n₂.val : ℝ))) -
             ((⌊(x k) * (n₁.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n₁.val : ℝ)))) := by
          simp [Int.floor_add_fract]
        _ = ((⌊(x k) * (n₂.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₁.val : ℝ)⌋ : ℝ)) +
            (Int.fract ((x k) * (n₂.val : ℝ)) - Int.fract ((x k) * (n₁.val : ℝ))) := by ring
    have h_target : |(x k) * (n : ℝ) - (↑(⌊(x k) * (n₂.val : ℝ)⌋ - ⌊(x k) * (n₁.val : ℝ)⌋) : ℝ)| ≤
        1 / (q : ℝ) := by
      rw [hn_eq_real]
      calc
        |(x k) * ((n₂.val : ℝ) - (n₁.val : ℝ)) -
          (↑(⌊(x k) * (n₂.val : ℝ)⌋ - ⌊(x k) * (n₁.val : ℝ)⌋) : ℝ)|
            = |(x k) * ((n₂.val : ℝ) - (n₁.val : ℝ)) -
              ((⌊(x k) * (n₂.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₁.val : ℝ)⌋ : ℝ))| := by simp
        _ = |Int.fract ((x k) * (n₂.val : ℝ)) - Int.fract ((x k) * (n₁.val : ℝ))| := by
          rw [hcalc]; simp
        _ ≤ 1 / (q : ℝ) := by rw [abs_sub_comm]; exact hb
    simpa using h_target
  · -- n₂.val < n₁.val: symmetric
    set n := n₁.val - n₂.val with hn_def
    have hn_pos : 1 ≤ n := by
      have hpos : 0 < n := Nat.sub_pos_of_lt hgt
      omega
    have hmax_n₁ : n₁.val ≤ q ^ m := by
      have h := Fin.is_lt n₁; exact Nat.le_of_lt_succ h
    have hn_le : n ≤ q ^ m := Nat.le_trans (Nat.sub_le _ _) hmax_n₁
    refine ⟨n, fun k => ⌊(x k) * (n₁.val : ℝ)⌋ - ⌊(x k) * (n₂.val : ℝ)⌋, hn_pos, hn_le, ?_⟩
    intro k
    have hn_eq_real : (n : ℝ) = (n₁.val : ℝ) - (n₂.val : ℝ) := by
      rw [hn_def, Nat.cast_sub (Nat.le_of_lt hgt)]
    have hb := fract_bound_lemma (Int.fract ((x k) * (n₂.val : ℝ)))
      (Int.fract ((x k) * (n₁.val : ℝ))) (by simpa using (h_floor_eq_real k).symm)
    have hcalc : (x k) * ((n₁.val : ℝ) - (n₂.val : ℝ)) =
        ((⌊(x k) * (n₁.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₂.val : ℝ)⌋ : ℝ)) +
        (Int.fract ((x k) * (n₁.val : ℝ)) - Int.fract ((x k) * (n₂.val : ℝ))) := by
      calc
        (x k) * ((n₁.val : ℝ) - (n₂.val : ℝ))
            = ((x k) * (n₁.val : ℝ)) - ((x k) * (n₂.val : ℝ)) := by ring
        _ = (((⌊(x k) * (n₁.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n₁.val : ℝ))) -
             ((⌊(x k) * (n₂.val : ℝ)⌋ : ℝ) + Int.fract ((x k) * (n₂.val : ℝ)))) := by
          simp [Int.floor_add_fract]
        _ = ((⌊(x k) * (n₁.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₂.val : ℝ)⌋ : ℝ)) +
            (Int.fract ((x k) * (n₁.val : ℝ)) - Int.fract ((x k) * (n₂.val : ℝ))) := by ring
    have h_target : |(x k) * (n : ℝ) - (↑(⌊(x k) * (n₁.val : ℝ)⌋ - ⌊(x k) * (n₂.val : ℝ)⌋) : ℝ)| ≤
        1 / (q : ℝ) := by
      rw [hn_eq_real]
      calc
        |(x k) * ((n₁.val : ℝ) - (n₂.val : ℝ)) -
          (↑(⌊(x k) * (n₁.val : ℝ)⌋ - ⌊(x k) * (n₂.val : ℝ)⌋) : ℝ)|
            = |(x k) * ((n₁.val : ℝ) - (n₂.val : ℝ)) -
              ((⌊(x k) * (n₁.val : ℝ)⌋ : ℝ) - (⌊(x k) * (n₂.val : ℝ)⌋ : ℝ))| := by simp
        _ = |Int.fract ((x k) * (n₁.val : ℝ)) - Int.fract ((x k) * (n₂.val : ℝ))| := by
          rw [hcalc]; simp
        _ ≤ 1 / (q : ℝ) := by rw [abs_sub_comm]; exact hb
    simpa using h_target

end Dirichlet
