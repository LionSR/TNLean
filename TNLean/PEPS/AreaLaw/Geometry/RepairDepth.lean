/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PowerScaleDepth
import TNLean.PEPS.AreaLaw.Geometry.SimultaneousRepair
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Depth and descendant count of a repair branch

Every child of a nonterminal parent of scale `S` receives the scale `d(S)`, so
the marks of generation `j` descended from an initial mark of scale `S` all have
scale `d^[j] S`. Since `d(S) ≤ S ^ ρ₀`, the logarithms of these scales satisfy
`log d^[j] S ≤ ρ₀ ^ j log S`. A generation whose scale is at least the stopping
scale `S_* > 1` therefore has depth at most `C + C log log (e^e + S)`. With at
most nine children per mark, the marks of the first `m + 1` generations number at
most `∑_{j ≤ m} 9 ^ j ≤ C (log (S + 2)) ^ C`. For an initial mark at layer `k`,
whose scale is at most a fixed multiple of `2 ^ k`, this is at most
`C (k + 1) ^ C`.

The module also proves the scalar threshold `geometry:fine-clearance`: for fixed
`c₁ > 0` and `C_B ≥ 0`, every sufficiently large `u` satisfies
`c₁ u ^ ρ₀ > 2 ⌈C_B u⌉ ^ β`, because `ρ₀ > β`.

The depth and descendant counts are the repair-branch instances of the
power-contracting recursion bounds of `TNLean.PEPS.AreaLaw.Geometry.PowerScaleDepth`.
These are scalar estimates about the iterated removal half-side. They do not
construct the repairs or verify the isolated-star induction.

## Main statements

* `log_repairHalfSide_iterate_le`: `log d^[j] S ≤ ρ₀ ^ j log S`.
* `exists_repair_depth_bound`: the depth bound `j ≤ C + C log log (e^e + S)`.
* `exists_repair_descendant_count_bound`: `geometry:descendant-count`.
* `exists_repair_descendant_count_layer_bound`: the layer form `C (k + 1) ^ C`.
* `eventually_fine_clearance`: `geometry:fine-clearance`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, lines 668–686
  (`geometry:descendant-count`) and lines 761–768 (`geometry:fine-clearance`).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The removal half-side is a power of two, hence positive. -/
theorem repairHalfSide_pos (S : ℝ) : 0 < repairHalfSide S := by
  unfold repairHalfSide
  positivity

/-- One removal step multiplies the logarithm of a positive scale by at most `ρ₀`.
Source: Section 11, `10-geometry.tex`, lines 670–671. -/
theorem log_repairHalfSide_le {S : ℝ} (hS : 0 < S) :
    Real.log (repairHalfSide S) ≤ (Exponents.rho : ℝ) * Real.log S := by
  rw [← Real.log_rpow hS]
  exact Real.log_le_log (repairHalfSide_pos S) (repairHalfSide_le_rpow hS)

/-- Along a repair branch from a positive scale `S`, the generation-`j` scale
satisfies `log d^[j] S ≤ ρ₀ ^ j log S`.
Source: Section 11, `10-geometry.tex`, lines 670–671. -/
theorem log_repairHalfSide_iterate_le {S : ℝ} (hS : 0 < S) (j : ℕ) :
    Real.log (repairHalfSide^[j] S) ≤ (Exponents.rho : ℝ) ^ j * Real.log S := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos : 0 < repairHalfSide^[j] S := by
      cases j with
      | zero => simpa using hS
      | succ j =>
        rw [Function.iterate_succ_apply']
        exact repairHalfSide_pos _
    rw [Function.iterate_succ_apply']
    calc Real.log (repairHalfSide (repairHalfSide^[j] S))
        ≤ (Exponents.rho : ℝ) * Real.log (repairHalfSide^[j] S) :=
          log_repairHalfSide_le hpos
      _ ≤ (Exponents.rho : ℝ) * ((Exponents.rho : ℝ) ^ j * Real.log S) :=
          mul_le_mul_of_nonneg_left ih rho_pos_lt_one.1.le
      _ = (Exponents.rho : ℝ) ^ (j + 1) * Real.log S := by ring

/-- The repair half-side contracts every positive scale to at most its `ρ₀`-th power. -/
private theorem repairHalfSide_pos_le_rpow (u : ℝ) (hu : 0 < u) :
    0 < repairHalfSide u ∧ repairHalfSide u ≤ u ^ (Exponents.rho : ℝ) :=
  ⟨repairHalfSide_pos u, repairHalfSide_le_rpow hu⟩

/-- A generation of a repair branch at scale at least `S_* > 1` has only ancestors
at scale at least `S_*`. -/
private theorem forall_lt_le_repairHalfSide_iterate {Sstar S : ℝ} (hSstar : 1 < Sstar)
    (hS : 0 < S) {m : ℕ} (hm : Sstar ≤ repairHalfSide^[m] S) :
    ∀ i < m + 1, Sstar ≤ repairHalfSide^[i] S := fun i hi ↦
  forall_le_iterate_of_le_iterate repairHalfSide_pos_le_rpow rho_pos_lt_one.1
    rho_pos_lt_one.2.le hSstar.le hS hm i (Nat.lt_succ_iff.mp hi)

/-- **Depth of a repair branch.** For a stopping scale `S_* > 1` there is a constant
`C` such that, along the branch from any positive initial scale `S`, every
generation `j` whose scale `d^[j] S` is at least `S_*` satisfies
`j ≤ C + C log log (e^e + S)`.
Source: Section 11, `10-geometry.tex`, lines 670–675. -/
theorem exists_repair_depth_bound {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S → ∀ j : ℕ, Sstar ≤ repairHalfSide^[j] S →
      (j : ℝ) ≤ C + C * Real.log (Real.log (Real.exp (Real.exp 1) + S)) := by
  obtain ⟨C, hC, hdepth⟩ := exists_iterate_depth_bound
    (fun u hu ↦ repairHalfSide_pos_le_rpow u (by linarith)) rho_pos_lt_one.1
    rho_pos_lt_one.2 hSstar
  refine ⟨C, hC, fun S hS j hj => ?_⟩
  have h := hdepth S hS (j + 1) (forall_lt_le_repairHalfSide_iterate hSstar hS hj)
  have hlog : Real.log (Real.log (S + Real.exp 1)) ≤
      Real.log (Real.log (Real.exp (Real.exp 1) + S)) := by
    have he : Real.exp 1 ≤ Real.exp (Real.exp 1) := by
      have := Real.add_one_le_exp (Real.exp 1)
      linarith
    exact Real.log_le_log (by linarith [one_le_log_add_exp_one hS.le])
      (Real.log_le_log (by positivity) (by linarith))
  push_cast at h
  linarith [mul_le_mul_of_nonneg_left hlog hC.le]

/-- **Descendant count of an initial mark** (`geometry:descendant-count`). For a
stopping scale `S_* > 1` there is a constant `C > 0` such that, for every positive
initial scale `S` and every generation `m` of its branch whose scale `d^[m] S` is
at least `S_*`, the at most `9 ^ j` marks of each generation `j ≤ m` number in
total at most `C (log (S + 2)) ^ C`.
Source: Section 11, `10-geometry.tex`, lines 670–682. -/
theorem exists_repair_descendant_count_bound {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 0 < S → ∀ m : ℕ, Sstar ≤ repairHalfSide^[m] S →
      ∑ j ∈ Finset.range (m + 1), (9 : ℝ) ^ j ≤ C * Real.log (S + 2) ^ C := by
  obtain ⟨C, hC, hcount⟩ := exists_iterate_generation_count_bound
    (fun u hu ↦ repairHalfSide_pos_le_rpow u (by linarith)) rho_pos_lt_one.1
    rho_pos_lt_one.2 hSstar (b := 9) (by norm_num)
  refine ⟨max (C * 2 ^ C) C, lt_max_of_lt_right hC, fun S hS m hm => ?_⟩
  have hall := forall_lt_le_repairHalfSide_iterate hSstar hS hm
  have hS0 : Sstar ≤ S := by simpa using hall 0 (Nat.succ_pos m)
  have hm' : ∀ i < m, Sstar ≤ repairHalfSide^[i] S := fun i hi ↦ hall i (by omega)
  set y : ℝ := Real.log (S + 2)
  have hy1 : 1 ≤ y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hxy : Real.log (S + Real.exp 1) ≤ 2 * y := by
    have : Real.log (S + Real.exp 1) ≤ Real.log (Real.exp 1 * (S + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
    rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp] at this
    linarith
  exact (hcount S hS m hm').trans (mul_rpow_le_max_mul_rpow hC
    (Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])) hxy hy1)

/-- **Descendant count at layer `k`.** If the initial scale is at most `M 2 ^ k`,
the descendant count of `geometry:descendant-count` is at most `C (k + 1) ^ C`,
with `C` depending only on `S_*` and `M`.
Source: Section 11, `10-geometry.tex`, lines 682–686. -/
theorem exists_repair_descendant_count_layer_bound {Sstar : ℝ} (hSstar : 1 < Sstar)
    {M : ℝ} (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ S : ℝ, 0 < S → S ≤ M * 2 ^ k →
      ∀ m : ℕ, Sstar ≤ repairHalfSide^[m] S →
        ∑ j ∈ Finset.range (m + 1), (9 : ℝ) ^ j ≤ C * ((k : ℝ) + 1) ^ C := by
  obtain ⟨C, hC, hcount⟩ := exists_repair_descendant_count_bound hSstar
  set A : ℝ := Real.log (M + 2) + 1 with hA_def
  have hA : 1 ≤ A := by
    have : 0 ≤ Real.log (M + 2) := Real.log_nonneg (by linarith)
    linarith
  refine ⟨max (C * A ^ C) C, lt_max_of_lt_right hC, fun k S hS hSk m hm => ?_⟩
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hlog : Real.log (S + 2) ≤ A * ((k : ℝ) + 1) := by
    calc Real.log (S + 2) ≤ Real.log ((M + 2) * 2 ^ k) :=
          Real.log_le_log (by linarith) (by nlinarith)
      _ = Real.log (M + 2) + (k : ℝ) * Real.log 2 := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
      _ ≤ A * ((k : ℝ) + 1) := by
          have h2 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          have hlM : 0 ≤ Real.log (M + 2) := Real.log_nonneg (by linarith)
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
  have hpos : 0 ≤ Real.log (S + 2) := Real.log_nonneg (by linarith)
  calc ∑ j ∈ Finset.range (m + 1), (9 : ℝ) ^ j ≤ C * Real.log (S + 2) ^ C :=
        hcount S hS m hm
    _ ≤ C * (A * ((k : ℝ) + 1)) ^ C := by gcongr
    _ = C * A ^ C * ((k : ℝ) + 1) ^ C := by
        rw [Real.mul_rpow (by linarith) (by linarith)]
        ring
    _ ≤ max (C * A ^ C) C * ((k : ℝ) + 1) ^ max (C * A ^ C) C := by
        have hexp : ((k : ℝ) + 1) ^ C ≤ ((k : ℝ) + 1) ^ max (C * A ^ C) C :=
          Real.rpow_le_rpow_of_exponent_le hk1 (le_max_right _ _)
        have hpos' : 0 ≤ ((k : ℝ) + 1) ^ C := by positivity
        have hCA : 0 ≤ C * A ^ C := by positivity
        calc C * A ^ C * ((k : ℝ) + 1) ^ C
            ≤ C * A ^ C * ((k : ℝ) + 1) ^ max (C * A ^ C) C :=
              mul_le_mul_of_nonneg_left hexp hCA
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Fine clearance threshold** (`geometry:fine-clearance`). For fixed `c₁ > 0`
and `C_B ≥ 0`, every sufficiently large `u` satisfies
`2 ⌈C_B u⌉ ^ β < c₁ u ^ ρ₀`. This is possible because `ρ₀ > β`.
Source: Section 11, `10-geometry.tex`, lines 761–768. -/
theorem eventually_fine_clearance {c₁ CB : ℝ} (hc₁ : 0 < c₁) (hCB : 0 ≤ CB) :
    ∀ᶠ u : ℝ in atTop,
      2 * (⌈CB * u⌉₊ : ℝ) ^ (Exponents.beta : ℝ) < c₁ * u ^ (Exponents.rho : ℝ) := by
  have hβ : 0 < (Exponents.beta : ℝ) := by
    norm_num [Exponents.beta, Exponents.boxError]
  have hβρ : (Exponents.beta : ℝ) < (Exponents.rho : ℝ) := by
    exact_mod_cast Exponents.geometry_gaps.2.2.2.2.1
  set B : ℝ := 2 * (CB + 1) ^ (Exponents.beta : ℝ) with hB_def
  have hB : 0 < B := by positivity
  have hlim : Tendsto (fun u : ℝ ↦ u ^ (-((Exponents.rho : ℝ) - (Exponents.beta : ℝ))))
      atTop (nhds 0) := tendsto_rpow_neg_atTop (by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hc₁ hB)),
    eventually_ge_atTop (1 : ℝ)] with u hu hu1
  have hu0 : 0 < u := by linarith
  have hceil : (⌈CB * u⌉₊ : ℝ) ≤ (CB + 1) * u := by
    have := Nat.ceil_lt_add_one (mul_nonneg hCB hu0.le)
    nlinarith
  have hsplit : u ^ (Exponents.beta : ℝ) =
      u ^ (-((Exponents.rho : ℝ) - (Exponents.beta : ℝ))) * u ^ (Exponents.rho : ℝ) := by
    rw [← Real.rpow_add hu0]
    ring_nf
  have hρpos : 0 < u ^ (Exponents.rho : ℝ) := Real.rpow_pos_of_pos hu0 _
  calc 2 * (⌈CB * u⌉₊ : ℝ) ^ (Exponents.beta : ℝ)
      ≤ 2 * ((CB + 1) * u) ^ (Exponents.beta : ℝ) := by
        gcongr
    _ = B * u ^ (Exponents.beta : ℝ) := by
        rw [Real.mul_rpow (by linarith) hu0.le, hB_def]
        ring
    _ = B * u ^ (-((Exponents.rho : ℝ) - (Exponents.beta : ℝ))) *
          u ^ (Exponents.rho : ℝ) := by
        rw [hsplit]
        ring
    _ < B * (c₁ / B) * u ^ (Exponents.rho : ℝ) := by
        gcongr
    _ = c₁ * u ^ (Exponents.rho : ℝ) := by
        field_simp

end TNLean.PEPS.AreaLaw.Geometry
