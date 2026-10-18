/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PowerScaleDepth

/-!
# Generation count of the cell partition

In the proof of the conditional information bound for one cell, a nonterminal
active square of side `u` reserves holes of radius `4 u ^ γ` that become the
active squares of the next generation, of side `u' = 8 u ^ γ`. The recursion
stops below a fixed threshold `u_*`, chosen so that `8 u ^ γ ≤ u ^ γ'` for
`u ≥ u_*`, where `γ < γ' < 1`. This module proves the scalar counting part of
that argument:

* a threshold `u_* > 1` with `8 u ^ γ ≤ u ^ γ'` above it exists, namely
  `cellPowerThreshold 8 γ γ'`;
* for every such threshold, a recursion from a cell of side `s` has
  `O(1 + log log (s + e))` generations;
* with at most `b` children per active square, the active squares of all
  generations number at most `C (1 + log s) ^ C` for `s ≥ 1`, with the named constant
  `C = cellGenerationCountConstant γ' u_* b`.

The recursive coloured partition itself is not constructed here, so its tiles
and exceptional sites are not yet related to this count of active squares.

The estimates are the cell-recursion instances of the power-contracting recursion
bounds in `TNLean.PEPS.AreaLaw.Geometry.PowerScaleDepth`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 224–227 (exponents), 240–241 (`t₀ = u ^ γ`), 276–280 (`u' = 8 t₀`) and
  302–311 (stopping threshold, generation count, and tile count).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.AreaLaw.Geometry

/-- The child side `u' = 8 u ^ γ` of an active square of side `u`.
Source: Lemma 3.2, `02-information.tex`, lines 240–241 and 276–280. -/
def cellChildSide (γ u : ℝ) : ℝ := 8 * u ^ γ

/-- The power threshold `max 2 (K ^ (1 / (δ - γ)))` beyond which `K u ^ γ ≤ u ^ δ`, for
`γ < δ`. At `K = 8` and `δ = γ'` it is the stopping threshold of the cell recursion; at
`K = 1000`, `δ = 1` it makes the reserved holes small against the side.
Source: Lemma 3.2, `02-information.tex`, lines 238–240 and 302–307. -/
def cellPowerThreshold (K γ δ : ℝ) : ℝ := max 2 (K ^ (δ - γ)⁻¹)

/-- The power threshold exceeds one. -/
theorem one_lt_cellPowerThreshold (K γ δ : ℝ) : 1 < cellPowerThreshold K γ δ :=
  lt_max_of_lt_left one_lt_two

/-- **Power domination at the named threshold.** For `K > 0` and `γ < δ`,
`K u ^ γ ≤ u ^ δ` for every `u ≥ cellPowerThreshold K γ δ`.
Source: Lemma 3.2, `02-information.tex`, lines 238–240 and 302–307. -/
theorem const_mul_rpow_le_rpow_of_cellPowerThreshold_le {K γ δ : ℝ} (hK : 0 < K)
    (hγδ : γ < δ) {u : ℝ} (hu : cellPowerThreshold K γ δ ≤ u) : K * u ^ γ ≤ u ^ δ := by
  have hε : 0 < δ - γ := sub_pos.mpr hγδ
  have hu0 : 0 < u := lt_of_lt_of_le two_pos (le_of_max_le_left hu)
  have hK' : K ≤ u ^ (δ - γ) := by
    calc K = (K ^ (δ - γ)⁻¹) ^ (δ - γ) := by
          rw [← Real.rpow_mul hK.le, inv_mul_cancel₀ hε.ne', Real.rpow_one]
      _ ≤ u ^ (δ - γ) := Real.rpow_le_rpow (by positivity) (le_of_max_le_right hu) hε.le
  calc K * u ^ γ ≤ u ^ (δ - γ) * u ^ γ := by gcongr
    _ = u ^ δ := by rw [← Real.rpow_add hu0]; ring_nf

/-- A stopping threshold for the cell recursion: for `γ < γ'` there is `u_* > 1`
with `8 u ^ γ ≤ u ^ γ'` for every `u ≥ u_*`, namely `cellPowerThreshold 8 γ γ'`.
Source: Lemma 3.2, `02-information.tex`, lines 302–307. -/
theorem exists_cellChildSide_le_rpow {γ γ' : ℝ} (hγ : γ < γ') :
    ∃ ustar : ℝ, 1 < ustar ∧ ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ' :=
  ⟨cellPowerThreshold 8 γ γ', one_lt_cellPowerThreshold _ _ _,
    fun _ hu ↦ const_mul_rpow_le_rpow_of_cellPowerThreshold_le (by norm_num) hγ hu⟩

/-- Above a stopping threshold with `8 u ^ γ ≤ u ^ γ'`, the child side is positive
and at most `u ^ γ'`. -/
private theorem cellChildSide_pos_le_rpow {γ γ' ustar : ℝ} (hustar : 1 < ustar)
    (hthr : ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ') :
    ∀ u, ustar ≤ u → 0 < cellChildSide γ u ∧ cellChildSide γ u ≤ u ^ γ' := fun u hu ↦
  ⟨by unfold cellChildSide; have : 0 < u := by linarith
      positivity, hthr u hu⟩

/-- **Generation count of the cell recursion.** Let `0 < γ' < 1` and let `u_* > 1`
be a stopping threshold with `8 u ^ γ ≤ u ^ γ'` for `u ≥ u_*`. There is a
constant `C > 0` such that every recursion from a cell of side `s > 0` whose
generations `0, …, m - 1` are nonterminal, that is have side at least `u_*`,
has `m ≤ C + C log log (s + e)`.
Source: Lemma 3.2, `02-information.tex`, lines 302–308. -/
theorem exists_cell_generation_bound {γ γ' ustar : ℝ} (hγ' : 0 < γ') (hγ'1 : γ' < 1)
    (hustar : 1 < ustar) (hthr : ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ') :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → ∀ m : ℕ,
      (∀ i < m, ustar ≤ (cellChildSide γ)^[i] s) →
        (m : ℝ) ≤ C + C * Real.log (Real.log (s + Real.exp 1)) :=
  exists_iterate_depth_bound (cellChildSide_pos_le_rpow hustar hthr) hγ' hγ'1 hustar

/-- The tile-count constant `max (C 2 ^ C) C` of the cell recursion, with
`C = iterateGenerationCountConstant γ' u_* b` the generation-count constant of the
power-contracting recursion at exponent `γ'`, stopping threshold `u_*` and branching bound `b`.
The change from `log (s + e)` to `1 + log s` costs the factor `2 ^ C`.
Source: Lemma 3.2, `02-information.tex`, lines 302–311. -/
def cellGenerationCountConstant (γ' ustar b : ℝ) : ℝ :=
  max (iterateGenerationCountConstant γ' ustar b * 2 ^ iterateGenerationCountConstant γ' ustar b)
    (iterateGenerationCountConstant γ' ustar b)

/-- The tile-count constant is positive. -/
theorem cellGenerationCountConstant_pos {γ' : ℝ} (hγ' : 0 < γ') (hγ'1 : γ' < 1) (ustar : ℝ)
    {b : ℝ} (hb : 0 ≤ b) : 0 < cellGenerationCountConstant γ' ustar b :=
  lt_max_of_lt_right (iterateGenerationCountConstant_pos γ' ustar hb)

/-- **Tile count of the cell recursion, with the named constant.** Let `0 < γ' < 1` and let
`u_* > 1` be a stopping threshold with `8 u ^ γ ≤ u ^ γ'` for `u ≥ u_*`. For a branching bound
`b ≥ 0`, every cell side `s ≥ 1` and every recursion whose generations `0, …, m - 1` are
nonterminal, `∑_{j ≤ m} b ^ j ≤ C (1 + log s) ^ C` with
`C = cellGenerationCountConstant γ' u_* b`.
Source: Lemma 3.2, `02-information.tex`, lines 302–311. -/
theorem cell_generation_count_bound {γ γ' ustar : ℝ} (hγ' : 0 < γ') (hγ'1 : γ' < 1)
    (hustar : 1 < ustar) (hthr : ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ')
    {b : ℝ} (hb : 0 ≤ b) (s : ℝ) (hs : 1 ≤ s) (m : ℕ)
    (hm : ∀ i < m, ustar ≤ (cellChildSide γ)^[i] s) :
    ∑ j ∈ Finset.range (m + 1), b ^ j ≤
      cellGenerationCountConstant γ' ustar b *
        (1 + Real.log s) ^ cellGenerationCountConstant γ' ustar b := by
  have hC := iterateGenerationCountConstant_pos γ' ustar hb
  have hs0 : 0 < s := by linarith
  set y : ℝ := 1 + Real.log s
  have hy1 : 1 ≤ y := by have := Real.log_nonneg hs; linarith
  have hxy : Real.log (s + Real.exp 1) ≤ 2 * y := by
    have h2e : (2 : ℝ) * Real.exp 1 ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have : Real.log (s + Real.exp 1) ≤ Real.log (Real.exp 2 * s) :=
      Real.log_le_log (by positivity) (by
        have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
        nlinarith [mul_le_mul_of_nonneg_right h2e hs0.le,
          mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le,
          mul_le_mul_of_nonneg_right he1 hs0.le])
    rw [Real.log_mul (Real.exp_pos 2).ne' hs0.ne', Real.log_exp] at this
    linarith [Real.log_nonneg hs]
  exact (sum_pow_le_iterateGenerationCountConstant (cellChildSide_pos_le_rpow hustar hthr) hγ' hγ'1
    hustar hb s hs0 m hm).trans (mul_rpow_le_max_mul_rpow hC
      (Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])) hxy hy1)

/-- **Tile count of the cell recursion.** Under the hypotheses of
`exists_cell_generation_bound`, for a branching bound `b ≥ 0` there is a constant
`C > 0` such that, for every cell side `s ≥ 1` and every recursion whose
generations `0, …, m - 1` are nonterminal, the at most `b ^ j` active squares of
each generation `j ≤ m` number in total at most `C (1 + log s) ^ C`. The constant is
`cellGenerationCountConstant γ' u_* b` (`cell_generation_count_bound`).
Source: Lemma 3.2, `02-information.tex`, lines 302–311. -/
theorem exists_cell_generation_count_bound {γ γ' ustar : ℝ} (hγ' : 0 < γ') (hγ'1 : γ' < 1)
    (hustar : 1 < ustar) (hthr : ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ')
    {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s → ∀ m : ℕ,
      (∀ i < m, ustar ≤ (cellChildSide γ)^[i] s) →
        ∑ j ∈ Finset.range (m + 1), b ^ j ≤ C * (1 + Real.log s) ^ C :=
  ⟨_, cellGenerationCountConstant_pos hγ' hγ'1 ustar hb,
    cell_generation_count_bound hγ' hγ'1 hustar hthr hb⟩

end TNLean.PEPS.Approximation
