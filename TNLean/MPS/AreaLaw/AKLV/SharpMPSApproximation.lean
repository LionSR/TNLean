/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.SharpPerCutApproximation
import TNLean.MPS.AreaLaw.AKLV.CutApproximationTail
import TNLean.MPS.AreaLaw.AKLV.SequentialApproximation

/-!
# Sharp AKLV matrix product approximation by sequential truncation

The physical accuracy-dependent windows give a Schmidt-tail estimate at
every cut. Their uniform fourth-root logarithmic rank bound passes to the
actual normalized ordered product of leading regional spectral projections.
Only the general sequential truncation and normalization inequalities are
used for the final passage to a matrix product state.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517. The actual first excited
energy is specified in the physical data. No window-fit, upper-gap,
local-dimension, filter-rank or parameter-feasibility hypothesis is added.
The local support and normalization corrections are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

**Scope restriction (actual first excited energy):** The positive projector
lower bound is also required to be an actual first excitation. The theorem
is not asserted for an arbitrary lower bound without choosing an actual
gap. The local support and normalization conventions are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The logarithmic accuracy scale used by sequential truncation, written in
terms of the chain length and final norm accuracy. -/
theorem aklvAccuracyLog_sequential {L : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    aklvAccuracyLog (epsilon ^ 2 / (16 * ((L : ℝ) + 1))) =
      Real.log (2048 * ((L : ℝ) + 1) / epsilon ^ 2) := by
  unfold aklvAccuracyLog
  congr 1
  field_simp
  ring

/-- Actual uniform Schmidt tails and their normalized sequential matrix product
approximation, with both the fourth-root and LVV-form logarithmic rank bounds
of the AKLV accuracy-dependent window construction. The universal constants are chosen
before the physical chain, gap and requested accuracy. -/
theorem exists_aklv_sharp_physical_sequential_mps_approximation :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ (L q : ℕ)
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → mu + g ∈ spectrum ℝ (∑ j, h j) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let rho := epsilon ^ 2 / (16 * ((L : ℝ) + 1))
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let z := aklvAccuracyLog rho
      let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D := aklvAccuracyRankBound q s0 g rho
      Real.log (D : ℝ) ≤
        C * (u ^ 3 / g + Real.sqrt (Real.sqrt (z ^ 3 / g)) * (u + Real.log (z + 1))) ∧
      Real.log (D : ℝ) ≤ 11 * C * (u ^ 3 / g) * z ∧
      Real.log (D : ℝ) ≤ 11 * C * (u ^ 3 / g) *
        Real.log (2048 * ((L : ℝ) + 1) / epsilon ^ 2) ∧
      (∀ k : ℕ, k ≤ L →
        1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
          (leftBlock L k) Ω).kyFanNorm D ≤ rho) ∧
      aklvSpectralTruncation Ω D ≠ 0 ∧
      ‖aklvNormalizedSpectralTruncation Ω D‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ aklvNormalizedSpectralTruncation Ω D x) ∧
      ‖aklvNormalizedSpectralTruncation Ω D - Ω‖ ≤ epsilon := by
  obtain ⟨A, C, hA, hC, hphysical⟩ := exists_aklv_sharp_physical_per_cut_approximation
  refine ⟨A, C, hA, hC, ?_⟩
  intro L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited epsilon hepsilon hepsilon1
    rho u z s0 D
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp only [rho]
    apply (div_le_iff₀ (by positivity : 0 < 16 * ((L : ℝ) + 1))).2
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  obtain ⟨_hq, _hg1, hlog, hlogLVV, hcut⟩ :=
    hphysical L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited rho hrho hrho1
  have hlogExplicit : Real.log (D : ℝ) ≤ 11 * C * (u ^ 3 / g) *
      Real.log (2048 * ((L : ℝ) + 1) / epsilon ^ 2) := by
    rw [← aklvAccuracyLog_sequential hepsilon]
    exact hlogLVV
  have htail (k : ℕ) (hk : k ≤ L) :
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) Ω).kyFanNorm D ≤ rho := by
    obtain ⟨y, hy, herror, _hoverlap, hrank, _hactual⟩ := hcut k hk
    exact one_sub_kyFanNorm_le_of_unit_cut_rank_approximation Ω y hΩ hy herror hrank
  refine ⟨hlog, hlogLVV, hlogExplicit, htail, ?_⟩
  exact aklvNormalizedSpectralTruncation_spec Ω hΩ hepsilon hepsilon1 fun k hk ↦
    htail k (Finset.mem_Ico.mp hk).2.le

/-- On a fixed-gap interval, the actual sequentially truncated matrix product
state has the cubic local-dimension dependence printed in the AKLV estimate.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517, restricted to a fixed
positive lower bound for the gap. -/
theorem exists_aklv_fixed_gap_physical_sequential_mps_approximation :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ (g₀ : ℝ), 0 < g₀ → g₀ ≤ 1 →
      ∀ (L q : ℕ)
        (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω →
      ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → g₀ ≤ g → mu + g ∈ spectrum ℝ (∑ j, h j) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let rho := epsilon ^ 2 / (16 * ((L : ℝ) + 1))
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let z := aklvAccuracyLog rho
      let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
      let D := aklvAccuracyRankBound q s0 g rho
      let C₀ := ((1 + 1 / Real.log 2) * (1 + Real.log (1 / g₀))) ^ 3
      Real.log (D : ℝ) ≤ 11 * C * C₀ * Real.log (q : ℝ) ^ 3 / g * z ∧
      aklvSpectralTruncation Ω D ≠ 0 ∧
      ‖aklvNormalizedSpectralTruncation Ω D‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ aklvNormalizedSpectralTruncation Ω D x) ∧
      ‖aklvNormalizedSpectralTruncation Ω D - Ω‖ ≤ epsilon := by
  obtain ⟨A, C, hA, hC, hsequential⟩ :=
    exists_aklv_sharp_physical_sequential_mps_approximation
  refine ⟨A, C, hA, hC, ?_⟩
  intro g₀ hg₀ hg₀one L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hg₀g hexcited
    epsilon hepsilon hepsilon1 rho u z s0 D C₀
  obtain ⟨_hfourth, hlog, _hexplicit, _htail, hnonzero, hnorm, hmps, herror⟩ :=
    hsequential L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited
      epsilon hepsilon hepsilon1
  obtain ⟨_hL, hq, hg1⟩ :=
    aklv_chain_dimension_and_gap_bounds h hsupp h0 h1 mu g Ω hΩ hground hgap hg hexcited
  have hcubic := aklv_cubic_cost_of_fixed_gap hg₀ hg₀one hg₀g hg hg1 q hq
  change u ^ 3 / g ≤ C₀ * Real.log (q : ℝ) ^ 3 / g at hcubic
  have hz : 0 ≤ z := by
    dsimp only [z]
    exact (aklvAccuracyLog_bounds (by dsimp only [rho]; positivity) (by
      dsimp only [rho]
      apply (div_le_iff₀ (by positivity : 0 < 16 * ((L : ℝ) + 1))).2
      have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      nlinarith)).1.trans' (by norm_num)
  have hcoef : 0 ≤ 11 * C := by positivity
  refine ⟨hlog.trans ?_, hnonzero, hnorm, hmps, herror⟩
  calc
    11 * C * (u ^ 3 / g) * z ≤ 11 * C * (C₀ * Real.log (q : ℝ) ^ 3 / g) * z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcubic hcoef) hz
    _ = 11 * C * C₀ * Real.log (q : ℝ) ^ 3 / g * z := by ring

end TNLean.MPS.AreaLaw
