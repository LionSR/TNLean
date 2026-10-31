/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.AccuracyWindow
import TNLean.MPS.AreaLaw.AKLV.OptimizedRankBound

/-!
# Sharp physical per-cut approximation from AKLV windows

The universal rank coefficient is chosen before all physical data. The
actual original interaction derives the nontrivial local dimension and
the upper gap bound independently of a fitting window. Actual filtered
images or the exact boundary vector attain the fourth-root logarithmic
rank budget at every cut.

Source: AKLV, arXiv:1301.1162v1, lines 1503--1517. The actual first excited
energy remains part of the original physical data. No window, filter,
rank comparison or upper-gap hypothesis is supplied to the conclusion.

**Scope restriction (actual first excited energy):** The positive projector
lower bound is also required to be an actual first excitation. The theorem
is not asserted for an arbitrary lower bound without choosing an actual
gap. The local support and normalization conventions are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- Two distinct spectral values force a nontrivial local dimension, and
positive-contraction endpoint perturbations bound the actual unique-ground
gap by one. The conclusion is independent of a fitting physical window. -/
theorem aklv_chain_dimension_and_gap_bounds {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h j) (interval L j.val (j.val + 2)))
    (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (mu g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (hground : (∑ j, h j) *ᵥ WithLp.ofLp Ω = (mu : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ j, h j) - (mu : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : mu + g ∈ spectrum ℝ (∑ j, h j)) :
    0 < L ∧ 2 ≤ q ∧ g ≤ 1 := by
  classical
  have hH : (∑ j, h j).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun j _ ↦ h0 j)).isHermitian
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq : 2 ≤ q := hH.two_le_local_dimension_of_two_spectral_values
    hmu hexcited (by linarith)
  have hL : 0 < L := by
    by_contra hnot
    have hL0 : L = 0 := by omega
    have hcfg : Subsingleton (Fin L → Fin q) := by subst L; infer_instance
    let := hcfg
    obtain ⟨i, hi⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
    obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hexcited
    have heq : mu = mu + g := hi.symm.trans
      ((congrArg hH.eigenvalues (Subsingleton.elim i j)).trans hj)
    linarith
  have hgs : IsGappedGroundState (∑ j, h j) mu Ω g :=
    isGappedGroundState_iff.mpr ⟨hΩ, hground, hgap⟩
  exact ⟨hL, hq, gap_le_one_of_positive_nearest_neighbor_terms hL hq h hsupp h0 h1 hgs⟩

/-- The actual same-cut physical approximants obey the sharp fourth-root
logarithmic rank bound, uniformly over cuts and chain lengths. Both the
filtered and exact boundary alternatives are retained. -/
theorem exists_aklv_sharp_physical_per_cut_approximation :
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
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      let u := 1 + Real.log (q : ℝ) + Real.log (1 / g)
      let z := aklvAccuracyLog rho
      let s0 : ℕ := ⌈A * u ^ 2 / g⌉₊
      2 ≤ q ∧ g ≤ 1 ∧
      Real.log (aklvAccuracyRankBound q s0 g rho : ℝ) ≤
        C * (u ^ 3 / g + Real.sqrt (Real.sqrt (z ^ 3 / g)) * (u + Real.log (z + 1))) ∧
      ∀ k : ℕ, k ≤ L → ∃ y : EuclideanSpace ℂ (Fin L → Fin q),
        ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ rho ∧
        (cutMatrix y k).rank ≤ aklvAccuracyRankBound q s0 g rho ∧
        (y = Ω ∨ IsAKLVAccuracyFilteredOutput k s0 h g rho Ω y) := by
  obtain ⟨A, hA, _hA21, haccuracy⟩ := exists_aklv_physical_accuracy_window
  have hC : 0 < aklvAccuracyLogCoefficient A := by
    have hlog : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
    unfold aklvAccuracyLogCoefficient aklvInitialRankLogCoefficient
    positivity
  refine ⟨A, aklvAccuracyLogCoefficient A, hA, hC, ?_⟩
  intro L q h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited rho hrho hrho1 u z s0
  obtain ⟨_hL, hq, hg1⟩ :=
    aklv_chain_dimension_and_gap_bounds h hsupp h0 h1 mu g Ω hΩ hground hgap hg hexcited
  refine ⟨hq, hg1, aklvAccuracyRankBound_log_le_fourthRoot hA hg hg1 hrho hrho1 q hq, ?_⟩
  intro k hk
  exact haccuracy L q k hq hk h mu g Ω hsupp h0 h1 hΩ hground hgap hg hexcited rho hrho hrho1

end TNLean.MPS.AreaLaw
