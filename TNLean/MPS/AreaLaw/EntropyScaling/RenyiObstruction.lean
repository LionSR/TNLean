/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TNLean.MPS.AreaLaw.EntropyScaling.EfficientApproximation
import TNLean.MPS.AreaLaw.EntropyScaling.RenyiApproximationLowerBound

/-!
# Rényi entropy obstruction to efficient MPS approximation

Efficient approximation forces a uniform logarithmic bound on every fixed
Rényi entropy of order greater than one, on every choice of contiguous blocks.
No consistency between chain lengths or normalization of the approximating
vectors is assumed. Source: SWVC08, arXiv:0705.0292v2, lines 309–345.

**Local fix (finite-chain constants):** the finite estimates use the corrected
sign of the logarithmic error term and the two-boundary factor for interior
blocks, documented in `docs/paper-gaps/swvc08_renyi_bond_dimension_sign.tex`
and `docs/paper-gaps/swvc08_interior_block_bond_rank.tex`. These corrections
leave the qualitative obstruction unchanged.
-/

open scoped ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Efficient approximation forces a uniform logarithmic Rényi entropy bound
on any chosen contiguous blocks. Source: SWVC08, arXiv:0705.0292v2,
lines 309–345, using the corrected two-boundary finite-chain estimate. -/
theorem IsEfficientlyApproximableByMPS.exists_logarithmic_renyi_bound
    {q : ℕ} {lengths : Set ℕ}
    {ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)}
    (happrox : IsEfficientlyApproximableByMPS ψ) (hψ : ∀ N, ‖ψ N‖ = 1)
    {α : ℝ} (hα : 1 < α) (a b : lengths → ℕ) (hab : ∀ N, a N ≤ b N) :
    ∃ K : ℝ, ∃ m : ℕ, ∀ N : lengths,
      renyiEntropy (Entropy.regionState (n := fun _ : Fin N.val ↦ q)
        (leftBlock N.val (b N) \ leftBlock N.val (a N)) (ψ N))
        (Entropy.regionState_posSemidef _ _).isHermitian α ≤
        K + (m : ℝ) * Real.log ((N.val : ℝ) + 1) := by
  obtain ⟨C, hC, m, happrox⟩ := happrox (1 / 2) (by norm_num)
  refine ⟨2 * |Real.log C| - α / (α - 1) * Real.log (1 - 1 / 2), 2 * m, fun N ↦ ?_⟩
  obtain ⟨D, φ, hD, hφ, herror⟩ := happrox N
  have hbound := hφ.renyiEntropy_sdiff_leftBlock_add_log_error_le_two_log
    (hψ N) (hab N) hα (by norm_num) herror
  have hx : 0 < (N.val : ℝ) + 1 := by positivity
  have hlogD : Real.log D ≤ |Real.log C| + (m : ℝ) * Real.log ((N.val : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos D with rfl | hDpos
    · simp only [Nat.cast_zero, Real.log_zero]
      exact add_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by linarith [(show (0 : ℝ) ≤ N.val from Nat.cast_nonneg _)])))
    · have hlog := Real.log_le_log (Nat.cast_pos.mpr hDpos) hD
      rw [Real.log_mul hC.ne' (pow_pos hx m).ne', Real.log_pow] at hlog
      exact hlog.trans (add_le_add (le_abs_self _) le_rfl)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- A family with no uniform logarithmic Rényi bound on its selected blocks
cannot be efficiently approximated. Source: SWVC08, arXiv:0705.0292v2,
lines 309–345. -/
theorem not_isEfficientlyApproximableByMPS_of_superlogarithmic_renyi
    {q : ℕ} {lengths : Set ℕ}
    {ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)}
    (hψ : ∀ N, ‖ψ N‖ = 1) {α : ℝ} (hα : 1 < α)
    (a b : lengths → ℕ) (hab : ∀ N, a N ≤ b N)
    (hgrowth : ∀ K : ℝ, ∀ m : ℕ, ∃ N : lengths,
      K + (m : ℝ) * Real.log ((N.val : ℝ) + 1) <
        renyiEntropy (Entropy.regionState (n := fun _ : Fin N.val ↦ q)
          (leftBlock N.val (b N) \ leftBlock N.val (a N)) (ψ N))
          (Entropy.regionState_posSemidef _ _).isHermitian α) :
    ¬ IsEfficientlyApproximableByMPS ψ := by
  intro happrox
  obtain ⟨K, m, hbound⟩ := happrox.exists_logarithmic_renyi_bound hψ hα a b hab
  obtain ⟨N, hN⟩ := hgrowth K m
  exact (not_lt_of_ge (hbound N)) hN

open Filter Asymptotics in
private theorem eventually_logarithmic_lt_rpow (K m : ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, K + m * Real.log x < c * x ^ r := by
  have hconst : (fun _ : ℝ ↦ K) =o[atTop] (fun x : ℝ ↦ x ^ r) :=
    isLittleO_const_left.mpr (Or.inr
      (tendsto_abs_atTop_atTop.comp (tendsto_rpow_atTop hr)))
  have hf := hconst.add ((isLittleO_log_rpow_atTop hr).const_mul_left m)
  filter_upwards [hf.bound (show 0 < c / 2 by positivity), eventually_gt_atTop (0 : ℝ)]
    with x hb hx
  have hp : 0 < x ^ r := Real.rpow_pos_of_pos hx r
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at hb
  nlinarith [le_abs_self (K + m * Real.log x)]

/-- The power-law Rényi obstruction of SWVC08, arXiv:0705.0292v2, lines 309–315.
The selected blocks occupy a fixed positive fraction of the chain, and their
Rényi entropy has a positive power-law lower bound. Both bounds may have
finitely many exceptional chain lengths. -/
theorem not_isEfficientlyApproximableByMPS_of_renyi_power_growth
    {q : ℕ} {lengths : Set ℕ} (hlengths : lengths.Infinite)
    {ψ : ∀ N : lengths, EuclideanSpace ℂ (Fin N.val → Fin q)}
    (hψ : ∀ N, ‖ψ N‖ = 1) {α : ℝ} (hα : 1 < α)
    (a b : lengths → ℕ) (hab : ∀ N, a N ≤ b N)
    {c κ η : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hη : 0 < η) {N₀ : ℕ}
    (hlinear : ∀ N : lengths, N₀ ≤ N.val →
      η * (N.val : ℝ) ≤ ((leftBlock N.val (b N) \ leftBlock N.val (a N)).card : ℝ))
    (hentropy : ∀ N : lengths, N₀ ≤ N.val →
      c * ((leftBlock N.val (b N) \ leftBlock N.val (a N)).card : ℝ) ^ κ ≤
        renyiEntropy (Entropy.regionState (n := fun _ : Fin N.val ↦ q)
          (leftBlock N.val (b N) \ leftBlock N.val (a N)) (ψ N))
          (Entropy.regionState_posSemidef _ _).isHermitian α) :
    ¬ IsEfficientlyApproximableByMPS ψ := by
  apply not_isEfficientlyApproximableByMPS_of_superlogarithmic_renyi hψ hα a b hab
  intro K m
  have hc' : 0 < c * (η / 2) ^ κ :=
    mul_pos hc (Real.rpow_pos_of_pos (half_pos hη) κ)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    (eventually_logarithmic_lt_rpow K (m : ℝ) hc' hκ)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max x₀ 1)
  obtain ⟨n, hn, hnlarge⟩ := hlengths.exists_gt (max N₀ n₀)
  let N : lengths := ⟨n, hn⟩
  refine ⟨N, ?_⟩
  have hN₀ : N₀ ≤ N.val := by dsimp only [N]; omega
  have hnn₀ : (n₀ : ℝ) < (N.val : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right N₀ n₀) hnlarge)
  have hN₁ : (1 : ℝ) ≤ N.val := by linarith [le_max_right x₀ 1]
  have hxN : x₀ ≤ (N.val : ℝ) + 1 := by linarith [le_max_left x₀ 1]
  have hsize : (η / 2) * ((N.val : ℝ) + 1) ≤
      ((leftBlock N.val (b N) \ leftBlock N.val (a N)).card : ℝ) := by
    nlinarith [hlinear N hN₀, mul_nonneg hη.le (sub_nonneg.mpr hN₁)]
  have hpow := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hsize hκ.le) hc.le
  rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
  apply (hx₀ _ hxN).trans_le
  apply le_trans ?_ (hentropy N hN₀)
  simpa only [mul_assoc] using hpow

end TNLean.MPS.AreaLaw
