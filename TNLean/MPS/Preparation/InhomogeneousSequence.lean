/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PartialIsometryPreparation
import TNLean.MPS.Preparation.ShortChainPreparation

/-!
# Inhomogeneous preparation with finitely many short rings

A positive logarithmic lower bound on the block lengths makes every block at least `3D`
for all sufficiently large rings. Every exceptional ring is prepared exactly by the finite
unitary synthesis of `exists_isPreparedInDepth_of_norm_eq_one`; its depth is absorbed into
one constant independent of the ring and its tensors. A one-site state is already a product.

The approximation hypotheses are those of `VaryingBondChain.IsPairApproximable`, with no
injectivity assumption.

**Scope restriction (positive block growth):** the positive logarithmic lower bound is an
explicit extra hypothesis: an upper bound `q = O(log N)` alone does not imply growth.
The conclusion is depth `O(L_N)` and error at most `δ_N`. It does not assert an
accuracy-dependent depth `O(log(N/ε))` from
`δ_N → 0` without a uniform error rate. See
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Main results

* `exists_isPreparedInDepth_inhomogeneous_of_log_lower`: one uniform depth bound for every
  positive ring length, with exact preparation below a fixed threshold.
* `exists_isPreparedInDepth_inhomogeneous_sequence`: logarithmic-depth sequence preparation
  with errors tending to zero.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`, block-length elimination argument.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- A logarithmic lower bound with positive coefficient eventually exceeds the register
length `3D`. The threshold depends only on `D` and the coefficient, not on the block schedule. -/
theorem exists_threshold_three_mul_le_of_log (D : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N q : ℕ, N₀ ≤ N → c * Real.log N ≤ q → 3 * D ≤ q := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp ((3 * D : ℝ) / c))
  refine ⟨N₀, fun N q hN hq => ?_⟩
  have hN' : Real.exp ((3 * D : ℝ) / c) < N :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans hN'
  have hlog := (Real.le_log_iff_exp_le hNpos).2 hN'.le
  have hbound : (3 * D : ℝ) ≤ c * Real.log N := by
    have := (div_le_iff₀ hc).1 hlog
    nlinarith
  exact_mod_cast hbound.trans hq

/-- Every vector on one site is a product vector, so no gates are needed. -/
theorem isPreparedInDepth_zero_one_site {d : ℕ} (ψ : Cfg d 1 → ℂ) :
    IsPreparedInDepth 0 ψ := by
  refine ⟨1, ⟨[], rfl, rfl⟩, fun _ a => ψ (fun _ => a), funext fun s => ?_⟩
  rw [Matrix.one_mulVec, productVector, Fin.prod_univ_one]
  exact congrArg ψ (funext fun i => congrArg s (Subsingleton.elim _ _))

/-- **All positive ring lengths with logarithmically growing blocks.** There are a threshold
`N₀` and a depth constant `C`, depending only on `d`, `D` and `c > 0`, such that any ring
whose block lengths satisfy `c log N ≤ ℓ k ≤ L` and whose positive parts are approximable
by pairs with error `δ` admits a unit state of depth at most `C L` and error at most `δ`.
For `N < N₀` the prepared state is exactly the normalized target state.

The exceptional rings use bounded finite-dimensional unitary synthesis, not an assumption of
exact preparation. No blocked-tensor injectivity is required. This is the finite-exception
argument for the inhomogeneous paragraph of arXiv:2307.01696 under the positive lower-growth
hypothesis recorded in the module docstring. -/
theorem exists_isPreparedInDepth_inhomogeneous_of_log_lower (d D : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    ∃ C N₀ : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : VaryingBondChain d D N) (L : ℕ) (δ : ℝ),
      (∀ k, c * Real.log N ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsPairApproximable A hN δ →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ T ≤ C * L ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ δ ∧
        (N < N₀ → ψ = (‖state A‖ : ℂ)⁻¹ • state A) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_threshold_three_mul_le_of_log D hc
  obtain ⟨K, hK⟩ := exists_isPreparedInDepth_of_norm_eq_one hd N₀
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  refine ⟨max C K, N₀, fun ℓ N _ hN A L δ hlog hL hA => ?_⟩
  have hLpos : 0 < L := by
    by_contra h
    have hzero : ∀ k, ℓ k = 0 := fun k => Nat.eq_zero_of_le_zero (by have := hL k; omega)
    simp only [hzero, Finset.sum_const_zero] at hN
    exact NeZero.ne N hN.symm
  by_cases hshort : N < N₀
  · obtain ⟨hne, ω, hω, hδ⟩ := hA
    have hn : ‖state A‖ ≠ 0 := by
      rw [state_eq_chainState, norm_chainState_eq _ hN]
      exact norm_ne_zero_iff.mpr hne
    have hunit : ‖(‖state A‖ : ℂ)⁻¹ • state A‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ hn]
    have hδ0 : 0 ≤ δ := by
      have hu : ‖(‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ •
          chainPosState (zeroPad A) hN‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
      have hle := norm_inner_le_norm (𝕜 := ℂ) (pairFamilyVector (padPairs A ℓ ω))
        ((‖chainPosState (zeroPad A) hN‖ : ℂ)⁻¹ • chainPosState (zeroPad A) hN)
      rw [hu, norm_pairFamilyVector (sum_star_padPairs_mul_self A ℓ hω), mul_one] at hle
      linarith
    have herr : 1 - ‖⟪(‖state A‖ : ℂ)⁻¹ • state A,
        (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ δ := by
      rw [inner_self_eq_norm_sq_to_K, hunit]
      simpa using hδ0
    by_cases hN1 : N = 1
    · subst hN1
      refine ⟨_, 0, hunit, Nat.zero_le _, ?_, herr, fun _ => rfl⟩
      exact isPreparedInDepth_zero_one_site (d := d)
        (fun s => ((‖state A‖ : ℂ)⁻¹ • state A) s)
    · refine ⟨_, K, hunit, ?_, hK N (by have := NeZero.ne N; omega) hshort.le _ hunit,
        herr, fun _ => rfl⟩
      exact (le_max_right C K).trans (Nat.le_mul_of_pos_right _ hLpos)
  · obtain ⟨ψ, hψ, hprep, herr⟩ := hC ℓ hN A L δ
      (fun k => hN₀ N (ℓ k) (by omega) (hlog k)) hL hA
    exact ⟨ψ, C * L, hψ, Nat.mul_le_mul_right L (le_max_left C K), hprep, herr,
      fun h => (hshort h).elim⟩

/-- **Vanishing error for an inhomogeneous sequence, including every short ring.**
For rings of `n + 1` sites whose block lengths have a positive logarithmic lower bound,
pair approximation with errors `δ n → 0` gives prepared unit states with errors tending to
zero and depths at most `C * L n`, for one constant `C`. Below one fixed threshold the states
are prepared exactly. A logarithmic upper bound on `L` gives logarithmic preparation depth,
without discarding finitely many members of the sequence.

The error rate is left as supplied by the sequence; no uniform exponential rate in the block
length is inferred from convergence alone. -/
theorem exists_isPreparedInDepth_inhomogeneous_sequence (d D : ℕ) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) (M L : ℕ → ℕ) [∀ n, NeZero (M n)]
    (ℓ : ∀ n, Fin (M n) → ℕ) (hN : ∀ n, ∑ k, ℓ n k = n + 1)
    (A : ∀ n, VaryingBondChain d D (n + 1)) (δ : ℕ → ℝ)
    (hlower : ∀ n k, c * Real.log (n + 1 : ℕ) ≤ ℓ n k)
    (hupper : ∀ n k, ℓ n k ≤ L n)
    (happrox : ∀ n, IsPairApproximable (A n) (hN n) (δ n))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hL : Asymptotics.IsBigO Filter.atTop (fun n => (L n : ℝ))
      (fun n => Real.log (n + 1 : ℕ))) :
    ∃ (C N₀ : ℕ) (ψ : ∀ n, MPVSpace d (n + 1)) (T : ℕ → ℕ),
      (∀ n, ‖ψ n‖ = 1 ∧ T n ≤ C * L n ∧
        IsPreparedInDepth (T n) (fun s => ψ n s) ∧
        1 - ‖⟪ψ n, (‖state (A n)‖ : ℂ)⁻¹ • state (A n)⟫_ℂ‖ ≤ δ n ∧
        (n + 1 < N₀ → ψ n = (‖state (A n)‖ : ℂ)⁻¹ • state (A n))) ∧
      Filter.Tendsto
        (fun n => 1 - ‖⟪ψ n, (‖state (A n)‖ : ℂ)⁻¹ • state (A n)⟫_ℂ‖)
        Filter.atTop (nhds 0) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
        (fun n => Real.log (n + 1 : ℕ)) := by
  classical
  obtain ⟨C, N₀, hC⟩ := exists_isPreparedInDepth_inhomogeneous_of_log_lower d D hd hc
  choose ψ T hψ using fun n =>
    hC (ℓ n) (hN n) (A n) (L n) (δ n) (hlower n) (hupper n) (happrox n)
  have hdepth : Asymptotics.IsBigO Filter.atTop (fun n => (T n : ℝ))
      (fun n => (L n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
    simp only [Real.norm_natCast]
    exact_mod_cast (hψ n).2.1
  refine ⟨C, N₀, ψ, T, hψ, ?_, hdepth.trans hL⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hψ n).2.2.2.1) hδ
  have hn : ‖state (A n)‖ ≠ 0 := by
    rw [state_eq_chainState, norm_chainState_eq _ (hN n)]
    exact norm_ne_zero_iff.mpr (happrox n).1
  have hu : ‖(‖state (A n)‖ : ℂ)⁻¹ • state (A n)‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hn]
  have hle := norm_inner_le_norm (𝕜 := ℂ) (ψ n)
    ((‖state (A n)‖ : ℂ)⁻¹ • state (A n))
  rw [(hψ n).1, hu, mul_one] at hle
  exact sub_nonneg.mpr hle

end MPSPreparation
