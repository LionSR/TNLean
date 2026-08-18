/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitModulusPowerSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Cesàro means over `1 ≤ n ≤ N` and orthogonality of unit-modulus phases

Let $s$ be a finite set of complex numbers of modulus one and let
$\lambda \in s$. The averages
$$
  \frac{1}{N}\sum_{n=1}^{N}\sum_{\mu \in s} (\bar\mu\lambda)^n
$$
converge to $1$. Each ratio $\bar\mu\lambda$ again has modulus one, and it
equals $1$ exactly when $\mu = \lambda$; the diagonal term contributes $1$ at
every $N$, while for $\mu \neq \lambda$ the geometric sum
$\sum_{n=1}^{N}\zeta^n = (\zeta - \zeta^{N+1})/(1-\zeta)$ stays bounded and its
average vanishes.

Alongside this scalar identity the file records the vector Cesàro statement in
the same range of summation: averages over $1 \le n \le N$ of a sequence
tending to zero tend to zero.

## Main statements

* `WeightedCesaro.tendsto_cesaro_zero`: Cesàro means over $1 \le n \le N$ of a
  null sequence in a complex normed space vanish.
* `WeightedCesaro.tendsto_cesaro_geom_zero`: the Cesàro mean of the powers of a
  unit-modulus number other than $1$ vanishes.
* `WeightedCesaro.tendsto_cesaro_phase_sum`: the orthogonality relation
  $\frac{1}{N}\sum_{n=1}^{N}\sum_{\mu \in s}(\bar\mu\lambda)^n \to 1$.

## Tags

Cesàro mean, geometric series, unit modulus, phase
-/

open Filter
open scoped Topology

namespace WeightedCesaro

/-- Reindexing a sum over `1 ≤ n ≤ N` as a sum over `0 ≤ i < N`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (u : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, u n = ∑ i ∈ Finset.range N, u (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)),
        Finset.sum_range_succ, ih]

/-- Cesàro means over `1 ≤ n ≤ N` of a sequence tending to zero tend to zero. -/
theorem tendsto_cesaro_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : ℕ → E} (h : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N, u n) atTop (𝓝 0) := by
  have hshift : Tendsto (fun i : ℕ ↦ u (i + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1)
  refine hshift.cesaro_smul.congr fun N ↦ ?_
  rw [sum_Icc_one_eq_sum_range, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num

/-- The Cesàro mean over `1 ≤ n ≤ N` of the powers of a unit-modulus number
other than `1` vanishes. -/
theorem tendsto_cesaro_geom_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ 1) :
    Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ζ ^ n) atTop (𝓝 0) := by
  have h := (UnitModulusPowerSum.cesaro_geom_sum_tendsto_zero hζ hne).const_mul ζ
  rw [mul_zero] at h
  refine h.congr fun N ↦ ?_
  rw [sum_Icc_one_eq_sum_range]
  simp only [pow_succ']
  rw [← Finset.mul_sum]
  ring

/-- The Cesàro mean over `1 ≤ n ≤ N` of the powers of `1` equals `1`. -/
theorem tendsto_cesaro_geom_one :
    Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, (1 : ℂ) ^ n) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun N hN ↦ ?_)
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN)
  simp only [one_pow, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_one]
  exact (inv_mul_cancel₀ hNne).symm

/-- **Orthogonality of unit-modulus phases.**  For a finite set `s` of complex
numbers of modulus one and `lam ∈ s`, the averages
`(1/N) ∑_{n=1}^{N} ∑_{μ ∈ s} (conj μ * lam) ^ n` converge to `1`: the term
`μ = lam` contributes `1` at every `N`, and every other term is a bounded
geometric sum divided by `N`. -/
theorem tendsto_cesaro_phase_sum {s : Finset ℂ} (hs : ∀ μ ∈ s, ‖μ‖ = 1) {lam : ℂ}
    (hlam : lam ∈ s) :
    Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
        ∑ n ∈ Finset.Icc 1 N, ∑ μ ∈ s, ((starRingEnd ℂ) μ * lam) ^ n) atTop (𝓝 1) := by
  classical
  have hlam1 : ‖lam‖ = 1 := hs lam hlam
  have hterm : ∀ μ ∈ s, Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
      ∑ n ∈ Finset.Icc 1 N, ((starRingEnd ℂ) μ * lam) ^ n) atTop
      (𝓝 (if μ = lam then 1 else 0)) := by
    intro μ hμ
    by_cases hμlam : μ = lam
    · subst hμlam
      rw [ite_eq_left rfl]
      have hone : (starRingEnd ℂ) μ * μ = 1 := by
        rw [Complex.conj_mul', hs μ hμ]
        norm_num
      simp only [hone]
      exact tendsto_cesaro_geom_one
    · rw [ite_eq_right hμlam]
      refine tendsto_cesaro_geom_zero ?_ ?_
      · rw [norm_mul, RCLike.norm_conj, hs μ hμ, hlam1, one_mul]
      · intro hζ
        apply hμlam
        have hmul : μ * ((starRingEnd ℂ) μ * lam) = μ * 1 := by rw [hζ]
        rw [← mul_assoc, Complex.mul_conj', hs μ hμ] at hmul
        simpa using hmul.symm
  have hsum := tendsto_finsetSum s hterm
  rw [Finset.sum_ite_eq' s lam (fun _ : ℂ ↦ (1 : ℂ)), ite_eq_left hlam] at hsum
  refine hsum.congr fun N ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_comm]

end WeightedCesaro
