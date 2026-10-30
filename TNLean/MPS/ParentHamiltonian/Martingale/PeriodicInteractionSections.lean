/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteractionRangeComparison
import QICLean.Analysis.WeightedPositiveKernel

/-!
# The local sections of a periodic interaction kernel

A translated interaction acts on each fixed-outside coefficient section by the
original local operator. For a positive interaction, a periodic Hamiltonian
kernel equation therefore supplies every local section equation.

Source: the local-kernel step in SPWC10, arXiv:0909.5347, Theorem 5 proof,
lines 869--880 of `Papers/0909.5347/main.tex`.
-/

namespace MPSTensor

variable {d R N : ℕ}

/-- Restricting a translated interaction to its own window gives the local
operator applied to that same section. Source: SPWC10, Theorem 5 proof,
lines 869--880. -/
theorem cyclicRestrictES_periodicLocalInteractionES
    (h : MPVSpace d R →ₗ[ℂ] MPVSpace d R) (hR : 0 < R) (hRN : R ≤ N)
    (i : Fin N) (τ : Cfg d N) (ψ : MPVSpace d N) :
    cyclicRestrictES (Fin.pos i) R i τ (periodicLocalInteractionES h i ψ) =
      h (cyclicRestrictES (Fin.pos i) R i τ ψ) := by
  ext ω
  change periodicLocalInteractionES h i ψ (cyclicCfg (Fin.pos i) R i ω τ) = _
  rw [periodicLocalInteractionES_apply h hR hRN]
  have hrestrict : cyclicRestrictES (Fin.pos i) R i
      (cyclicCfg (Fin.pos i) R i ω τ) ψ = cyclicRestrictES (Fin.pos i) R i τ ψ := by
    ext ν
    exact congrFun (cyclicRestrictₗ_cyclicCfg_outside (Fin.pos i) i ω τ ψ.ofLp) ν
  have hextract : extractWindow R i (cyclicCfg (Fin.pos i) R i ω τ) = ω :=
    extractWindow_replaceWindow R hRN i τ ω
  rw [hrestrict, hextract]

/-- A translated local interaction vanishes precisely when it kills every
actual coefficient section on its window. Source: SPWC10, Theorem 5 proof,
lines 869--880. -/
theorem periodicLocalInteractionES_eq_zero_iff_sections
    (h : MPVSpace d R →ₗ[ℂ] MPVSpace d R) (hR : 0 < R) (hRN : R ≤ N)
    (i : Fin N) (ψ : MPVSpace d N) :
    periodicLocalInteractionES h i ψ = 0 ↔
      ∀ τ : Cfg d N, h (cyclicRestrictES (Fin.pos i) R i τ ψ) = 0 := by
  constructor
  · intro hzero τ
    rw [← cyclicRestrictES_periodicLocalInteractionES h hR hRN i τ ψ, hzero, map_zero]
  · intro hzero
    ext σ
    rw [periodicLocalInteractionES_apply h hR hRN]
    exact congrArg (fun v : MPVSpace d R ↦ v (extractWindow R i σ)) (hzero σ)

/-- Positivity derives every local section equation from the actual periodic
Hamiltonian kernel. Source: SPWC10, Theorem 5 proof, lines 869--880. -/
theorem periodicInteractionHamiltonianES_eq_zero_iff_sections
    (h : MPVSpace d R →ₗ[ℂ] MPVSpace d R) (hh : h.IsPositive)
    (hR : 0 < R) (hRN : R ≤ N) (ψ : MPVSpace d N) :
    periodicInteractionHamiltonianES h N ψ = 0 ↔
      ∀ (i : Fin N) (τ : Cfg d N), h (cyclicRestrictES (Fin.pos i) R i τ ψ) = 0 := by
  rw [periodicInteractionHamiltonianES, WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun i : Fin N ↦ periodicLocalInteractionES_isPositive hh i) ψ]
  exact forall_congr' fun i ↦ periodicLocalInteractionES_eq_zero_iff_sections h hR hRN i ψ

/-- A zero local term inside a larger active interval kills every actual
spectator section by the corresponding term on that interval. The interaction
range stays fixed. Source: finite-range identity extension in Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem periodicLocalInteractionES_rightFiber_eq_zero_of_eq_zero
    {W : ℕ} (h : MPVSpace d R →ₗ[ℂ] MPVSpace d R) (hR : 0 < R)
    (hWN : W ≤ N) (s : Fin N) (q : Fin W) (hqR : q.val + R ≤ W)
    (ψ : MPVSpace d N)
    (hzero : periodicLocalInteractionES h (cyclicForwardSite s q.val) ψ = 0)
    (τ : Cfg d (N - W)) :
    periodicLocalInteractionES h q
      (ContinuousLinearMap.rightFiber
        (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s ψ) τ) = 0 := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s
  have heq := LinearMap.congr_fun
    (periodicLocalInteractionES_conj_cyclicActiveBlock h hR hWN s q hqR) (U ψ)
  change U (periodicLocalInteractionES h (cyclicForwardSite s q.val)
      (U.symm (U ψ))) = _ at heq
  rw [U.symm_apply_apply, hzero, map_zero] at heq
  apply PiLp.ext
  intro σ
  have hσ := congrArg (fun v ↦ v (σ, τ)) heq
  change 0 = periodicLocalInteractionES h q (ContinuousLinearMap.rightFiber (U ψ) τ) σ at hσ
  exact hσ.symm

end MPSTensor
