/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleVariationalEigenvalue

/-!
# The asymptotic finite variational step for the uncle Hamiltonian

A quadratic lower bound for an actual trial's squared norm, a vanishing
actual kernel projection and a linear energy upper bound give arbitrarily
small positive eigenvalues on the chains of length 6N+1. This is the purely
analytic step after the source tensor and genericity estimates; those
estimates remain explicit inputs here.

Source: arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
-/

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace MPSTensor

/-- The actual uncle Hamiltonians have eventually a positive eigenvalue
below every positive threshold when the actual trial family has quadratic
squared norm, vanishing kernel projection and linear energy. The kernel
complement vector is derived by subtracting its actual orthogonal projection.
This is the analytic step of arXiv:1210.6613, proof of thm:gapless,
lines 1302–1314; no source tensor estimate is asserted by this lemma alone. -/
theorem eventually_exists_pos_eigenvalue_uncleHamiltonianES_lt_of_trial_bounds
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : (N : ℕ) → EuclideanSpace ℂ (Cfg d (6 * N + 1)))
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ᶠ N : ℕ in atTop, c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ‖v N‖ ^ 2)
    (hProj : Tendsto (fun N : ℕ ↦
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2) atTop (𝓝 0))
    (hEnergy : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (⟪uncleHamiltonianES A B R L (6 * N + 1) (v N), v N⟫_ℂ).re ≤ C * N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
        Module.End.HasEigenvalue
          (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap (μ : ℂ) := by
  obtain ⟨C, hC, hEnergy⟩ := hEnergy
  intro ε hε
  let k : ℝ := ε * c / 2
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (C / k)
  have hMpos : 0 < M := Nat.cast_pos.mp ((div_pos hC hk).trans hM)
  have hProjSmall : ∀ᶠ N : ℕ in atTop,
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2 < c / 2 :=
    hProj.eventually (eventually_lt_nhds (half_pos hc))
  filter_upwards [hNorm, hEnergy, hProjSmall, eventually_ge_atTop M]
    with N hNormN hEnergyN hProjN hMN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (hMpos.trans_le hMN)
  have hNormN' : c * ((N : ℝ) + 1) ^ 2 ≤ ‖v N‖ ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNormN
  have hMass : (c / 2) * (N : ℝ) ^ 2 ≤ ‖v N‖ ^ 2 -
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2 := by
    have hlinear : 0 ≤ c * (N : ℝ) := mul_nonneg hc.le hNpos.le
    have hquadratic : 0 ≤ c * (N : ℝ) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    nlinarith only [hNormN', hProjN.le, hc, hlinear, hquadratic]
  have hLarge : C < k * (N : ℝ) := by
    have hdiv : C / k < (N : ℝ) := hM.trans_le (Nat.cast_le.mpr hMN)
    simpa only [mul_comm] using (div_lt_iff₀ hk).mp hdiv
  have hRayleigh : C * (N : ℝ) < ε * ((c / 2) * (N : ℝ) ^ 2) := by
    calc
      C * (N : ℝ) < (k * (N : ℝ)) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hLarge hNpos
      _ = _ := by dsimp [k]; ring
  apply exists_pos_eigenvalue_uncleHamiltonianES_lt_of_projection_bound
    A B R L (6 * N + 1) (v N) ε
  exact hEnergyN.trans_lt
    (hRayleigh.trans_le (mul_le_mul_of_nonneg_left hMass hε.le))

end MPSTensor
