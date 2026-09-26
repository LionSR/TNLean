/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap

/-!
# Periodic gaps from open intervals of divisible length

A uniform positive open-chain gap along the lengths \(pM\), for fixed
\(p > 0\), implies a uniform positive periodic gap at every sufficiently large
length. Choose a divisible open interval containing \(m\) local terms with
\(m\gamma > (R-1)^2\), then apply the finite-range Knabe comparison.

This is the transfer needed after Nachtergaele's open-chain estimate,
arXiv:cond-mat/9410110, Theorem 2.1(ii). The finite-range coefficient is the
TNLean derivation in `docs/paper-gaps/knabe88_finite_range_coefficient.tex`.
-/

open Filter
open scoped Topology

namespace MPSTensor

variable {d D : ℕ}

/-- A positive open-chain gap on all sufficiently large multiples of a fixed
positive integer implies a positive periodic gap at every sufficiently large
length. This applies to the divisible open lengths in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), using the finite-range comparison in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_parentHamiltonianES_gap_of_eventually_divisible_openParentHamiltonianES_gap
    (A : MPSTensor d D) {p R : ℕ} (hp : 1 ≤ p) (hR : 1 ≤ R)
    {γ : ℝ} (hγ : 0 < γ)
    (hOpen : ∀ᶠ M : ℕ in atTop, ∀ u ∈
      (LinearMap.ker (openParentHamiltonianES A R (p * M)))ᗮ,
      γ * ‖u‖ ≤ ‖openParentHamiltonianES A R (p * M) u‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ v ∈
      (LinearMap.ker (parentHamiltonianES A R N))ᗮ,
      δ * ‖v‖ ≤ ‖parentHamiltonianES A R N v‖ := by
  obtain ⟨n, hn⟩ := exists_lt_nsmul hγ (((R : ℝ) - 1) ^ 2)
  obtain ⟨M, hM, hGap⟩ := ((eventually_ge_atTop (n + 2 * R)).and hOpen).exists
  have hMp : M ≤ p * M := by nlinarith
  let m := p * M - R + 1
  have hm : R ≤ m ∧ n ≤ m ∧ m + R - 1 = p * M := by omega
  have hnum : ((R : ℝ) - 1) ^ 2 < (m : ℝ) * γ := by
    exact hn.trans_le (by simpa only [nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm.2.1) hγ.le)
  obtain ⟨hδ, hPeriodic⟩ := parentHamiltonianES_gap_of_openParentHamiltonianES_gap
    A hR hm.1 hnum (hm.2.2.symm ▸ hGap)
  exact ⟨_, hδ, (eventually_ge_atTop (2 * m)).mono hPeriodic⟩

end MPSTensor
