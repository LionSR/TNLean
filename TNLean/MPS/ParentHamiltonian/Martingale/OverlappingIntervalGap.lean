/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Martingale.PositiveComparisonGap
import TNLean.MPS.ParentHamiltonian.Martingale.TwoGroundProjectionGap

/-!
# Combining gaps on overlapping open intervals

A long prefix and a terminal interval cover an open chain. A bound on the
product of their ground projections, after subtracting the full-chain ground
projection, combines their spectral gaps. This permits an interval of arbitrary
length to be treated using a prefix whose length is divisible by a chosen
grouping length.

The ground-projection estimate is the three-interval estimate of Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma `commutation` (ii). The sharp
two-projection comparison supplies the step from divisible lengths to
arbitrary lengths.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A prefix contains only interaction terms of the full open chain. -/
theorem openPrefixParentHamiltonianES_le_openParentHamiltonianES
    (A : MPSTensor d D) (R N n : ℕ) :
    openPrefixParentHamiltonianES A R N n ≤ openParentHamiltonianES A R N := by
  classical
  rw [openPrefixParentHamiltonianES, openParentHamiltonianES]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun i : NonwrappingStart R N => i.1.val + R ≤ n)
    (fun _ => by simp) (fun i => localTermES A R i.1)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A R i.1))

/-- An interval Hamiltonian contains only interaction terms of the full open chain. -/
theorem openSuffixParentHamiltonianES_le_openParentHamiltonianES
    (A : MPSTensor d D) (R W N n : ℕ) :
    openSuffixParentHamiltonianES A R W N n ≤ openParentHamiltonianES A R N := by
  classical
  rw [openSuffixParentHamiltonianES, openParentHamiltonianES]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A R i.1))

/-- Gaps for a prefix and a terminal interval give a full-chain gap if the
product of their ground projections differs from the full-chain ground
projection by at most \(1/2\). The two interval energies sum to at most twice
the full-chain energy, so a common interval gap \(\kappa\) gives a gap
\(\kappa/16\). This is an auxiliary two-interval consequence of the projector
estimate in Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma `commutation` (ii). -/
theorem openParentHamiltonianES_norm_gap_of_overlapping_interval_gaps
    (A : MPSTensor d D) (R N n W : ℕ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLeft : ∀ v ∈ (LinearMap.ker (openPrefixParentHamiltonianES A R N n))ᗮ,
      κ * ‖v‖ ≤ ‖openPrefixParentHamiltonianES A R N n v‖)
    (hRight : ∀ v ∈ (LinearMap.ker (openSuffixParentHamiltonianES A R W N N))ᗮ,
      κ * ‖v‖ ≤ ‖openSuffixParentHamiltonianES A R W N N v‖)
    (hDefect : ‖(LinearMap.ker (openParentHamiltonianES A R N)).starProjection -
      (LinearMap.ker (openPrefixParentHamiltonianES A R N n)).starProjection.comp
        (LinearMap.ker (openSuffixParentHamiltonianES A R W N N)).starProjection‖ ≤
      (1 / 2 : ℝ)) :
    ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      (κ / 16) * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  have hWU := (openPrefixParentHamiltonianES_isPositive A R N n).ker_le_of_le
    (openPrefixParentHamiltonianES_le_openParentHamiltonianES A R N n)
  have hWV := (openSuffixParentHamiltonianES_isPositive A R W N N).ker_le_of_le
    (openSuffixParentHamiltonianES_le_openParentHamiltonianES A R W N N)
  have hCover : openPrefixParentHamiltonianES A R N n +
      openSuffixParentHamiltonianES A R W N N ≤ (2 : ℂ) • openParentHamiltonianES A R N := by
    simpa only [two_smul] using add_le_add
      (openPrefixParentHamiltonianES_le_openParentHamiltonianES A R N n)
      (openSuffixParentHamiltonianES_le_openParentHamiltonianES A R W N N)
  have hTwice := smul_le_smul_of_nonneg_left ((add_le_add
      (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap
        (openPrefixParentHamiltonianES_isPositive A R N n) hκ hLeft)
      (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap
        (openSuffixParentHamiltonianES_isPositive A R W N N) hκ hRight)).trans hCover)
    (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hLower : ((κ / 2 : ℝ) : ℂ) •
      ((LinearMap.ker (openPrefixParentHamiltonianES A R N n))ᗮ.starProjection.toLinearMap +
        (LinearMap.ker (openSuffixParentHamiltonianES A R W N N))ᗮ.starProjection.toLinearMap) ≤
      openParentHamiltonianES A R N := by
    convert hTwice using 1
    · rw [smul_add, smul_add, smul_smul, smul_smul]
      norm_num [div_eq_mul_inv, mul_comm]
    · rw [smul_smul]
      norm_num
  intro v hv
  refine le_trans ?_ (FrustrationFree.norm_gap_of_two_ground_projection_bounds _ _ _
    (by positivity) (by norm_num : (1 / 2 : ℝ) < 1) hWU hWV hLower hDefect v hv)
  gcongr
  linarith

end MPSTensor
