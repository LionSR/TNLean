/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.FixedAmbient
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.Martingale.TwoGroundProjectionGap

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

/-- Gaps for a prefix and a terminal interval give a full-chain gap if the
product of their ground projections differs from the full-chain ground
projection by at most \(1/2\). The two interval energies sum to at most twice
the full-chain energy, so a common interval gap \(\kappa\) gives a gap
\(\kappa/16\); each gap says that every eigenvalue is `0` or at least the gap. This is an
auxiliary two-interval consequence of the projector estimate in Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma `commutation` (ii). -/
theorem hamiltonian_parentChainInteraction_gap_of_overlapping_interval_gaps
    (A : MPSTensor d D) (R N n W : ℕ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLeft : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R N).restrict fun i ↦ i.val + R ≤ n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ)
    (hRight : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R N).restrict
        fun i ↦ N - W ≤ i.val ∧ i.val + R ≤ N).hamiltonian) μ → μ = 0 ∨ (κ : ℂ) ≤ μ)
    (hDefect : ‖(LinearMap.ker
        (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian)).starProjection -
      (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A R N).restrict
        fun i ↦ i.val + R ≤ n).hamiltonian)).starProjection.comp
        (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A R N).restrict
          fun i ↦ N - W ≤ i.val ∧ i.val + R ≤ N).hamiltonian)).starProjection‖ ≤
      (1 / 2 : ℝ)) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian) μ →
        μ = 0 ∨ ((κ / 16 : ℝ) : ℂ) ≤ μ := by
  have hnn := fun i ↦ Matrix.nonneg_iff_posSemidef.mpr
    (posSemidef_parentChainInteraction_term A R N i)
  have hPL := Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_restrict_parentChainInteraction A R N fun i ↦ i.val + R ≤ n)
  have hPR := Matrix.isPositive_toEuclideanLin_iff.mpr
    (posSemidef_hamiltonian_restrict_parentChainInteraction A R N
      fun i ↦ N - W ≤ i.val ∧ i.val + R ≤ N)
  have hLL := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.hamiltonian_restrict_le hnn fun i ↦ i.val + R ≤ n)
  have hLR := Matrix.toEuclideanLin_le_toEuclideanLin_iff.mpr
    (ManyBody.Interaction.hamiltonian_restrict_le hnn fun i ↦ N - W ≤ i.val ∧ i.val + R ≤ N)
  have hWU := hPL.ker_le_of_le hLL
  have hWV := hPR.ker_le_of_le hLR
  have hTwice := smul_le_smul_of_nonneg_left ((add_le_add
      (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap hPL hκ
        ((ManyBody.forall_hasEigenvalue_iff_norm
          (posSemidef_hamiltonian_restrict_parentChainInteraction A R N _)).mp hLeft))
      (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap hPR hκ
        ((ManyBody.forall_hasEigenvalue_iff_norm
          (posSemidef_hamiltonian_restrict_parentChainInteraction A R N _)).mp hRight))).trans
      ((add_le_add hLL hLR).trans_eq (two_smul ℂ _).symm))
    (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hLower : ((κ / 2 : ℝ) : ℂ) •
      ((LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A R N).restrict
          fun i ↦ i.val + R ≤ n).hamiltonian))ᗮ.starProjection.toLinearMap +
        (LinearMap.ker (Matrix.toEuclideanLin ((parentChainInteraction A R N).restrict
          fun i ↦ N - W ≤ i.val ∧ i.val + R ≤ N).hamiltonian))ᗮ.starProjection.toLinearMap) ≤
      Matrix.toEuclideanLin (parentChainInteraction A R N).hamiltonian := by
    convert hTwice using 1
    · rw [smul_add, smul_add, smul_smul, smul_smul]
      norm_num [div_eq_mul_inv, mul_comm]
    · rw [smul_smul]
      norm_num
  exact ManyBody.forall_hasEigenvalue_mono (by linarith)
    (FrustrationFree.forall_hasEigenvalue_of_two_ground_projection_bounds _ _ _
      (by positivity) (by norm_num : (1 / 2 : ℝ) < 1) hWU hWV hLower hDefect)

end MPSTensor
