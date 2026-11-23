/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.OpenRangeComparison
import QICLean.Spectral.Gap.EuclideanFiberwiseGap

/-!
# Gaps of interval Hamiltonians after adjoining free sites

An interval Hamiltonian, acting on a larger chain, is an orthogonal direct
sum of copies of its finite-interval operator. Its gap, the lower bound on its
nonzero eigenvalues, is therefore preserved. The proof transports the kernel
projection and its positive comparison under the physical coordinate
isometry. This supplies the fixed-ambient interpretation of the local gaps
in Nachtergaele, arXiv:cond-mat/9410110, condition C2, lines 1045--1056.
-/

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Adjoining free sites to a prefix preserves its finite-interval gap: every eigenvalue of the
prefix Hamiltonian on the longer chain is `0` or at least the gap. This is the fixed-ambient
interpretation of the local gap in Nachtergaele, arXiv:cond-mat/9410110, condition C2,
lines 1045--1056. -/
theorem hamiltonian_prefix_parentChainInteraction_gap_of_local_gap
    (A : MPSTensor d D) {R n q : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R (n + q)).restrict fun i ↦ i.val + R ≤ n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ := by
  have hConj :=
    hamiltonian_prefix_parentChainInteraction_conj_rightSpectatorConfigLinearIsometryEquiv
      A (L := R) (n := n) (r := q) (p := n) le_rfl
  exact ContinuousLinearMap.forall_hasEigenvalue_of_conj_rightFiberwiseMap
    (rightSpectatorConfigLinearIsometryEquiv d n q) _
    (Matrix.toEuclideanLin (parentChainInteraction A R n).hamiltonian) hκ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentChainInteraction A R n))
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc,
      hamiltonian_prefix_parentChainInteraction_self_eq_hamiltonian_parentChainInteraction] using!
        hConj)
    hGap

/-- Inserting a finite terminal-interval Hamiltonian into a larger chain preserves its gap:
every eigenvalue of the interval Hamiltonian on the larger chain is `0` or at least the gap.
The physical coordinate isometry places its active sites first and the free sites second. This
is the fixed-ambient form of Nachtergaele's condition C2, arXiv:cond-mat/9410110,
lines 1045--1056. -/
theorem hamiltonian_restrict_parentChainInteraction_gap_of_local_gap
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) {κ : ℝ} (hκ : 0 < κ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
      ((parentChainInteraction A R N).restrict
        fun i ↦ n - W ≤ i.val ∧ i.val + R ≤ n).hamiltonian) μ →
        μ = 0 ∨ (κ : ℂ) ≤ μ := by
  have hConj := hamiltonian_restrict_parentChainInteraction_conj_cyclicActiveBlock A hR hRW hWn hnN
  exact ContinuousLinearMap.forall_hasEigenvalue_of_conj_rightFiberwiseMap
    (cyclicActiveBlockConfigLinearIsometryEquiv d W (hWn.trans hnN) ⟨n - W, by omega⟩) _
    (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian) hκ
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentChainInteraction A R W))
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hConj)
    hGap

end MPSTensor
