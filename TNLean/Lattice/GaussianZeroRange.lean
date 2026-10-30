/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianFilteredTerm
import TNLean.Circuit.LocalCircuit
import TNLean.Algebra.ToEuclideanLinApply
import Mathlib.Topology.MetricSpace.Defs

/-!
# Exact Gaussian filtering for zero-range Hamiltonians

Let a finite metric space index both the sites and the terms of a local Hamiltonian.
If each term `Hᵢ` acts inside `Metric.closedBall i 0`, it acts only at site `i`.
The terms therefore commute pairwise, and filtering `Hᵢ` under the full Hamiltonian
or any partial sum returns `Hᵢ` exactly. Each term also preserves every eigenspace
of the full Hamiltonian, so its excited component on a ground vector vanishes.

This proves the zero-range case of Hastings, *Solving Gapped Hamiltonians Locally*,
arXiv:cond-mat/0508554v3, eqs. `mid`, `apb`, and `facld` (lines 285–348), directly,
without division by the interaction range. The filter is the normalized Gaussian
average of eq. `thd`; see `docs/paper-gaps/hastings05_truncated_dynamics.tex` for the
missing factor of `q` in the printed eq. `mid`. No positivity assumption on the
Gaussian parameter is needed for these identities, because the underlying
Heisenberg evolution is constant.

The metric assumption is essential to the reduction to singleton supports:
in a pseudometric space the radius-zero ball may contain distinct sites.
-/

open Matrix QuantumCircuit GaussianFilter
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

section Commuting

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A commuting observable is fixed by the normalized Gaussian filter, at every variance. -/
theorem gaussianFilteredTerm_eq_of_commute (q ΔE : ℝ) {H W : Matrix n n ℂ}
    (hc : Commute H W) : gaussianFilteredTerm q ΔE H W = W := by
  have hconst (t : ℝ) : hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) = W := by
    have hWt : Commute W (hermitianUnitaryPath H t) := by
      unfold hermitianUnitaryPath
      exact Commute.exp_right ((hc.symm.smul_right Complex.I).smul_right t)
    rw [← hWt.eq, Matrix.mul_assoc, SpectralFilter.hermitianUnitaryPath_mul_neg, Matrix.mul_one]
  simp [gaussianFilteredTerm, gaussianIntertwiner, hconst]

/-- A commuting observable preserves every ground eigenspace. -/
theorem mem_groundEigenspace_apply_of_commute {H W : Matrix n n ℂ} (hc : Commute H W)
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀) :
    toEuclideanLin W ψ ∈ groundEigenspace H E₀ := by
  have hψ' := Module.End.mem_eigenspace_iff.mp hψ
  apply Module.End.mem_eigenspace_iff.mpr
  rw [← toEuclideanLin_mul_apply, hc.eq, toEuclideanLin_mul_apply, hψ', map_smul]

/-- A commuting observable has no component outside the ground eigenspace on a ground vector. -/
theorem starProjection_apply_eq_of_commute {H W : Matrix n n ℂ} (hc : Commute H W)
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundEigenspace H E₀) :
    (groundEigenspace H E₀).starProjection (toEuclideanLin W ψ) = toEuclideanLin W ψ :=
  (groundEigenspace H E₀).starProjection_eq_self_iff.mpr
    (mem_groundEigenspace_apply_of_commute hc hψ)

end Commuting

section SingleSites

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- Terms supported on their individual sites commute pairwise. -/
theorem commute_of_singleton_support
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d ({i} : Set ι)) (i j : ι) :
    Commute (h i) (h j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply commute_of_mem_supportedOperators _ (hsupp i) (hsupp j)
    apply Set.disjoint_left.mpr
    intro k hki hkj
    simp only [Set.mem_singleton_iff] at hki hkj
    exact hij (hki.symm.trans hkj)

/-- Any partial sum of zero-range terms commutes with each individual term, even when the
partial sum omits its index. -/
theorem commute_sum_of_singleton_support
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d ({i} : Set ι)) (s : Finset ι) (i : ι) :
    Commute (∑ j ∈ s, h j) (h i) := by
  change (∑ j ∈ s, h j) * h i = h i * ∑ j ∈ s, h j
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (commute_of_singleton_support h hsupp j i).eq

/-- The local and full Gaussian filters are exact for physical zero-range terms. -/
theorem gaussianFilteredTerm_sum_eq_of_singleton_support
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d ({i} : Set ι))
    (s : Finset ι) (q ΔE : ℝ) (i : ι) :
    gaussianFilteredTerm q ΔE (∑ j ∈ s, h j) (h i) = h i :=
  gaussianFilteredTerm_eq_of_commute q ΔE (commute_sum_of_singleton_support h hsupp s i)

end SingleSites

section Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MetricSpace ι] {d : ℕ}

omit [DecidableEq ι] in
/-- In a genuine metric, radius-zero balls are singletons. -/
theorem singleton_support_of_zero_range
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i 0)) :
    ∀ i, h i ∈ supportedOperators d ({i} : Set ι) := by
  intro i
  simpa only [Metric.closedBall_zero] using hsupp i

/-- The Gaussian filter under every retained local generator fixes a zero-range term. -/
theorem gaussianFilteredTerm_sum_eq_of_zero_range
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i 0))
    (s : Finset ι) (q ΔE : ℝ) (i : ι) :
    gaussianFilteredTerm q ΔE (∑ j ∈ s, h j) (h i) = h i :=
  gaussianFilteredTerm_sum_eq_of_singleton_support h
    (singleton_support_of_zero_range h hsupp) s q ΔE i

/-- Full and truncated filters agree exactly in the physical metric zero-range case. -/
theorem gaussianFilteredTerm_full_and_sum_eq_of_zero_range
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i 0))
    (s : Finset ι) (q ΔE : ℝ) (i : ι) :
    gaussianFilteredTerm q ΔE (∑ j, h j) (h i) = h i ∧
      gaussianFilteredTerm q ΔE (∑ j ∈ s, h j) (h i) = h i :=
  ⟨gaussianFilteredTerm_sum_eq_of_zero_range h hsupp Finset.univ q ΔE i,
    gaussianFilteredTerm_sum_eq_of_zero_range h hsupp s q ΔE i⟩

/-- A zero-range term preserves the full ground eigenspace exactly. -/
theorem starProjection_term_eq_of_zero_range
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i 0))
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hψ : ψ ∈ groundEigenspace (∑ j, h j) E₀) (i : ι) :
    (groundEigenspace (∑ j, h j) E₀).starProjection (toEuclideanLin (h i) ψ) =
      toEuclideanLin (h i) ψ :=
  starProjection_apply_eq_of_commute (commute_sum_of_singleton_support h
    (singleton_support_of_zero_range h hsupp) Finset.univ i) hψ

/-- Hastings, arXiv:cond-mat/0508554v3, eq. `facld`: in the metric zero-range case
its excited component vanishes exactly, for every retained generator. -/
theorem sub_starProjection_gaussianFilteredTerm_sum_eq_zero_of_zero_range
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, h i ∈ supportedOperators d (Metric.closedBall i 0))
    (s : Finset ι) (q ΔE : ℝ) {E₀ : ℝ} {ψ : EuclideanSpace ℂ (ι → Fin d)}
    (hψ : ψ ∈ groundEigenspace (∑ j, h j) E₀) (i : ι) :
    toEuclideanLin (gaussianFilteredTerm q ΔE (∑ j ∈ s, h j) (h i)) ψ -
      (groundEigenspace (∑ j, h j) E₀).starProjection
        (toEuclideanLin (gaussianFilteredTerm q ΔE (∑ j ∈ s, h j) (h i)) ψ) = 0 := by
  rw [gaussianFilteredTerm_sum_eq_of_zero_range h hsupp s q ΔE i,
    starProjection_term_eq_of_zero_range h hsupp hψ i, sub_self]

end Metric

end TNLean.Lattice
