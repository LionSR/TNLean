/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyEdges
import Mathlib.Data.Nat.Log

/-!
# Finite interaction families in the binary hierarchy

A finite family of periodic edges is extended by zero beyond its length. Its Hermiticity,
nearest-neighbour support, residual estimates and centred operator bounds then hold for
all natural indices. The periodic sum is exactly the original finite sum.

This realizes the finite chain of Hastings, arXiv:cond-mat/0508554v3, Section II,
lines 609–628 and 668–730, without assumptions on nonexistent interaction terms.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- Extend a finite edge family by zero beyond the chain length.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628. -/
def extendFiniteEdges {A : Type*} [Zero A] {N : ℕ} (a : Fin N → A) (j : ℕ) : A :=
  if hj : j < N then a ⟨j, hj⟩ else 0

@[simp]
theorem extendFiniteEdges_apply_fin {A : Type*} [Zero A] {N : ℕ} (a : Fin N → A)
    (j : Fin N) : extendFiniteEdges a j = a j := by simp [extendFiniteEdges, j.isLt]

/-- Every edge beyond the finite chain is zero. -/
theorem extendFiniteEdges_eq_zero {A : Type*} [Zero A] {N : ℕ} (a : Fin N → A)
    {j : ℕ} (hj : N ≤ j) : extendFiniteEdges a j = 0 := by
  simp only [extendFiniteEdges, dite_eq_right (Nat.not_lt.mpr hj)]

/-- Extension by zero preserves the physical sum over the finite chain.
Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 709–720. -/
theorem sum_extendFiniteEdges {A : Type*} [AddCommMonoid A] {N : ℕ} (a : Fin N → A) :
    ∑ j ∈ Finset.range N, extendFiniteEdges a j = ∑ j : Fin N, a j := by
  rw [Finset.sum_range]
  simp only [extendFiniteEdges_apply_fin]

/-- Padding the finite family by zero preserves its sum on every larger interval.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 709–720. -/
theorem sum_extendFiniteEdges_of_le {A : Type*} [AddCommMonoid A] {N L : ℕ}
    (a : Fin N → A) (hNL : N ≤ L) :
    ∑ j ∈ Finset.range L, extendFiniteEdges a j = ∑ j : Fin N, a j := by
  rw [← sum_extendFiniteEdges a]
  symm
  apply Finset.sum_subset (Finset.range_mono hNL)
  intro j _ hj
  exact extendFiniteEdges_eq_zero a (by simpa only [Finset.mem_range, not_lt] using hj)

/-- The number of binary levels needed for a finite chain, with at least two levels.
Hastings, arXiv:cond-mat/0508554v3, lines 705–711. -/
def finiteHierarchyDepth (N : ℕ) : ℕ := max 2 (Nat.clog 2 N)

/-- The chosen depth permits the uniform hierarchy estimates. -/
theorem two_le_finiteHierarchyDepth (N : ℕ) : 2 ≤ finiteHierarchyDepth N := le_max_left _ _

/-- Zero padding to the chosen dyadic length accommodates every finite chain. -/
theorem le_two_pow_finiteHierarchyDepth (N : ℕ) : N ≤ 2 ^ finiteHierarchyDepth N :=
  (Nat.le_pow_clog (by decide : 1 < 2) N).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right _ _))

/-- The chosen number of levels is at most two plus the upper binary logarithm. -/
theorem finiteHierarchyDepth_le_clog_add_two (N : ℕ) :
    finiteHierarchyDepth N ≤ Nat.clog 2 N + 2 := by unfold finiteHierarchyDepth; omega

/-- The tree edges and closing edge give precisely the finite periodic sum.
Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 709–720. -/
theorem hierarchySum_hierarchyEdge_extend_add_zero {A : Type*} [AddCommMonoid A]
    {N h : ℕ} (a : Fin N → A) (hN : N ≤ 2 ^ h) :
    hierarchySum (hierarchyEdge (extendFiniteEdges a)) h 0 + extendFiniteEdges a 0 =
      ∑ j : Fin N, a j := by
  rw [hierarchySum_hierarchyEdge_add_zero, sum_extendFiniteEdges_of_le a hN]

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ}

omit [Fintype n] [DecidableEq n] in
/-- Hermiticity of the actual finite edge operators implies Hermiticity of their extension.
Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 640–642. -/
theorem isHermitian_extendFiniteEdges (a : Fin N → Matrix n n ℂ)
    (ha : ∀ j, (a j).IsHermitian) (j : ℕ) : (extendFiniteEdges a j).IsHermitian := by
  by_cases hj : j < N
  · simpa only [extendFiniteEdges, dite_eq_left hj] using ha ⟨j, hj⟩
  · simpa only [extendFiniteEdges, dite_eq_right hj] using
      (isHermitian_zero : (0 : Matrix n n ℂ).IsHermitian)

/-- Finite local residual estimates extend to all natural indices; added zero terms have
zero centred residual. Hastings, arXiv:cond-mat/0508554v3, equation `low`, lines 633–639. -/
theorem residual_extendFiniteEdges_le (a : Fin N → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ j, ‖toEuclideanLin
      (a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε) (j : ℕ) :
    ‖toEuclideanLin
      (extendFiniteEdges a j -
        ((⟪ψ, toEuclideanLin (extendFiniteEdges a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε := by
  by_cases hj : j < N
  · simpa only [extendFiniteEdges, dite_eq_left hj] using ha ⟨j, hj⟩
  · simpa [extendFiniteEdges, hj] using hε

/-- Finite centred-norm estimates extend to all natural indices.
Hastings, arXiv:cond-mat/0508554v3, lines 676–695. -/
theorem centeredNorm_extendFiniteEdges_le (a : Fin N → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ j, ‖a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K) (j : ℕ) :
    ‖extendFiniteEdges a j -
      ((⟪ψ, toEuclideanLin (extendFiniteEdges a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K := by
  by_cases hj : j < N
  · simpa only [extendFiniteEdges, dite_eq_left hj] using ha ⟨j, hj⟩
  · simpa [extendFiniteEdges, hj] using hK

end Matrices

section Support

variable {ι : Type*} [Fintype ι] {d N : ℕ}

/-- Internal finite edges retain their two-supersite support after zero extension.
The closing edge is unrestricted here and is treated by its separate spectral window.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 668–685. -/
theorem extendFiniteEdges_mem_supportedOperators (blk : ι → ℕ)
    (a : Fin N → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ j : Fin N, 0 < (j : ℕ) →
      a j ∈ supportedOperators d {i | blk i + 1 = (j : ℕ) ∨ blk i = (j : ℕ)})
    (j : ℕ) (hj : 0 < j) :
    extendFiniteEdges a j ∈ supportedOperators d {i | blk i + 1 = j ∨ blk i = j} := by
  by_cases hjN : j < N
  · simpa only [extendFiniteEdges, dite_eq_left hjN] using ha ⟨j, hjN⟩ hj
  · simpa only [extendFiniteEdges, dite_eq_right hjN] using
      (Submodule.zero_mem (supportedOperators d {i | blk i + 1 = j ∨ blk i = j}))

/-- Every joining operator of the hierarchy has its parent-block support, derived from
only the finite internal-edge assumptions.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628 and 668–685. -/
theorem hierarchyEdge_extendFiniteEdges_mem_supportedOperators (blk : ι → ℕ)
    (a : Fin N → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ha : ∀ j : Fin N, 0 < (j : ℕ) →
      a j ∈ supportedOperators d {i | blk i + 1 = (j : ℕ) ∨ blk i = (j : ℕ)})
    (m k : ℕ) : hierarchyEdge (extendFiniteEdges a) m k ∈
      supportedOperators d (levelBlock blk (m + 1) k) :=
  hierarchyEdge_mem_supportedOperators blk (extendFiniteEdges a)
    (extendFiniteEdges_mem_supportedOperators blk a ha) m k

end Support

end TNLean.MPS.AreaLaw.LocalSolution
