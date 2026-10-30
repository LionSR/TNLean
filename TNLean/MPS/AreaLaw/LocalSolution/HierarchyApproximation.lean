/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyRadius
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyEdges
import TNLean.MPS.AreaLaw.LocalSolution.PhysicalEnergy

/-!
# The quantitative periodic hierarchy

The pair operators determine every projection of the hierarchy. The window radii
and a sufficient projection length are explicit. The residual and operator-norm
estimates give a nonzero final space. The gap of the physical Hamiltonian bounds
its dimension, after the error in the truncated sum has been included.

Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730, assumes the local
residual bound of equation `low`. That bound remains an input here; the projections,
their recursion, their radii, and the energy of their final states are constructed.

**Local fix (periodic hierarchy):** the recurrence measures every level against
the original state, and one additional spectral window treats the closing edge.
These corrections are documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

section Definition

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The periodic projection constructed from the actual edge operators and their
expectations in the reference state. Edge zero closes the periodic chain.
Hastings, arXiv:cond-mat/0508554v3, lines 626–628 and 668–730. -/
noncomputable def periodicHierarchyProjection (a : ℕ → Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ n) (K r : ℝ) (h : ℕ) : Matrix n n ℂ :=
  hierarchyClosingProjection (hierarchyEdge a)
    (fun m k => (⟪ψ, toEuclideanLin (hierarchyEdge a m k) ψ⟫_ℂ).re)
    (hierarchyWindowRadius K r h) h (a 0) (⟪ψ, toEuclideanLin (a 0) ψ⟫_ℂ).re

end Definition

section Supersites

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- With the explicit length, the corrected periodic hierarchy retains a unit
vector. The only estimates assumed are the local residual and centred-norm bounds.
Hastings, arXiv:cond-mat/0508554v3, equation `low` and lines 609–707. -/
theorem exists_unit_mem_periodicHierarchyProjection (blk : ι → ℕ)
    (a : ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ j, 0 < j → a j ∈ supportedOperators d {i | blk i + 1 = j ∨ blk i = j})
    (ha : ∀ j, (a j).IsHermitian)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {K r J Δ : ℝ} (hK : 0 < K)
    {h : ℕ} (hh : 2 ≤ h) (hr : hierarchyProjectionLength h J Δ ≤ r)
    (hres : ∀ j, ‖toEuclideanLin
      (a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ K * Real.exp (-r))
    (hbound : ∀ j, ‖a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K) :
    ∃ φ : EuclideanSpace ℂ (ι → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (periodicHierarchyProjection a ψ K r h) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) := by
  obtain ⟨φ, hφ, hPφ, hnear⟩ := exists_unit_mem_hierarchyClosingProjection blk
    (hierarchyEdge a) (fun m k => (⟪ψ, toEuclideanLin (hierarchyEdge a m k) ψ⟫_ℂ).re)
    (hierarchyWindowRadius K r h) (hierarchyEdge_mem_supportedOperators blk a hsupp)
    (fun m k => ha _) (hierarchyWindowRadius_pos hK r h) hψ
    (fun m k => hres _) (fun m k => hbound _) h (ha 0)
    (⟪ψ, toEuclideanLin (a 0) ψ⟫_ℂ).re (hres 0) (hbound 0)
    (hierarchyDeficiency_window_succ_lt_one_of_length hh hK hr)
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 512 * (h : ℝ) ^ 2).trans
    ((hierarchyProjectionLength_ge_square h J Δ).trans hr)
  exact ⟨φ, hφ, hPφ, hnear.trans (mul_le_mul_of_nonneg_left
    (hierarchyDeficiency_window_succ_le hK hr0 hh) (by norm_num))⟩

/-- Every orthonormal family retained by the constructed periodic projection has
at most twice as many members as the ground-space dimension. The only gap assumed
is that of the physical Hamiltonian `H`; the explicit length controls both errors.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730. -/
theorem card_le_two_mul_re_trace_of_periodicHierarchyProjection (blk : ι → ℕ)
    (a : ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ j, 0 < j → a j ∈ supportedOperators d {i | blk i + 1 = j ∨ blk i = j})
    (ha : ∀ j, (a j).IsHermitian)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {K r J Δ : ℝ} (hK : 0 < K)
    {h : ℕ} (hh : 2 ≤ h) (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hbound : K ≤ J * r)
    {H P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = E₀)
    (happrox : ‖H - ∑ j ∈ Finset.range (2 ^ h), a j‖ ≤
      (2 : ℝ) ^ h * J * Real.exp (-r))
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ)
    (s : Finset κ)
    (hkeep : ∀ j ∈ s, toEuclideanLin (periodicHierarchyProjection a ψ K r h) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  have hbudget : 2 * ((2 : ℝ) ^ h * J * Real.exp (-r)) +
      (hierarchySum (fun m _ => hierarchyWindowRadius K r h m) h 0 +
        hierarchyWindowRadius K r h h) ≤ Δ / 2 := by
    linarith [hierarchyTruncationError_le_eighth_gap hh hJ hΔ hr,
      hierarchySum_windowRadius_add_le_quarter_gap hh hJ hΔ hK.le hr hbound 0]
  refine card_le_two_mul_re_trace_of_approximation hP₀ hΔ hgap hψ hE₀ happrox hbudget hφ s ?_
  intro j hj
  rw [← hierarchySum_hierarchyEdge_add_zero]
  exact re_inner_supersiteHierarchySum_add_le_add blk
    (hierarchyProjection (hierarchyEdge a)
      (fun m k => (⟪ψ, toEuclideanLin (hierarchyEdge a m k) ψ⟫_ℂ).re)
      (hierarchyWindowRadius K r h))
    (hierarchyEdge a) (hierarchyWindowRadius K r h)
    (hierarchyProjection_zero _ _ _) (hierarchyProjection_succ _ _ _)
    (hierarchyEdge_mem_supportedOperators blk a hsupp) (fun m k => ha _)
    (fun m => (hierarchyWindowRadius_pos hK r h m).le) h (ha 0)
    (hierarchyWindowRadius_pos hK r h h).le (hφ.1 j) (hkeep j hj)

end Supersites

end TNLean.MPS.AreaLaw.LocalSolution
