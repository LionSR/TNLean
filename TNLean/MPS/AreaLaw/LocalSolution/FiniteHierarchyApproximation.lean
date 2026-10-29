/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.FiniteHierarchyEdges
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyApproximation
import TNLean.MPS.AreaLaw.LocalSolution.HierarchyNesting

/-!
# The quantitative hierarchy from finite physical inputs

The finite periodic edge family determines every projection, including the closing-link
window. Its local residual and centred-norm bounds yield a nonzero retained space. The gap
of the physical Hamiltonian and the error of its finite approximating sum give the final
state count. No conditions on interaction terms outside the finite chain are assumed.

**Local fix (periodic hierarchy):** these statements use the corrected norm deficiency
and one extra closing-link window, as recorded in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

Source: Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d h N : ℕ}

/-- The projection length for a finite chain is explicitly quadratic in its upper binary
logarithm. Hastings, arXiv:cond-mat/0508554v3, lines 709–720. -/
theorem hierarchyProjectionLength_finiteHierarchyDepth_le (N : ℕ) (J Δ : ℝ) :
    hierarchyProjectionLength (finiteHierarchyDepth N) J Δ ≤
      512 * ((Nat.clog 2 N : ℝ) + 2) ^ 2 * (1 + max 0 (Real.log (J / Δ))) := by
  unfold hierarchyProjectionLength
  gcongr
  exact_mod_cast finiteHierarchyDepth_le_clog_add_two N

/-- An effective coupling bound linear in the number of physical terms still gives an
explicit cubic bound in the upper binary logarithm for the projection length. This is
an elementary scalar consequence, independent of the geometry of the grouping.
Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem hierarchyProjectionLength_finiteHierarchyDepth_mul_le {N : ℕ} (hN : 1 ≤ N)
    {C J Δ : ℝ} (hC : 0 < C) (hJ : 0 < J) (hΔ : 0 < Δ) :
    hierarchyProjectionLength (finiteHierarchyDepth N) ((N : ℝ) * C * J) Δ ≤
      512 * ((Nat.clog 2 N : ℝ) + 2) ^ 3 *
        (1 + max 0 (Real.log (C * J / Δ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hlogN : Real.log (N : ℝ) ≤ (Nat.clog 2 N : ℝ) := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ Nat.clog 2 N) := Real.log_le_log hNpos (by
        exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) N)
      _ = (Nat.clog 2 N : ℝ) * Real.log 2 := Real.log_pow 2 _
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 N)]
  have hlog : Real.log ((N : ℝ) * C * J / Δ) =
      Real.log (N : ℝ) + Real.log (C * J / Δ) := by
    rw [show (N : ℝ) * C * J / Δ = (N : ℝ) * (C * J / Δ) by ring]
    exact Real.log_mul hNpos.ne' (div_pos (mul_pos hC hJ) hΔ).ne'
  have hmax : max 0 (Real.log (N : ℝ) + Real.log (C * J / Δ)) ≤
      Real.log (N : ℝ) + max 0 (Real.log (C * J / Δ)) := by
    apply max_le
    · positivity
    · exact add_le_add (le_refl (Real.log (N : ℝ)))
        (le_max_right (0 : ℝ) (Real.log (C * J / Δ)))
  have hfactor : 1 + max 0 (Real.log ((N : ℝ) * C * J / Δ)) ≤
      ((Nat.clog 2 N : ℝ) + 2) * (1 + max 0 (Real.log (C * J / Δ))) := by
    rw [hlog]
    have hcross := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Nat.clog 2 N))
      (le_max_left 0 (Real.log (C * J / Δ)))
    nlinarith [le_max_left 0 (Real.log (C * J / Δ))]
  calc
    _ ≤ 512 * ((Nat.clog 2 N : ℝ) + 2) ^ 2 *
        (1 + max 0 (Real.log ((N : ℝ) * C * J / Δ))) :=
      hierarchyProjectionLength_finiteHierarchyDepth_le N _ _
    _ ≤ 512 * ((Nat.clog 2 N : ℝ) + 2) ^ 2 *
        (((Nat.clog 2 N : ℝ) + 2) * (1 + max 0 (Real.log (C * J / Δ)))) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

/-- The actual finite periodic edge family constructs a nonzero final space at the
explicit logarithmic projection length. The residual assumption is equation `low`.
Hastings, arXiv:cond-mat/0508554v3, lines 633–639 and 705–711. -/
theorem exists_unit_mem_periodicHierarchyProjection_of_finite (blk : ι → ℕ)
    (a : Fin N → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ j : Fin N, 0 < (j : ℕ) →
      a j ∈ supportedOperators d {i | blk i + 1 = (j : ℕ) ∨ blk i = (j : ℕ)})
    (ha : ∀ j, (a j).IsHermitian)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {K r J Δ : ℝ} (hK : 0 < K)
    (hh : 2 ≤ h) (hr : hierarchyProjectionLength h J Δ ≤ r)
    (hres : ∀ j, ‖toEuclideanLin
      (a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ K * Real.exp (-r))
    (hbound : ∀ j, ‖a j - ((⟪ψ, toEuclideanLin (a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤ K) :
    ∃ φ : EuclideanSpace ℂ (ι → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (periodicHierarchyProjection (extendFiniteEdges a) ψ K r h) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges a))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges a) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ := by
  obtain ⟨φ, hφ, hkeep, hnear⟩ := exists_unit_mem_periodicHierarchyProjection blk
    (extendFiniteEdges a) (extendFiniteEdges_mem_supportedOperators blk a hsupp)
    (isHermitian_extendFiniteEdges a ha) hψ hK hh hr
    (residual_extendFiniteEdges_le a ψ (mul_nonneg hK.le (Real.exp_pos _).le) hres)
    (centeredNorm_extendFiniteEdges_le a ψ hK.le hbound)
  refine ⟨φ, hφ, hkeep, hnear, ?_⟩
  exact isRetainedHierarchy_of_hierarchyClosingProjection blk
    (hierarchyEdge (extendFiniteEdges a))
    (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges a) m k) ψ⟫_ℂ).re)
    (hierarchyWindowRadius K r h)
    (hierarchyEdge_extendFiniteEdges_mem_supportedOperators blk a hsupp)
    (fun m k ↦ isHermitian_extendFiniteEdges a ha _) h (extendFiniteEdges a 0)
    (⟪ψ, toEuclideanLin (extendFiniteEdges a 0) ψ⟫_ℂ).re hkeep

/-- The gap of the physical Hamiltonian bounds every orthonormal family retained by
the hierarchy constructed from the finite edge family. The finite approximating sum
is explicit, and its error is derived from the same chosen projection length.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730. -/
theorem card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_finite (blk : ι → ℕ)
    (a : Fin N → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hN : N ≤ 2 ^ h)
    (hsupp : ∀ j : Fin N, 0 < (j : ℕ) →
      a j ∈ supportedOperators d {i | blk i + 1 = (j : ℕ) ∨ blk i = (j : ℕ)})
    (ha : ∀ j, (a j).IsHermitian)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {K r J Δ : ℝ} (hK : 0 < K)
    (hh : 2 ≤ h) (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hbound : K ≤ J * r)
    {H P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = E₀)
    (happrox : ‖H - ∑ j : Fin N, a j‖ ≤ (N : ℝ) * J * Real.exp (-r))
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ)
    (s : Finset κ)
    (hkeep : ∀ j ∈ s,
      toEuclideanLin (periodicHierarchyProjection (extendFiniteEdges a) ψ K r h) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  have happrox' : ‖H - ∑ j ∈ Finset.range (2 ^ h), extendFiniteEdges a j‖ ≤
      (2 : ℝ) ^ h * J * Real.exp (-r) := by
    rw [sum_extendFiniteEdges_of_le a hN]
    have hNreal : (N : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hN
    exact happrox.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hNreal hJ.le) (Real.exp_pos _).le)
  exact card_le_two_mul_re_trace_of_periodicHierarchyProjection blk (extendFiniteEdges a)
    (extendFiniteEdges_mem_supportedOperators blk a hsupp)
    (isHermitian_extendFiniteEdges a ha) hψ hK hh hJ hΔ hr hbound hP₀ hgap hE₀
    happrox' hφ s hkeep

end TNLean.MPS.AreaLaw.LocalSolution
