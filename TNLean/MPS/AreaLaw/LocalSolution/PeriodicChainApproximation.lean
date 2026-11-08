/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicCoarsening
import TNLean.MPS.AreaLaw.LocalSolution.FiniteHierarchyApproximation

/-!
# The quadratic logarithmic hierarchy on a periodic chain

The local periodic terms determine the coarse operators and every spectral projection.
The sharp centred bound is `K=4ℓJ`. If the physical local error decays as `exp(-ηℓ)`,
write `r=ηℓ` and `J_eff=4J/η`; then `K=J_eff*r`, independently of chain length.
The explicit quadratic logarithmic projection length therefore controls both the
sum of spectral radii and the total error in the original Hamiltonian. In the source
application, the comparison summands `gᵢ` are the full Gaussian-filtered terms, whose
sum is the original Hamiltonian; the small local errors compare these summands with
the truncated terms, rather than with the unfiltered local interactions. The only
spectral gap assumed is that of the original physical Hamiltonian.

**Local fix (periodic hierarchy):** the norm deficiency uses the corrected recurrence,
and one extra spectral window treats the closing edge. These are documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`.

The physical sites in this module form regular blocks `Fin N × Fin (2*ℓ)`.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 609–730.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The explicit quadratic logarithmic length also absorbs a linear truncation prefactor.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
theorem hierarchyTruncationError_mul_length_le_eighth_gap {h : ℕ} (hh : 2 ≤ h)
    {J Δ r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) :
    (2 : ℝ) ^ h * J * r * Real.exp (-r) ≤ Δ / 8 := by
  have hH : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hr0 : 0 ≤ r := (by positivity : 0 ≤ 512 * (h : ℝ) ^ 2).trans
    ((hierarchyProjectionLength_ge_square h J Δ).trans hr)
  have hJr : 0 ≤ J * r := mul_nonneg hJ.le hr0
  have hbudget : 2 * J * r / 9 ≤ J * r := by nlinarith
  have hE := hierarchyWindowEnergy_le_quarter_gap hh hJ hΔ hr hbudget
  have hexp : Real.exp (-r) ≤ Real.exp (-r / (4 * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    apply neg_le_neg
    rw [div_le_iff₀ (by positivity : 0 < 4 * (h : ℝ))]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * (h : ℝ) - 1) hr0]
  calc
    _ ≤ (2 : ℝ) ^ h * J * r * Real.exp (-r / (4 * (h : ℝ))) := by gcongr
    _ ≤ Δ / 8 := by nlinarith

/-- The physical-gap count accepts any approximation error below one eighth of the gap.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
theorem card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_error
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (blk : ι → ℕ)
    (a : ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ j, 0 < j → a j ∈ supportedOperators d {i | blk i + 1 = j ∨ blk i = j})
    (ha : ∀ j, (a j).IsHermitian)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {K r J Δ δ : ℝ} (hK : 0 < K)
    {h : ℕ} (hh : 2 ≤ h) (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength h J Δ ≤ r) (hbound : K ≤ J * r)
    {H P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = E₀)
    (happrox : ‖H - ∑ j ∈ Finset.range (2 ^ h), a j‖ ≤ δ) (hδ : δ ≤ Δ / 8)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ)
    (s : Finset κ)
    (hkeep : ∀ j ∈ s, toEuclideanLin (periodicHierarchyProjection a ψ K r h) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  have hbudget : 2 * δ +
      (hierarchySum (fun m _ => hierarchyWindowRadius K r h m) h 0 +
        hierarchyWindowRadius K r h h) ≤ Δ / 2 := by
    linarith [hierarchySum_windowRadius_add_le_quarter_gap hh hJ hΔ hK.le hr hbound 0]
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

/-- The actual periodic local terms determine the sharp one-dimensional hierarchy.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
noncomputable def periodicCoarseProjection {N ℓ d : ℕ}
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (ψ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)) (J r : ℝ) :=
  periodicHierarchyProjection (extendFiniteEdges (periodicCoarseOperator a)) ψ
    (4 * (ℓ : ℝ) * J) r (finiteHierarchyDepth N)

set_option maxHeartbeats 600000 in
-- The product-indexed configuration spaces require additional definitional reductions.
/-- Actual periodic local residuals give a nearby unit vector retained throughout the tree.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
theorem exists_unit_mem_periodicCoarseProjection {N ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | periodicPhysicalDistance i v ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian)
    {ψ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)} (hψ : ‖ψ‖ = 1)
    {J η Δ r : ℝ} (hJ : 0 < J)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth N) (4 * J / η) Δ ≤ r)
    (hres : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ J * Real.exp (-r))
    (hbound : ∀ i, ‖a i‖ ≤ J) :
    let b := periodicCoarseOperator a
    let h := finiteHierarchyDepth N
    let K := 4 * (ℓ : ℝ) * J
    ∃ φ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (periodicCoarseProjection a ψ J r) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hK : 0 < 4 * (ℓ : ℝ) * J := by positivity
  apply exists_unit_mem_periodicHierarchyProjection_of_finite
    (ι := Fin N × Fin (2 * ℓ)) (d := d) (N := N) (h := finiteHierarchyDepth N)
    (fun i ↦ (i.1 : ℕ)) (periodicCoarseOperator a)
    (periodicCoarseOperator_mem_supportedOperators hℓ a hsupp)
    (isHermitian_periodicCoarseOperator a ha) hψ hK (two_le_finiteHierarchyDepth N) hr
    _ (centeredNorm_periodicCoarseOperator_le a hψ hJ.le hbound)
  intro j
  have hresj := residual_periodicCoarseOperator_le a ψ
    (mul_nonneg hJ.le (Real.exp_pos _).le) hres j
  push_cast at hresj
  nlinarith [mul_nonneg (mul_nonneg hℓr.le hJ.le) (Real.exp_pos (-r)).le]

set_option maxHeartbeats 800000 in
-- The product-indexed configuration spaces require additional definitional reductions.
/-- The physical gap gives the final state count at quadratic logarithmic range,
with both the pair norms and the total truncation error derived from the local terms.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
theorem card_le_two_mul_re_trace_of_periodicCoarseProjection {N ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a g : (Fin N × Fin (2 * ℓ)) →
      Matrix ((Fin N × Fin (2 * ℓ)) → Fin d) ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | periodicPhysicalDistance i v ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian)
    {ψ : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)} (hψ : ‖ψ‖ = 1)
    {J η Δ r : ℝ} (hJ : 0 < J) (hη : 0 < η) (hΔ : 0 < Δ)
    (hrscale : r = η * (ℓ : ℝ))
    (hr : hierarchyProjectionLength (finiteHierarchyDepth N) (4 * J / η) Δ ≤ r)
    (herror : ∀ i, ‖g i - a i‖ ≤ J * Real.exp (-r))
    {P₀ : Matrix ((Fin N × Fin (2 * ℓ)) → Fin d)
      ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin (∑ i, g i) v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin (∑ i, g i) ψ⟫_ℂ).re = E₀)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)}
    (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hkeep : ∀ j ∈ s, toEuclideanLin (periodicCoarseProjection a ψ J r) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  let b := periodicCoarseOperator a
  let h := finiteHierarchyDepth N
  let K : ℝ := 4 * (ℓ : ℝ) * J
  let Jeff : ℝ := 4 * J / η
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hK : 0 < K := by dsimp [K]; positivity
  have hJeff : 0 < Jeff := by dsimp [Jeff]; positivity
  have hKr : K = Jeff * r := by
    dsimp [K, Jeff]
    rw [hrscale]
    field_simp
  have hsumerror : ‖(∑ i, g i) - ∑ i, a i‖ ≤
      (N : ℝ) * (2 * (ℓ : ℝ)) * J * Real.exp (-r) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖g i - a i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N × Fin (2 * ℓ), J * Real.exp (-r) :=
        Finset.sum_le_sum fun i _ ↦ herror i
      _ = _ := by simp [Fintype.card_prod]; ring
  have hNreal : (N : ℝ) ≤ (2 : ℝ) ^ h := by
    exact_mod_cast le_two_pow_finiteHierarchyDepth N
  have hcoeff : (N : ℝ) * (2 * (ℓ : ℝ)) * J ≤ (2 : ℝ) ^ h * Jeff * r := by
    have hc := mul_le_mul_of_nonneg_right hNreal hK.le
    rw [mul_assoc ((2 : ℝ) ^ h) Jeff r, ← hKr]
    dsimp [K] at hc ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (mul_nonneg hℓr.le hJ.le)]
  have happrox : ‖(∑ i, g i) - ∑ j ∈ Finset.range (2 ^ h), extendFiniteEdges b j‖ ≤
      (2 : ℝ) ^ h * Jeff * r * Real.exp (-r) := by
    rw [sum_extendFiniteEdges_of_le b (le_two_pow_finiteHierarchyDepth N)]
    change ‖(∑ i, g i) - ∑ j, periodicCoarseOperator a j‖ ≤ _
    rw [sum_periodicCoarseOperator]
    exact hsumerror.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
  exact card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_error
    (ι := Fin N × Fin (2 * ℓ)) (d := d) (fun i ↦ (i.1 : ℕ)) (extendFiniteEdges b)
    (extendFiniteEdges_mem_supportedOperators _ b
      (periodicCoarseOperator_mem_supportedOperators hℓ a hsupp))
    (isHermitian_extendFiniteEdges b (isHermitian_periodicCoarseOperator a ha))
    hψ hK (two_le_finiteHierarchyDepth N) hJeff hΔ hr hKr.le hP₀ hgap hE₀ happrox
    (hierarchyTruncationError_mul_length_le_eighth_gap
      (two_le_finiteHierarchyDepth N) hJeff hΔ hr) hφ s hkeep

/-- The actual periodic grouping has a quadratic upper binary logarithmic length.
The effective coupling `4J/η` is independent of the number of physical sites.
For the coarsening in Hastings, arXiv:cond-mat/0508554v3, lines 609–730. -/
theorem hierarchyProjectionLength_periodicCoarse_le {N ℓ : ℕ} (hℓ : 0 < ℓ)
    (J η Δ : ℝ) :
    hierarchyProjectionLength (finiteHierarchyDepth N) (4 * J / η) Δ ≤
      512 * ((Nat.clog 2 (N * (2 * ℓ)) : ℝ) + 2) ^ 2 *
        (1 + max 0 (Real.log ((4 * J / η) / Δ))) := by
  have hN : N ≤ N * (2 * ℓ) := Nat.le_mul_of_pos_right N (by omega)
  have hclog := Nat.clog_mono_right 2 hN
  refine (hierarchyProjectionLength_finiteHierarchyDepth_le N (4 * J / η) Δ).trans ?_
  gcongr

end TNLean.MPS.AreaLaw.LocalSolution
