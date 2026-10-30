/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.CoordinateSliceHierarchy
import TNLean.MPS.AreaLaw.LocalSolution.FiniteHierarchyApproximation

/-!
# The coordinate-slice approximation from physical local terms

The physical terms determine the coarse edge operators, every spectral window, and the
final projection. Local residual and norm bounds give a nearby retained unit vector.
The physical spectral gap bounds the number of orthonormal retained states.

**Scope restriction (coordinate slices):** this construction uses one nonnegative integer
coordinate, with each term supported within the stated coordinate radius of its centre.
The metric bridge in `CoordinateSliceHierarchy.lean` derives this support from metric balls
on finite coordinate boxes and on metrics dominating the coordinate maximum metric.
This is one coordinate-slice form of the higher-dimensional extension in Hastings,
arXiv:cond-mat/0508554v3, lines 745–756; the corrected deficiency and closing window are
recorded in `docs/paper-gaps/hastings05_hierarchical_projection.tex` and
`docs/paper-gaps/hastings05_hierarchical_energy.tex`. The precise coordinate-box scope is
recorded in `docs/paper-gaps/hastings05_coordinate_slices.tex`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d N : ℕ}

/-- The final projection determined by the physical terms and their coordinate slices.
The coarse coupling bound is `2 N_phys J`. Hastings, arXiv:cond-mat/0508554v3,
lines 609–730 and 745–756. -/
noncomputable def coordinateSliceProjection (z : ι → ℕ) (ℓ : ℕ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (ψ : EuclideanSpace ℂ (ι → Fin d)) (J r : ℝ) :
    Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  periodicHierarchyProjection (extendFiniteEdges (coordinateSliceOperator z ℓ hN a)) ψ
    (2 * Fintype.card ι * J) r (finiteHierarchyDepth N)

/-- The actual local terms give a nearby unit vector retained at every node. Coverage
of the physical sites by the finite slice family is included explicitly.
The only residual input is the local estimate of equation `low`.
Hastings, arXiv:cond-mat/0508554v3, lines 633–639, 705–743 and 745–756. -/
theorem exists_unit_mem_coordinateSliceProjection [Nonempty ι] (z : ι → ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N) (hz : ∀ i, z i < N * (2 * ℓ))
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | Nat.dist (z v) (z i) ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian) {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1)
    {J Δ r : ℝ} (hJ : 0 < J)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth N) (2 * Fintype.card ι * J) Δ ≤ r)
    (hres : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ J * Real.exp (-r))
    (hbound : ∀ i, ‖a i‖ ≤ J) :
    let b := coordinateSliceOperator z ℓ hN a
    let h := finiteHierarchyDepth N
    let K := 2 * Fintype.card ι * J
    ∃ φ : EuclideanSpace ℂ (ι → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (coordinateSliceProjection z ℓ hN a ψ J r) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ ∧
      ∀ i, coordinateSlice ℓ (z i) < N := by
  let b := coordinateSliceOperator z ℓ hN a
  let K : ℝ := 2 * Fintype.card ι * J
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hK : 0 < K := by dsimp [K]; positivity
  have hresb : ∀ j, ‖toEuclideanLin
      (b j - ((⟪ψ, toEuclideanLin (b j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ K * Real.exp (-r) := by
    intro j
    refine (residual_coordinateSliceOperator_le z ℓ hN a ψ
      (mul_nonneg hJ.le (Real.exp_pos _).le) hres j).trans ?_
    dsimp [K]
    nlinarith [mul_nonneg hcard.le (mul_nonneg hJ.le (Real.exp_pos (-r)).le)]
  obtain ⟨φ, hφ, hkeep, hnear, htree⟩ := exists_unit_mem_periodicHierarchyProjection_of_finite
    (fun i ↦ coordinateSlice ℓ (z i)) b
    (coordinateSliceOperator_mem_supportedOperators z hℓ hN a hsupp)
    (isHermitian_coordinateSliceOperator z ℓ hN a ha) hψ hK
    (two_le_finiteHierarchyDepth N) hr hresb
    (centeredNorm_coordinateSliceOperator_le_two_mul z ℓ hN a hψ hJ.le hbound)
  exact ⟨φ, hφ, hkeep, hnear, htree, fun i ↦ coordinateSlice_lt hℓ (hz i)⟩

/-- The physical gap bounds the number of orthonormal states retained by the explicit
coordinate-slice projection. No gap for an approximating operator is assumed.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730 and 745–756. -/
theorem card_le_two_mul_re_trace_of_coordinateSliceProjection [Nonempty ι] (z : ι → ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (a : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d {v | Nat.dist (z v) (z i) ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian) {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1)
    {J Δ r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth N) (2 * Fintype.card ι * J) Δ ≤ r)
    {H P₀ : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ (ι → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = E₀)
    (happrox : ‖H - ∑ i, a i‖ ≤ Fintype.card ι * J * Real.exp (-r))
    {κ : Type*} {φ : κ → EuclideanSpace ℂ (ι → Fin d)} (hφ : Orthonormal ℂ φ)
    (s : Finset κ)
    (hkeep : ∀ j ∈ s,
      toEuclideanLin (coordinateSliceProjection z ℓ hN a ψ J r) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  let b := coordinateSliceOperator z ℓ hN a
  let K : ℝ := 2 * Fintype.card ι * J
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hK : 0 < K := by dsimp [K]; positivity
  have hr1 : 1 ≤ r := by
    have hx := (hierarchyProjectionLength_ge_square (finiteHierarchyDepth N) K Δ).trans hr
    have hh : (2 : ℝ) ≤ finiteHierarchyDepth N := by
      exact_mod_cast two_le_finiteHierarchyDepth N
    nlinarith [sq_nonneg ((finiteHierarchyDepth N : ℝ) - 1)]
  have hbudget : K ≤ K * r := by nlinarith
  have happrox' : ‖H - ∑ j, b j‖ ≤ (N : ℝ) * K * Real.exp (-r) := by
    rw [sum_coordinateSliceOperator]
    refine happrox.trans ?_
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    dsimp [K]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (N : ℝ) - 1)
      (mul_nonneg (mul_nonneg hcard.le hJ.le) (Real.exp_pos (-r)).le)]
  exact card_le_two_mul_re_trace_of_periodicHierarchyProjection_of_finite
    (fun i ↦ coordinateSlice ℓ (z i)) b (le_two_pow_finiteHierarchyDepth N)
    (coordinateSliceOperator_mem_supportedOperators z hℓ hN a hsupp)
    (isHermitian_coordinateSliceOperator z ℓ hN a ha) hψ hK
    (two_le_finiteHierarchyDepth N) hK hΔ hr hbudget hP₀ hgap hE₀ happrox' hφ s hkeep

omit [DecidableEq ι] in
/-- If there are no more coarse slices than physical sites, the complete slice construction
has an explicit cubic logarithmic projection length. This holds for full coordinate boxes
with an occupied site in each slice. Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem hierarchyProjectionLength_coordinateSlices_le [Nonempty ι]
    (hcount : N ≤ Fintype.card ι) {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    hierarchyProjectionLength (finiteHierarchyDepth N) (2 * Fintype.card ι * J) Δ ≤
      512 * ((Nat.clog 2 (Fintype.card ι) : ℝ) + 2) ^ 3 *
        (1 + max 0 (Real.log (2 * J / Δ))) := by
  have hdepth : finiteHierarchyDepth N ≤ finiteHierarchyDepth (Fintype.card ι) :=
    max_le_max le_rfl (Nat.clog_mono_right 2 hcount)
  have hmono : hierarchyProjectionLength (finiteHierarchyDepth N) (2 * Fintype.card ι * J) Δ ≤
      hierarchyProjectionLength (finiteHierarchyDepth (Fintype.card ι))
        (2 * Fintype.card ι * J) Δ := by
    unfold hierarchyProjectionLength
    gcongr
  have h := hierarchyProjectionLength_finiteHierarchyDepth_mul_le
    (N := Fintype.card ι) (by exact Fintype.card_pos) (by norm_num : (0 : ℝ) < 2) hJ hΔ
  rw [show (Fintype.card ι : ℝ) * 2 * J = 2 * Fintype.card ι * J by ring] at h
  exact hmono.trans h

end TNLean.MPS.AreaLaw.LocalSolution
