/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.CoordinateSliceApproximation

/-!
# Coordinate slices on finite rectangular boxes

Every positive side length of a full box is at most its number of sites. Choosing that
many coarse slices covers the box and satisfies the physical-size hypothesis of the cubic
logarithmic length estimate. Coordinate maximum-metric locality implies the coordinate
strip locality used in the construction.

This proves the geometry of the coordinate-slice option in arbitrary dimension for full
rectangular boxes. Source: Hastings, arXiv:cond-mat/0508554v3, lines 745–756.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- A side of a nonempty rectangular box has no more elements than the whole box.
Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem coordinateSide_le_card_box {D : ℕ} (L : Fin D → ℕ) (hL : ∀ k, 0 < L k)
    (axis : Fin D) : L axis ≤ Fintype.card (∀ k, Fin (L k)) := by
  let origin : ∀ k, Fin (L k) := fun k ↦ ⟨0, hL k⟩
  let f : Fin (L axis) → (∀ k, Fin (L k)) := fun a ↦ Function.update origin axis a
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrFun hab axis
    simpa only [f, Function.update_self] using h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The physical box is covered when its side length is used as the coarse slice count. -/
theorem coordinateBox_slice_extent {D : ℕ} (L : Fin D → ℕ) (axis : Fin D)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (v : ∀ k, Fin (L k)) :
    (v axis : ℕ) < L axis * (2 * ℓ) :=
  (v axis).isLt.trans_le (Nat.le_mul_of_pos_right _ (by omega))

/-- Maximum-metric balls in a finite rectangular box lie in the corresponding coordinate
strip. No separately supplied coordinate-Lipschitz hypothesis is needed.
Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem coordinateBox_ball_subset_strip {D : ℕ} (L : Fin D → ℕ) (axis : Fin D) (ℓ : ℕ)
    (i : ∀ k, Fin (L k)) :
    {v : (∀ k, Fin (L k)) | dist (fun k ↦ (v k : ℕ)) (fun k ↦ (i k : ℕ)) ≤ ℓ} ⊆
      {v | Nat.dist (v axis) (i axis) ≤ ℓ} := by
  intro v hv
  exact natDist_coordinate_le_of_dist_le (fun w : Fin D → ℕ ↦ w)
    (fun _ _ ↦ le_rfl) axis hv

/-- Full boxes in every dimension satisfy the cubic logarithmic projection-length bound.
The local norm and residual estimates enter only through their scalar coupling bound.
Hastings, arXiv:cond-mat/0508554v3, lines 745–756. -/
theorem hierarchyProjectionLength_coordinateBox_le {D : ℕ} (L : Fin D → ℕ)
    (hL : ∀ k, 0 < L k) (axis : Fin D) {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    hierarchyProjectionLength (finiteHierarchyDepth (L axis))
        (2 * Fintype.card (∀ k, Fin (L k)) * J) Δ ≤
      512 * ((Nat.clog 2 (Fintype.card (∀ k, Fin (L k))) : ℝ) + 2) ^ 3 *
        (1 + max 0 (Real.log (2 * J / Δ))) := by
  let : Nonempty (∀ k, Fin (L k)) := ⟨fun k ↦ ⟨0, hL k⟩⟩
  exact hierarchyProjectionLength_coordinateSlices_le (coordinateSide_le_card_box L hL axis) hJ hΔ

/-- Maximum-metric local terms on a full rectangular box construct a nearby unit vector
retained at every node of the coordinate-slice hierarchy. All coordinate-support and
coverage conditions are derived from the box itself.
Hastings, arXiv:cond-mat/0508554v3, lines 633–639, 705–743 and 745–756. -/
theorem exists_unit_mem_coordinateSliceProjection_of_box {D d : ℕ}
    (L : Fin D → ℕ) (hL : ∀ k, 0 < L k) (axis : Fin D)
    {ℓ : ℕ} (hℓ : 0 < ℓ)
    (a : (∀ k, Fin (L k)) →
      Matrix ((∀ k, Fin (L k)) → Fin d) ((∀ k, Fin (L k)) → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d
      {v | dist (fun k ↦ (v k : ℕ)) (fun k ↦ (i k : ℕ)) ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian)
    {ψ : EuclideanSpace ℂ ((∀ k, Fin (L k)) → Fin d)} (hψ : ‖ψ‖ = 1)
    {J Δ r : ℝ} (hJ : 0 < J)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth (L axis))
      (2 * Fintype.card (∀ k, Fin (L k)) * J) Δ ≤ r)
    (hres : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ J * Real.exp (-r))
    (hbound : ∀ i, ‖a i‖ ≤ J) :
    let z := fun v : (∀ k, Fin (L k)) ↦ (v axis : ℕ)
    let b := coordinateSliceOperator z ℓ (hL axis) a
    let h := finiteHierarchyDepth (L axis)
    let K := 2 * Fintype.card (∀ k, Fin (L k)) * J
    ∃ φ : EuclideanSpace ℂ ((∀ k, Fin (L k)) → Fin d), ‖φ‖ = 1 ∧
      toEuclideanLin (coordinateSliceProjection z ℓ (hL axis) a ψ J r) φ = φ ∧
      ‖φ - ψ‖ ≤ 2 * (((3 : ℝ) ^ (h + 1) - 1) * Real.exp (-r / 8)) ∧
      IsRetainedHierarchy
        (hierarchyProjection (hierarchyEdge (extendFiniteEdges b))
          (fun m k ↦ (⟪ψ, toEuclideanLin (hierarchyEdge (extendFiniteEdges b) m k) ψ⟫_ℂ).re)
          (hierarchyWindowRadius K r h)) h 0 φ ∧
      ∀ i, coordinateSlice ℓ (z i) < L axis := by
  let : Nonempty (∀ k, Fin (L k)) := ⟨fun k ↦ ⟨0, hL k⟩⟩
  have hsupp' : ∀ i, a i ∈ supportedOperators d
      {v : (∀ k, Fin (L k)) | Nat.dist (v axis) (i axis) ≤ ℓ} := by
    intro i
    exact supportedOperators_mono (d := d) (ι := ∀ k, Fin (L k))
      (coordinateBox_ball_subset_strip L axis ℓ i) (hsupp i)
  exact exists_unit_mem_coordinateSliceProjection (ι := ∀ k, Fin (L k)) (d := d)
    (fun v ↦ (v axis : ℕ)) hℓ (hL axis) (coordinateBox_slice_extent L axis hℓ) a hsupp'
    ha hψ hJ hr hres hbound

/-- The physical gap counts the states in the actual coordinate-slice projection on a
full rectangular box, starting only from physical local terms and their approximation.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730 and 745–756. -/
theorem card_le_two_mul_re_trace_of_coordinateSliceProjection_of_box {D d : ℕ}
    (L : Fin D → ℕ) (hL : ∀ k, 0 < L k) (axis : Fin D)
    {ℓ : ℕ} (hℓ : 0 < ℓ)
    (a : (∀ k, Fin (L k)) →
      Matrix ((∀ k, Fin (L k)) → Fin d) ((∀ k, Fin (L k)) → Fin d) ℂ)
    (hsupp : ∀ i, a i ∈ supportedOperators d
      {v | dist (fun k ↦ (v k : ℕ)) (fun k ↦ (i k : ℕ)) ≤ ℓ})
    (ha : ∀ i, (a i).IsHermitian)
    {ψ : EuclideanSpace ℂ ((∀ k, Fin (L k)) → Fin d)} (hψ : ‖ψ‖ = 1)
    {J Δ r : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hr : hierarchyProjectionLength (finiteHierarchyDepth (L axis))
      (2 * Fintype.card (∀ k, Fin (L k)) * J) Δ ≤ r)
    {H P₀ : Matrix ((∀ k, Fin (L k)) → Fin d) ((∀ k, Fin (L k)) → Fin d) ℂ}
    (hP₀ : IsStarProjection P₀) {E₀ : ℝ}
    (hgap : ∀ v : EuclideanSpace ℂ ((∀ k, Fin (L k)) → Fin d),
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P₀ v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    (hE₀ : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = E₀)
    (happrox : ‖H - ∑ i, a i‖ ≤ Fintype.card (∀ k, Fin (L k)) * J * Real.exp (-r))
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ((∀ k, Fin (L k)) → Fin d)}
    (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (hkeep : ∀ j ∈ s, toEuclideanLin
      (coordinateSliceProjection (fun v : (∀ k, Fin (L k)) ↦ (v axis : ℕ))
        ℓ (hL axis) a ψ J r) (φ j) = φ j) :
    (s.card : ℝ) ≤ 2 * (trace P₀).re := by
  let : Nonempty (∀ k, Fin (L k)) := ⟨fun k ↦ ⟨0, hL k⟩⟩
  have hsupp' : ∀ i, a i ∈ supportedOperators d
      {v : (∀ k, Fin (L k)) | Nat.dist (v axis) (i axis) ≤ ℓ} := by
    intro i
    exact supportedOperators_mono (d := d) (ι := ∀ k, Fin (L k))
      (coordinateBox_ball_subset_strip L axis ℓ i) (hsupp i)
  exact card_le_two_mul_re_trace_of_coordinateSliceProjection (ι := ∀ k, Fin (L k)) (d := d)
    (fun v ↦ (v axis : ℕ)) hℓ (hL axis) a hsupp'
    ha hψ hJ hΔ hr hP₀ hgap hE₀ happrox hφ s hkeep

end TNLean.MPS.AreaLaw.LocalSolution
