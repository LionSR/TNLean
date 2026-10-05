/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveHamiltonian

/-!
# Passing from the active endpoint block to the actual open chain

The actual endpoint Hamiltonian reduces the explicitly constructed active
subspace. On its orthogonal complement the derived inner-sector penalty
gives energy at least one half. A gap of the actual compressed block
therefore gives the minimum of that gap and one half for the full open
Hamiltonian. This is the final sector-gluing step; its active-block input
still has to be supplied by the boundary-normalization comparison.

Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped InnerProductSpace ComplexOrder

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- A gap of the actual compressed endpoint block transfers to the full
actual open-chain Hamiltonian. The inactive energy bound and exact kernel
transport are derived, rather than supplied as hypotheses. -/
theorem mixedEndpoint_open_norm_gap_of_active_norm_gap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ N))ᗮ,
      δ * ‖x‖ ≤ ‖mixedEndpointActiveHamiltonian A₀ A₁ N x‖) :
    ∀ v ∈ (LinearMap.ker (openInteractionHamiltonianES
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1)))ᗮ,
      min δ (1 / 2) * ‖v‖ ≤ ‖openInteractionHamiltonianES
        (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1) v‖ := by
  let H := openInteractionHamiltonianES
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (N + 1 + 1)
  let K := mixedEndpointActiveHamiltonian A₀ A₁ N
  let U := mixedEndpointActiveLinearIsometry D₀ D₁ N
  let Q := mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)
  have hH : H.IsPositive := by
    apply LinearMap.nonneg_iff_isPositive.mp
    exact Finset.sum_nonneg fun i _ => LinearMap.nonneg_iff_isPositive.mpr
      (periodicLocalInteractionES_isPositive
        (mixedEndpointParentInteraction_isPositive A₀ A₁ 0) i.1)
  have hK : K.IsPositive := mixedEndpointActiveHamiltonian_isPositive A₀ A₁ N
  have hleft (x : mixedEndpointActiveSpace D₀ D₁ N) : U.toLinearMap.adjoint (U x) = x :=
    LinearMap.congr_fun mixedEndpointActiveLinearIsometry_adjoint_comp x
  have hright (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1))) :
      U (U.toLinearMap.adjoint v) = Q v :=
    LinearMap.congr_fun mixedEndpointActiveLinearIsometry_comp_adjoint v
  have hintertwine (x : mixedEndpointActiveSpace D₀ D₁ N) : U (K x) = H (U x) :=
    mixedEndpointActiveHamiltonian_intertwines A₀ A₁ N x
  intro v hv
  let x := U.toLinearMap.adjoint v
  let y := v - U x
  have hsum : U x + y = v := by dsimp [y]; abel
  have hadj : U.toLinearMap.adjoint y = 0 := by
    change U.toLinearMap.adjoint (v - U x) = 0
    rw [map_sub, hleft]
    exact sub_self x
  have horth (z : mixedEndpointActiveSpace D₀ D₁ N) : ⟪U z, y⟫_ℂ = 0 := by
    calc
      ⟪U z, y⟫_ℂ = ⟪z, U.toLinearMap.adjoint y⟫_ℂ :=
        (LinearMap.adjoint_inner_right U.toLinearMap z y).symm
      _ = 0 := by rw [hadj, inner_zero_right]
  have hx : x ∈ (LinearMap.ker K)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    change ⟪z, U.toLinearMap.adjoint v⟫_ℂ = 0
    rw [LinearMap.adjoint_inner_right]
    apply Submodule.inner_right_of_mem_orthogonal _ hv
    change H (U z) = 0
    rw [← hintertwine, LinearMap.mem_ker.mp hz, map_zero]
  have hactive := hK.re_inner_ge_of_norm_gap hδ hGap x hx
  have hQy : Q y = 0 := by rw [← hright, hadj, map_zero]
  have hinactive := mixedEndpointOpen_inactive_energy_lower_bound A₀ A₁ (by omega) y hQy
  have hcross : ⟪H y, U x⟫_ℂ = 0 := by
    rw [hH.isSymmetric, ← hintertwine]
    exact inner_eq_zero_symm.mpr (horth (K x))
  have henergy : (⟪H v, v⟫_ℂ).re =
      (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
    calc
      _ = (⟪H (U x + y), U x + y⟫_ℂ).re := by rw [hsum]
      _ = (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
        rw [map_add, inner_add_left, inner_add_right, inner_add_right,
          ← hintertwine, U.inner_map_map, horth, hcross]
        simp
  have hnorm : ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    calc
      _ = ‖U x + y‖ ^ 2 := by rw [hsum]
      _ = ‖U x‖ ^ 2 + ‖y‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth x)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [U.norm_map]
  have hquadratic : min δ (1 / 2) * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
    rw [hnorm, henergy, mul_add]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hactive
    · have hi : (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ (⟪H y, y⟫_ℂ).re := by
        calc
          _ ≤ (⟪y, H y⟫_ℂ).re := hinactive
          _ = _ := inner_re_symm (𝕜 := ℂ) y (H y)
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans hi
  have hbound := hquadratic.trans (re_inner_le_norm (𝕜 := ℂ) (H v) v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact le_of_mul_le_mul_right
      (by simpa only [pow_two, mul_assoc] using hbound) (norm_pos_iff.mpr hv0)

end
end MPOSymmetry
end MPSTensor
