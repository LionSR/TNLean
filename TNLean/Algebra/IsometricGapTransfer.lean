/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PositiveGapTransfer

/-!
# Kernel and gap transport along an isometric inclusion

An operator intertwining an isometric inclusion restricts to the original
operator on the included space. A strictly positive quadratic-form bound on
the orthogonal complement rules out additional kernel vectors. For symmetric
operators the two sectors are orthogonal also for the energy, so their lower
bounds combine by taking the minimum.

The results do not assume pairwise commutation of the local terms of either
operator. They support physical embeddings of parent Hamiltonians, as in
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`.
-/

open scoped InnerProductSpace

namespace LinearIsometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A strict quadratic-form bound off an isometric inclusion excludes any
additional kernel vectors. Intertwining suffices; neither symmetry nor
positivity on the included space is needed. -/
theorem ker_eq_map_of_intertwines_of_inactive_bound (U : E →ₗᵢ[ℂ] F)
    {H : F →ₗ[ℂ] F} {K : E →ₗ[ℂ] E}
    (hintertwine : ∀ x, H (U x) = U (K x)) {c : ℝ} (hc : 0 < c)
    (hInactive : ∀ y, U.toLinearMap.adjoint y = 0 →
      c * ‖y‖ ^ 2 ≤ (⟪H y, y⟫_ℂ).re) :
    LinearMap.ker H = (LinearMap.ker K).map U.toLinearMap := by
  have hleft (x : E) : U.toLinearMap.adjoint (U x) = x :=
    LinearMap.congr_fun U.adjoint_comp_self' x
  ext v
  constructor
  · intro hv
    let x := U.toLinearMap.adjoint v
    let y := v - U x
    have hadj : U.toLinearMap.adjoint y = 0 := by
      change U.toLinearMap.adjoint (v - U x) = 0
      rw [map_sub, hleft]
      exact sub_self x
    have horth (z : E) : ⟪U z, y⟫_ℂ = 0 := by
      calc
        ⟪U z, y⟫_ℂ = ⟪z, U.toLinearMap.adjoint y⟫_ℂ :=
          (LinearMap.adjoint_inner_right U.toLinearMap z y).symm
        _ = 0 := by rw [hadj, inner_zero_right]
    have henergy : (⟪H y, y⟫_ℂ).re = 0 := by
      change (⟪H (v - U x), y⟫_ℂ).re = 0
      rw [map_sub, LinearMap.mem_ker.mp hv, hintertwine,
        inner_sub_left, inner_zero_left, horth]
      simp
    have hbound := hInactive y hadj
    rw [henergy] at hbound
    have hnormSq : ‖y‖ ^ 2 ≤ 0 :=
      le_of_mul_le_mul_left (by simpa using hbound) hc
    have hy : y = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hnormSq (sq_nonneg _)))
    have hvx : U x = v := (sub_eq_zero.mp hy).symm
    refine ⟨x, ?_, hvx⟩
    apply LinearMap.mem_ker.mpr
    apply U.injective
    rw [map_zero, ← hintertwine, hvx]
    exact LinearMap.mem_ker.mp hv
  · rintro ⟨x, hx, rfl⟩
    change H (U x) = 0
    rw [hintertwine, LinearMap.mem_ker.mp hx, map_zero]

/-- Quadratic-form bounds on an invariant isometric image and its orthogonal
complement combine with the minimum constant. No sign restriction on the
constants or positivity hypothesis is needed. -/
theorem re_inner_ge_of_intertwines (U : E →ₗᵢ[ℂ] F)
    {H : F →ₗ[ℂ] F} {K : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hintertwine : ∀ x, H (U x) = U (K x)) {δ c : ℝ}
    (hGap : ∀ x ∈ (LinearMap.ker K)ᗮ,
      δ * ‖x‖ ^ 2 ≤ (⟪K x, x⟫_ℂ).re)
    (hInactive : ∀ y, U.toLinearMap.adjoint y = 0 →
      c * ‖y‖ ^ 2 ≤ (⟪H y, y⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ,
      min δ c * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
  have hleft (x : E) : U.toLinearMap.adjoint (U x) = x :=
    LinearMap.congr_fun U.adjoint_comp_self' x
  intro v hv
  let x := U.toLinearMap.adjoint v
  let y := v - U x
  have hsum : U x + y = v := by
    dsimp [y]
    rw [add_comm, sub_add_cancel]
  have hadj : U.toLinearMap.adjoint y = 0 := by
    change U.toLinearMap.adjoint (v - U x) = 0
    rw [map_sub, hleft]
    exact sub_self x
  have horth (z : E) : ⟪U z, y⟫_ℂ = 0 := by
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
    rw [hintertwine, LinearMap.mem_ker.mp hz, map_zero]
  have hcross : ⟪H y, U x⟫_ℂ = 0 := by
    rw [hH, hintertwine]
    exact inner_eq_zero_symm.mpr (horth (K x))
  have henergy : (⟪H v, v⟫_ℂ).re =
      (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
    calc
      _ = (⟪H (U x + y), U x + y⟫_ℂ).re := by rw [hsum]
      _ = (⟪K x, x⟫_ℂ).re + (⟪H y, y⟫_ℂ).re := by
        rw [map_add, inner_add_left, inner_add_right, inner_add_right,
          hintertwine, U.inner_map_map, horth, hcross]
        simp
  have hnorm : ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    calc
      _ = ‖U x + y‖ ^ 2 := by rw [hsum]
      _ = ‖U x‖ ^ 2 + ‖y‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth x)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [U.norm_map]
  rw [hnorm, henergy, mul_add]
  exact add_le_add
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hGap x hx))
    ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (hInactive y hadj))

/-- A norm gap of a positive operator transfers through an isometric
intertwiner when the orthogonal complement has a quadratic-form bound. The
resulting gap is the minimum of the original gap and the complementary bound. -/
theorem norm_gap_of_intertwines (U : E →ₗᵢ[ℂ] F)
    {H : F →ₗ[ℂ] F} {K : E →ₗ[ℂ] E} (hH : H.IsPositive) (hK : K.IsPositive)
    (hintertwine : ∀ x, H (U x) = U (K x)) {δ c : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker K)ᗮ, δ * ‖x‖ ≤ ‖K x‖)
    (hInactive : ∀ y, U.toLinearMap.adjoint y = 0 →
      c * ‖y‖ ^ 2 ≤ (⟪H y, y⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, min δ c * ‖v‖ ≤ ‖H v‖ := by
  intro v hv
  have hquadratic := U.re_inner_ge_of_intertwines hH.isSymmetric hintertwine
    (hK.re_inner_ge_of_norm_gap hδ hGap) hInactive v hv
  have hbound := hquadratic.trans (re_inner_le_norm (𝕜 := ℂ) (H v) v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact le_of_mul_le_mul_right
      (by simpa only [pow_two, mul_assoc] using hbound) (norm_pos_iff.mpr hv0)

end LinearIsometry
