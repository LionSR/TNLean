/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Norm compression for two orthogonal projections

This file proves the elementary Hilbert-space passage from a Friedrichs overlap
bound for two subspaces to a norm estimate for the product of their orthogonal
projections. The common intersection is removed before the overlap bound is
applied.
-/

open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The Friedrichs overlap of \(U\) and \(V\), after removing their common
intersection, is at most \(\eta\).

This is the two-subspace overlap quantity used in the principal-angle argument
of arXiv:2011.12127 §IV.C, eq:4:martingale-2, and in the Kastoryano–Lucia 2018
principal-angle estimate. Its application to MPS ground spaces is discussed in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
def IsFriedrichsBound (U V : Submodule ℂ E) (η : ℝ) : Prop :=
  ∀ x : E, x ∈ U → x ∈ (U ⊓ V)ᗮ →
    ∀ y : E, y ∈ V → y ∈ (U ⊓ V)ᗮ →
      ‖⟪x, y⟫_ℂ‖ ≤ η * ‖x‖ * ‖y‖

/-- A Friedrichs overlap bound controls the orthogonal projection of a vector
in one reduced subspace onto the other reduced subspace.

Here the reduced parts of \(U\) and \(V\) are their intersections with
\((U \cap V)^\perp\). This is the two-subspace geometric estimate underlying
the principal-angle argument in arXiv:2011.12127 §IV.C,
eq:4:martingale-2. The later MPS-specific input is the Kastoryano–Lucia 2018
principal-angle estimate. The precise comparison is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem norm_starProjection_le_of_friedrichs_bound
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η)
    (hAngle : IsFriedrichsBound U V η)
    {v : E} (hvV : v ∈ V) (hvInter : v ∈ (U ⊓ V)ᗮ) :
    ‖U.starProjection v‖ ≤ η * ‖v‖ := by
  let x := U.starProjection v
  change ‖x‖ ≤ η * ‖v‖
  have hxU : x ∈ U := U.starProjection_apply_mem v
  have hxInter : x ∈ (U ⊓ V)ᗮ := by
    rw [Submodule.mem_orthogonal'] at hvInter ⊢
    intro z hz
    calc
      ⟪x, z⟫_ℂ = ⟪v, U.starProjection z⟫_ℂ :=
        U.inner_starProjection_left_eq_right v z
      _ = ⟪v, z⟫_ℂ := by rw [U.starProjection_eq_self_iff.mpr hz.1]
      _ = 0 := hvInter z hz
  have hInner := hAngle x hxU hxInter v hvV hvInter
  have hInnerEq : ⟪x, v⟫_ℂ = ⟪x, x⟫_ℂ := by
    calc
      ⟪x, v⟫_ℂ = ⟪U.starProjection x, v⟫_ℂ := by
        rw [U.starProjection_eq_self_iff.mpr hxU]
      _ = ⟪x, U.starProjection v⟫_ℂ :=
        U.inner_starProjection_left_eq_right x v
      _ = ⟪x, x⟫_ℂ := rfl
  rw [hInnerEq, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x)] at hInner
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact mul_nonneg hη (norm_nonneg v)
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith [hInner]

/-- A Friedrichs overlap bound controls the product of the two orthogonal
projections on the orthogonal complement of their common range.

This is the generic two-projection norm-compression lemma associated with
arXiv:2011.12127 §IV.C, eq:4:martingale-2. The MPS-specific input needed later
is the Kastoryano–Lucia 2018 principal-angle estimate; its source boundary is
recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem norm_starProjection_starProjection_le_of_friedrichs_bound
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η)
    (hAngle : IsFriedrichsBound U V η)
    {v : E} (hvInter : v ∈ (U ⊓ V)ᗮ) :
    ‖U.starProjection (V.starProjection v)‖ ≤
      η * ‖V.starProjection v‖ := by
  apply norm_starProjection_le_of_friedrichs_bound U V hη hAngle
  · exact V.starProjection_apply_mem v
  · rw [Submodule.mem_orthogonal'] at hvInter ⊢
    intro z hz
    calc
      ⟪V.starProjection v, z⟫_ℂ = ⟪v, V.starProjection z⟫_ℂ :=
        V.inner_starProjection_left_eq_right v z
      _ = ⟪v, z⟫_ℂ := by rw [V.starProjection_eq_self_iff.mpr hz.2]
      _ = 0 := hvInter z hz

/-- On the reduced range of the first projection, a Friedrichs overlap bound
gives the directional compression estimate
\(\|P_U(P_Vv)\|\leq\eta\|P_Uv\|\).

The restriction to the range of \(P_U\) is essential: without it, this
directional inequality would force \(P_V\) to preserve \(\ker P_U\), which does
not follow from a subspace-angle bound. This is the restricted geometric form
relevant to arXiv:2011.12127 §IV.C, eq:4:martingale-2; the remaining
Kastoryano–Lucia 2018 principal-angle estimate for MPS ground spaces is
described in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem norm_starProjection_starProjection_le_of_friedrichs_bound_of_mem
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η)
    (hAngle : IsFriedrichsBound U V η)
    {v : E} (hvU : v ∈ U) (hvInter : v ∈ (U ⊓ V)ᗮ) :
    ‖U.starProjection (V.starProjection v)‖ ≤
      η * ‖U.starProjection v‖ := by
  calc
    ‖U.starProjection (V.starProjection v)‖ ≤
        η * ‖V.starProjection v‖ :=
      norm_starProjection_starProjection_le_of_friedrichs_bound
        U V hη hAngle hvInter
    _ ≤ η * ‖v‖ :=
      mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le v) hη
    _ = η * ‖U.starProjection v‖ := by
      rw [U.norm_starProjection_apply hvU]

/-- For projections onto \(K^\perp\) and \(L^\perp\), a Friedrichs bound on
these kernel complements gives directional compression on the reduced range of
the first projection.

This is the form in which the generic geometry can be applied to local
excitation projections. The source is arXiv:2011.12127 §IV.C,
eq:4:martingale-2; the MPS-specific input is the Kastoryano–Lucia 2018
principal-angle estimate, whose comparison is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem norm_starProjection_orthogonal_comp_le_of_friedrichs_bound
    (K L : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η)
    (hAngle : IsFriedrichsBound Kᗮ Lᗮ η)
    {v : E} (hvK : v ∈ Kᗮ) (hvInter : v ∈ (Kᗮ ⊓ Lᗮ)ᗮ) :
    ‖Kᗮ.starProjection (Lᗮ.starProjection v)‖ ≤
      η * ‖Kᗮ.starProjection v‖ :=
  norm_starProjection_starProjection_le_of_friedrichs_bound_of_mem
    Kᗮ Lᗮ hη hAngle hvK hvInter

end Submodule
