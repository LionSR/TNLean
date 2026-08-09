/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Norm compression for two orthogonal projections

This file proves elementary Hilbert-space consequences of a Friedrichs overlap
bound for two subspaces. Besides norm estimates for products of orthogonal projections,
it gives the source anticommutator lower bound for the complementary excitation
projections. The common ground-space intersection is removed before the overlap bound is
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

private theorem starProjection_mem_orthogonal_of_le
    (U W : Submodule ℂ E) (hWU : W ≤ U) {v : E} (hvW : v ∈ Wᗮ) :
    U.starProjection v ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal'] at hvW ⊢
  intro z hz
  calc
    ⟪U.starProjection v, z⟫_ℂ = ⟪v, U.starProjection z⟫_ℂ :=
      U.inner_starProjection_left_eq_right v z
    _ = ⟪v, z⟫_ℂ := by rw [U.starProjection_eq_self_iff.mpr (hWU hz)]
    _ = 0 := hvW z hz

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
  have hxInter : x ∈ (U ⊓ V)ᗮ :=
    starProjection_mem_orthogonal_of_le U (U ⊓ V) inf_le_left hvInter
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
  · exact starProjection_mem_orthogonal_of_le V (U ⊓ V) inf_le_right hvInter

private theorem friedrichs_anticommutator_reduced
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ 1)
    (hAngle : IsFriedrichsBound U V η)
    {v : E} (hvInter : v ∈ (U ⊓ V)ᗮ) :
    -η * (RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ)) ≤
      RCLike.re (⟪Uᗮ.starProjection v, Vᗮ.starProjection v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, Uᗮ.starProjection v⟫_ℂ) := by
  let x := U.starProjection v
  let y := V.starProjection v
  let a := Uᗮ.starProjection v
  let b := Vᗮ.starProjection v
  have hxU : x ∈ U := U.starProjection_apply_mem v
  have hyV : y ∈ V := V.starProjection_apply_mem v
  have hxInter : x ∈ (U ⊓ V)ᗮ :=
    starProjection_mem_orthogonal_of_le U (U ⊓ V) inf_le_left hvInter
  have hyInter : y ∈ (U ⊓ V)ᗮ :=
    starProjection_mem_orthogonal_of_le V (U ⊓ V) inf_le_right hvInter
  have hxyNorm : ‖⟪x, y⟫_ℂ‖ ≤ η * ‖x‖ * ‖y‖ :=
    hAngle x hxU hxInter y hyV hyInter
  have hxyRe : RCLike.re (⟪x, y⟫_ℂ) ≤ η * ‖x‖ * ‖y‖ :=
    (RCLike.re_le_norm _).trans hxyNorm
  have hsumNorm : ‖x + y‖ ^ 2 ≤
      (1 + η) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    rw [norm_add_sq (𝕜 := ℂ)]
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hxv : RCLike.re (⟪x, v⟫_ℂ) = ‖x‖ ^ 2 := by
    change RCLike.re (⟪U.starProjection v, v⟫_ℂ) = ‖U.starProjection v‖ ^ 2
    exact U.re_inner_starProjection_eq_normSq v
  have hyv : RCLike.re (⟪y, v⟫_ℂ) = ‖y‖ ^ 2 := by
    change RCLike.re (⟪V.starProjection v, v⟫_ℂ) = ‖V.starProjection v‖ ^ 2
    exact V.re_inner_starProjection_eq_normSq v
  have hsumInner : RCLike.re (⟪x + y, v⟫_ℂ) = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [inner_add_left, map_add, hxv, hyv]
  have hinnerNorm : ‖x‖ ^ 2 + ‖y‖ ^ 2 ≤ ‖x + y‖ * ‖v‖ := by
    rw [← hsumInner]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm (x + y) v)
  have hsumProj : ‖x‖ ^ 2 + ‖y‖ ^ 2 ≤ (1 + η) * ‖v‖ ^ 2 := by
    let S := ‖x‖ ^ 2 + ‖y‖ ^ 2
    have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hηone : 0 ≤ 1 + η := by linarith
    by_cases hS0 : S = 0
    · rw [show ‖x‖ ^ 2 + ‖y‖ ^ 2 = 0 from hS0]
      exact mul_nonneg hηone (sq_nonneg _)
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      have hsq : S ^ 2 ≤ ‖x + y‖ ^ 2 * ‖v‖ ^ 2 := by
        dsimp [S]
        nlinarith
      dsimp [S] at hSpos ⊢
      nlinarith
  have hav : RCLike.re (⟪a, v⟫_ℂ) = ‖a‖ ^ 2 := by
    change RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) = ‖Uᗮ.starProjection v‖ ^ 2
    exact Uᗮ.re_inner_starProjection_eq_normSq v
  have hbv : RCLike.re (⟪b, v⟫_ℂ) = ‖b‖ ^ 2 := by
    change RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ) = ‖Vᗮ.starProjection v‖ ^ 2
    exact Vᗮ.re_inner_starProjection_eq_normSq v
  have hpythU := U.norm_sq_eq_add_norm_sq_starProjection v
  have hpythV := V.norm_sq_eq_add_norm_sq_starProjection v
  change ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖a‖ ^ 2 at hpythU
  change ‖v‖ ^ 2 = ‖y‖ ^ 2 + ‖b‖ ^ 2 at hpythV
  have hdiagLower :
      (1 - η) * ‖v‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [hsumProj]
  let e := a + b
  have hev : RCLike.re (⟪e, v⟫_ℂ) = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    dsimp [e]
    rw [inner_add_left]
    change RCLike.re (⟪a, v⟫_ℂ) + RCLike.re (⟪b, v⟫_ℂ) = _
    rw [hav, hbv]
  have hinnerE : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖e‖ * ‖v‖ := by
    rw [← hev]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm e v)
  have heSq : (1 - η) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖e‖ ^ 2 := by
    have hc : 0 ≤ 1 - η := sub_nonneg.mpr hηle
    have hQ : 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hvNorm : 0 ≤ ‖v‖ := norm_nonneg _
    by_cases hv0 : ‖v‖ = 0
    · have hv : v = 0 := norm_eq_zero.mp hv0
      subst v
      simp [a, b, e]
    · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne hvNorm (Ne.symm hv0)
      have hQsq : (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 ≤ ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
        nlinarith
      have hcQ := mul_le_mul_of_nonneg_left hdiagLower hQ
      have hmul :
          ((1 - η) * (‖a‖ ^ 2 + ‖b‖ ^ 2)) * ‖v‖ ^ 2 ≤
            ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
        nlinarith
      exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hvpos)).mp hmul
  have hconj : RCLike.re (⟪b, a⟫_ℂ) = RCLike.re (⟪a, b⟫_ℂ) := by
    rw [← inner_conj_symm a b, RCLike.conj_re]
  rw [show RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) = ‖a‖ ^ 2 from hav,
    show RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ) = ‖b‖ ^ 2 from hbv]
  change -η * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
    RCLike.re (⟪a, b⟫_ℂ) + RCLike.re (⟪b, a⟫_ℂ)
  rw [hconj]
  have heExpand : ‖e‖ ^ 2 = ‖a‖ ^ 2 + 2 * RCLike.re (⟪a, b⟫_ℂ) + ‖b‖ ^ 2 := by
    exact norm_add_sq a b
  nlinarith [heSq]

private theorem friedrichs_anticommutator_of_le_one
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ 1)
    (hAngle : IsFriedrichsBound U V η) (v : E) :
    -η * (RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ)) ≤
      RCLike.re (⟪Uᗮ.starProjection v, Vᗮ.starProjection v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, Uᗮ.starProjection v⟫_ℂ) := by
  let W := U ⊓ V
  let p := W.starProjection v
  let z := v - p
  have hzInter : z ∈ Wᗮ := W.sub_starProjection_mem_orthogonal v
  have hpU : p ∈ U := by
    exact (W.starProjection_apply_mem v).1
  have hpV : p ∈ V := by
    exact (W.starProjection_apply_mem v).2
  have hUzero : Uᗮ.starProjection p = 0 := by
    rw [Uᗮ.starProjection_apply_eq_zero_iff]
    exact U.le_orthogonal_orthogonal hpU
  have hVzero : Vᗮ.starProjection p = 0 := by
    rw [Vᗮ.starProjection_apply_eq_zero_iff]
    exact V.le_orthogonal_orthogonal hpV
  have hUz : Uᗮ.starProjection z = Uᗮ.starProjection v := by
    simp [z, map_sub, hUzero]
  have hVz : Vᗮ.starProjection z = Vᗮ.starProjection v := by
    simp [z, map_sub, hVzero]
  have hUdiag : RCLike.re (⟪Uᗮ.starProjection z, z⟫_ℂ) =
      RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) := by
    rw [Uᗮ.re_inner_starProjection_eq_normSq,
      Uᗮ.re_inner_starProjection_eq_normSq]
    change ‖Uᗮ.starProjection z‖ ^ 2 = ‖Uᗮ.starProjection v‖ ^ 2
    rw [hUz]
  have hVdiag : RCLike.re (⟪Vᗮ.starProjection z, z⟫_ℂ) =
      RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ) := by
    rw [Vᗮ.re_inner_starProjection_eq_normSq,
      Vᗮ.re_inner_starProjection_eq_normSq]
    change ‖Vᗮ.starProjection z‖ ^ 2 = ‖Vᗮ.starProjection v‖ ^ 2
    rw [hVz]
  have h :=
    friedrichs_anticommutator_reduced U V hη hηle hAngle hzInter
  rw [hUdiag, hVdiag, hUz, hVz] at h
  exact h

/-- A Friedrichs bound for two ground-space ranges gives the anticommutator lower bound
for their complementary excitation projections.

Let `U` and `V` be the ranges of the ground-space projections `qᵢ` and `qⱼ`. Then
`Uᗮ.starProjection` and `Vᗮ.starProjection` are the complementary excitation projections
`hᵢ = 1 - qᵢ` and `hⱼ = 1 - qⱼ`. If the Friedrichs overlap of `U` and `V`, with their
common intersection removed, is at most `η`, then
`hᵢhⱼ + hⱼhᵢ ≥ -η(hᵢ + hⱼ)` as a quadratic-form inequality.

This is the generic two-projection bridge from the ground-space principal-angle estimate to
arXiv:2011.12127, Section IV.C, `eq:4:martingale-2` (lines 2176--2182). It does not assert the
false all-vector norm compression bound for the excitation product. The MPS-specific task is only
to supply the uniform ground-space Friedrichs bound in the chosen blocking convention, as recorded
in `docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem re_inner_anticommutator_starProjection_orthogonal_ge_neg_of_friedrichs_bound
    (U V : Submodule ℂ E) {η : ℝ} (hη : 0 ≤ η)
    (hAngle : IsFriedrichsBound U V η) (v : E) :
    -η * (RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ)) ≤
      RCLike.re (⟪Uᗮ.starProjection v, Vᗮ.starProjection v⟫_ℂ) +
      RCLike.re (⟪Vᗮ.starProjection v, Uᗮ.starProjection v⟫_ℂ) := by
  by_cases hηle : η ≤ 1
  · exact friedrichs_anticommutator_of_le_one U V hη hηle hAngle v
  · have hOne : IsFriedrichsBound U V 1 := by
      intro x _ _ y _ _
      simpa using norm_inner_le_norm x y
    have h :=
      friedrichs_anticommutator_of_le_one U V (η := 1) zero_le_one le_rfl hOne v
    have hdiag : 0 ≤ RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
        RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ) :=
      add_nonneg (Uᗮ.re_inner_starProjection_nonneg v)
        (Vᗮ.re_inner_starProjection_nonneg v)
    calc
      -η * (RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
          RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ)) ≤
          -1 * (RCLike.re (⟪Uᗮ.starProjection v, v⟫_ℂ) +
            RCLike.re (⟪Vᗮ.starProjection v, v⟫_ℂ)) := by
        exact mul_le_mul_of_nonneg_right (neg_le_neg_iff.mpr (le_of_not_ge hηle)) hdiag
      _ ≤ _ := h

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
