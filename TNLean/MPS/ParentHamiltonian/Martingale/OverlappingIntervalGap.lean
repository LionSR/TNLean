/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison

/-!
# Combining gaps on overlapping open intervals

A long prefix and a terminal interval cover an open chain. A bound on the
product of their ground projections, after subtracting the full-chain ground
projection, combines their spectral gaps. This permits an interval of arbitrary
length to be treated using a prefix whose length is divisible by a chosen
grouping length.

The ground-projection estimate is the three-interval estimate of Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma `commutation` (ii). The elementary
two-projection inequality below supplies the step from divisible lengths to
arbitrary lengths.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

private theorem norm_sq_le_eight_projection_errors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U V W : Submodule ℂ E)
    (hDefect : ‖W.starProjection - U.starProjection.comp V.starProjection‖ ≤ (1 / 2 : ℝ))
    (v : E) (hv : v ∈ Wᗮ) :
    ‖v‖ ^ 2 ≤ 8 * (‖Uᗮ.starProjection v‖ ^ 2 + ‖Vᗮ.starProjection v‖ ^ 2) := by
  have hsmall := ContinuousLinearMap.le_of_opNorm_le
    (W.starProjection - U.starProjection.comp V.starProjection) hDefect v
  have hproduct : ‖U.starProjection (V.starProjection v)‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      W.starProjection_apply_eq_zero_iff.mpr hv, zero_sub, norm_neg] using hsmall
  have hdecomp : v = U.starProjection (V.starProjection v) +
      U.starProjection (Vᗮ.starProjection v) + Uᗮ.starProjection v := by
    simp only [Submodule.starProjection_orthogonal_val, map_sub]
    abel
  have hnorm : ‖v‖ ≤ (1 / 2 : ℝ) * ‖v‖ +
      ‖Vᗮ.starProjection v‖ + ‖Uᗮ.starProjection v‖ := calc
    ‖v‖ = ‖U.starProjection (V.starProjection v) +
        U.starProjection (Vᗮ.starProjection v) + Uᗮ.starProjection v‖ := congrArg norm hdecomp
    _ ≤ ‖U.starProjection (V.starProjection v)‖ +
        ‖U.starProjection (Vᗮ.starProjection v)‖ + ‖Uᗮ.starProjection v‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add
      (add_le_add hproduct (U.norm_starProjection_apply_le _)) le_rfl
  have hlinear : ‖v‖ ≤ 2 * (‖Uᗮ.starProjection v‖ + ‖Vᗮ.starProjection v‖) := by
    linarith
  have hsquare := mul_self_le_mul_self (norm_nonneg v) hlinear
  nlinarith [sq_nonneg (‖Uᗮ.starProjection v‖ - ‖Vᗮ.starProjection v‖)]

private theorem norm_gap_of_two_ground_projection_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (H G F : E →ₗ[ℂ] E) (U V : Submodule ℂ E)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hLeft : (κ : ℂ) • Uᗮ.starProjection.toLinearMap ≤ G)
    (hRight : (κ : ℂ) • Vᗮ.starProjection.toLinearMap ≤ F)
    (hCover : G + F ≤ (2 : ℂ) • H)
    (hDefect : ‖(LinearMap.ker H).starProjection -
      U.starProjection.comp V.starProjection‖ ≤ (1 / 2 : ℝ)) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, (κ / 16) * ‖v‖ ≤ ‖H v‖ := by
  intro v hv
  have horder := (add_le_add hLeft hRight).trans hCover
  have hproj (S : Submodule ℂ E) :
      (⟪S.starProjection v, v⟫_ℂ).re = ‖S.starProjection v‖ ^ 2 :=
    S.re_inner_starProjection_eq_normSq v
  have henergy : κ * (‖Uᗮ.starProjection v‖ ^ 2 + ‖Vᗮ.starProjection v‖ ^ 2) ≤
      2 * (⟪H v, v⟫_ℂ).re := by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, inner_sub_left, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, map_ofNat, RCLike.re_eq_complex_re,
      Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_ofNat,
      zero_mul, sub_zero, hproj, sub_nonneg, mul_add] using
      horder.re_inner_nonneg_left v
  have hprojection := mul_le_mul_of_nonneg_left
    (norm_sq_le_eight_projection_errors U V (LinearMap.ker H) hDefect v hv) hκ
  have hquadratic : (κ / 16) * ‖v‖ ^ 2 ≤ ‖H v‖ * ‖v‖ := by
    nlinarith [show (⟪H v, v⟫_ℂ).re ≤ ‖H v‖ * ‖v‖ from
      re_inner_le_norm (𝕜 := ℂ) (H v) v]
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp
      (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hquadratic)

namespace MPSTensor

variable {d D : ℕ}

/-- A prefix contains only interaction terms of the full open chain. -/
theorem openPrefixParentHamiltonianES_le_openParentHamiltonianES
    (A : MPSTensor d D) (R N n : ℕ) :
    openPrefixParentHamiltonianES A R N n ≤ openParentHamiltonianES A R N := by
  classical
  rw [openPrefixParentHamiltonianES, openParentHamiltonianES]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun i : NonwrappingStart R N => i.1.val + R ≤ n)
    (fun _ => by simp) (fun i => localTermES A R i.1)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A R i.1))

/-- An interval Hamiltonian contains only interaction terms of the full open chain. -/
theorem openSuffixParentHamiltonianES_le_openParentHamiltonianES
    (A : MPSTensor d D) (R W N n : ℕ) :
    openSuffixParentHamiltonianES A R W N n ≤ openParentHamiltonianES A R N := by
  classical
  rw [openSuffixParentHamiltonianES, openParentHamiltonianES]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A R i.1))

/-- Gaps for a prefix and a terminal interval give a full-chain gap if the
product of their ground projections differs from the full-chain ground
projection by at most \(1/2\). The two interval energies sum to at most twice
the full-chain energy, so a common interval gap \(\kappa\) gives a gap
\(\kappa/16\). This is an auxiliary two-interval consequence of the projector
estimate in Nachtergaele, arXiv:cond-mat/9410110, Section 6,
Lemma `commutation` (ii). -/
theorem openParentHamiltonianES_norm_gap_of_overlapping_interval_gaps
    (A : MPSTensor d D) (R N n W : ℕ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLeft : ∀ v ∈ (LinearMap.ker (openPrefixParentHamiltonianES A R N n))ᗮ,
      κ * ‖v‖ ≤ ‖openPrefixParentHamiltonianES A R N n v‖)
    (hRight : ∀ v ∈ (LinearMap.ker (openSuffixParentHamiltonianES A R W N N))ᗮ,
      κ * ‖v‖ ≤ ‖openSuffixParentHamiltonianES A R W N N v‖)
    (hDefect : ‖(LinearMap.ker (openParentHamiltonianES A R N)).starProjection -
      (LinearMap.ker (openPrefixParentHamiltonianES A R N n)).starProjection.comp
        (LinearMap.ker (openSuffixParentHamiltonianES A R W N N)).starProjection‖ ≤
      (1 / 2 : ℝ)) :
    ∀ v ∈ (LinearMap.ker (openParentHamiltonianES A R N))ᗮ,
      (κ / 16) * ‖v‖ ≤ ‖openParentHamiltonianES A R N v‖ := by
  exact norm_gap_of_two_ground_projection_bounds
    (openParentHamiltonianES A R N)
    (openPrefixParentHamiltonianES A R N n)
    (openSuffixParentHamiltonianES A R W N N) _ _ hκ
    (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap
      (openPrefixParentHamiltonianES_isPositive A R N n) hκ hLeft)
    (LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_norm_gap
      (openSuffixParentHamiltonianES_isPositive A R W N N) hκ hRight)
    (by simpa only [two_smul] using (add_le_add
      (openPrefixParentHamiltonianES_le_openParentHamiltonianES A R N n)
      (openSuffixParentHamiltonianES_le_openParentHamiltonianES A R W N N))) hDefect

end MPSTensor
