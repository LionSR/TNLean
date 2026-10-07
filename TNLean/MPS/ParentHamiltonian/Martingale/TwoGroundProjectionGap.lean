/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TwoProjectionCompression
import QICLean.Analysis.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion

/-!
# A sharp comparison from two ground projections

Let two interval ground spaces contain the ground space of an open chain.
If the product of their orthogonal projections differs from the full ground
projection by at most \(c<1\), then their complementary projections have
sum bounded below by \(1-c\) on the full ground-space complement. An energy
comparison with coefficient \(\kappa\) therefore gives a gap
\(\kappa(1-c)\).

This is an auxiliary consequence of the three-interval ground-projection
estimate in Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma
`commutation` (ii). The proof uses the Friedrichs-angle anticommutator
inequality for the complementary projections. In contrast to a triangle
inequality, this comparison retains the limiting coefficient as the
projection defect tends to zero.
-/

open scoped InnerProductSpace ComplexOrder

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem intersection_eq_of_strict_defect
    (U V W : Submodule ℂ E) {c : ℝ} (hc : c < 1)
    (hWU : W ≤ U) (hWV : W ≤ V)
    (hDefect : ‖W.starProjection - U.starProjection.comp V.starProjection‖ ≤ c) :
    W = U ⊓ V := by
  refine le_antisymm (le_inf hWU hWV) ?_
  intro v hv
  let z := v - W.starProjection v
  have hzU : z ∈ U := U.sub_mem hv.1 (hWU (W.starProjection_apply_mem v))
  have hzV : z ∈ V := V.sub_mem hv.2 (hWV (W.starProjection_apply_mem v))
  have hzW : z ∈ Wᗮ := W.sub_starProjection_mem_orthogonal v
  have hNorm : ‖z‖ ≤ c * ‖z‖ := by
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      W.starProjection_apply_eq_zero_iff.mpr hzW,
      V.starProjection_eq_self_iff.mpr hzV, U.starProjection_eq_self_iff.mpr hzU,
      zero_sub, norm_neg] using ContinuousLinearMap.le_of_opNorm_le
        (W.starProjection - U.starProjection.comp V.starProjection) hDefect z
  have hz : z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg z])
  exact W.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

private theorem sum_excitation_ker (U V : Submodule ℂ E) :
    LinearMap.ker (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) = U ⊓ V := by
  simpa [Submodule.ker_starProjection, Fintype.sum_bool, iInf_bool_eq, inf_comm] using
    (WeightedPositiveKernel.ker_sum_eq_iInf (P := fun b : Bool =>
      if b then Uᗮ.starProjection.toLinearMap else Vᗮ.starProjection.toLinearMap)
      (by intro b; cases b <;> exact (Submodule.isSymmetricProjection_starProjection _).isPositive))

private theorem sum_excitation_gap (U V : Submodule ℂ E) {c : ℝ} (hc : c < 1)
    (hDefect : ‖U.starProjection.comp V.starProjection - (U ⊓ V).starProjection‖ ≤ c) :
    ∀ v ∈ (U ⊓ V)ᗮ, (1 - c) * ‖v‖ ≤
      ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖ := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hDefect
  have hAngle := Submodule.isFriedrichsBound_of_norm_starProjection_comp_sub_inf_starProjection_le
    U V hDefect
  have hPositive := (Submodule.isSymmetricProjection_starProjection Uᗮ).isPositive.add
    (Submodule.isSymmetricProjection_starProjection Vᗮ).isPositive
  suffices hGap : ∀ v ∈ (LinearMap.ker
      (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap))ᗮ,
      (1 - c) * ‖v‖ ≤ ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖
    by simpa only [sum_excitation_ker] using hGap
  apply FrustrationFree.spectralGap_of_martingale_of_finiteDimensional (sub_pos.mpr hc)
    hPositive
  intro v
  have hAnti :=
    Submodule.re_inner_anticommutator_starProjection_orthogonal_ge_neg_of_friedrichs_bound
      U V hc0 hAngle v
  simp only [LinearMap.add_apply, ContinuousLinearMap.coe_coe, inner_add_left,
    inner_add_right, RCLike.re_eq_complex_re, Complex.add_re] at hAnti ⊢
  have hDiag (S : Submodule ℂ E) : (⟪S.starProjection v, S.starProjection v⟫_ℂ).re =
      (⟪S.starProjection v, v⟫_ℂ).re := by
    rw [← S.inner_starProjection_left_eq_right, S.starProjection_eq_self_iff.mpr
      (S.starProjection_apply_mem v)]
  nlinarith [hDiag Uᗮ, hDiag Vᗮ]

/-- If two ground spaces contain \(\ker H\), their projection defect is
at most \(c<1\), and \(H\) dominates \(\kappa\) times the sum of their
excitation projections, then \(H\) has norm gap \(\kappa(1-c)\).

This is the sharp two-interval comparison used with Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma `commutation` (ii). The strict
projection-defect bound also forces the two ground spaces to intersect
exactly in \(\ker H\). -/
theorem norm_gap_of_two_ground_projection_bounds (H : E →ₗ[ℂ] E) (U V : Submodule ℂ E)
    {κ c : ℝ} (hκ : 0 ≤ κ) (hc : c < 1)
    (hWU : LinearMap.ker H ≤ U) (hWV : LinearMap.ker H ≤ V)
    (hLower : (κ : ℂ) • (Uᗮ.starProjection.toLinearMap +
      Vᗮ.starProjection.toLinearMap) ≤ H)
    (hDefect : ‖(LinearMap.ker H).starProjection -
      U.starProjection.comp V.starProjection‖ ≤ c) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, (κ * (1 - c)) * ‖v‖ ≤ ‖H v‖ := by
  have hInter := intersection_eq_of_strict_defect U V (LinearMap.ker H) hc hWU hWV hDefect
  have hSumPos := (Submodule.isSymmetricProjection_starProjection Uᗮ).isPositive.add
    (Submodule.isSymmetricProjection_starProjection Vᗮ).isPositive
  have hAngleDefect : ‖U.starProjection.comp V.starProjection -
      (U ⊓ V).starProjection‖ ≤ c := by simpa only [hInter, norm_sub_rev] using hDefect
  have hSumGap : ∀ v ∈ (LinearMap.ker
      (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap))ᗮ,
      (1 - c) * ‖v‖ ≤ ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖ :=
    by simpa only [sum_excitation_ker] using sum_excitation_gap U V hc hAngleDefect
  intro v hv
  have hEnergy := hSumPos.re_inner_ge_of_norm_gap (sub_nonneg.mpr hc.le) hSumGap v
    (by simpa only [sum_excitation_ker, ← hInter] using hv)
  have hComparison : κ * (⟪(Uᗮ.starProjection.toLinearMap +
      Vᗮ.starProjection.toLinearMap) v, v⟫_ℂ).re ≤ (⟪H v, v⟫_ℂ).re := by
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_left,
      inner_smul_left, RCLike.re_eq_complex_re, Complex.conj_ofReal,
      Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using
      hLower.re_inner_nonneg_left v
  have hQuadratic : (κ * (1 - c)) * ‖v‖ ^ 2 ≤ ‖H v‖ * ‖v‖ :=
    by simpa only [mul_assoc] using ((mul_le_mul_of_nonneg_left hEnergy hκ).trans
      hComparison).trans (re_inner_le_norm (𝕜 := ℂ) (H v) v)
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp
      (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hQuadratic)

end FrustrationFree

