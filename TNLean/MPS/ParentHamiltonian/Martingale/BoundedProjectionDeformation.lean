/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.BoundedCongruenceGap
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import QICLean.Analysis.WeightedPositiveKernel

/-!
# Deforming a finite family of projection constraints

For symmetric projections \(P_i\) and an invertible map \(e\), let \(Q_i\)
be the orthogonal projection onto \((e^{-1}(\ker P_i))^\perp\).
If \(\lVert ev\rVert\le B\lVert v\rVert\) and
\(\lVert e^{-1}w\rVert\le C\lVert w\rVert\), then
\[
 C^{-2}\sum_i Q_i\le e^*(\sum_iP_i)e\le B^2\sum_iQ_i.
\]
Consequently a gap \(\delta\) of \(\sum_iP_i\) gives a gap
\(\delta/(B^2C^2)\) of \(\sum_iQ_i\). These constants do not depend on
the number of summands or the dimensions of the spaces.

All deformed constraints are defined by their pulled-back kernels. Applying
this result to a chain requires proving that these are the actual local
constraints and that the two norm bounds are uniform in the chain length.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

namespace LinearEquiv

/-- The canonical projection constraint whose kernel is the inverse image
of \(\ker P\) under \(e\). -/
noncomputable def deformedConstraintProjection (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    E →ₗ[ℂ] E :=
  ((LinearMap.ker P).comap e.toLinearMap)ᗮ.starProjection.toLinearMap

/-- Deformed constraints are symmetric projections. -/
theorem deformedConstraintProjection_isSymmetricProjection
    (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    (e.deformedConstraintProjection P).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

/-- The deformed projection has exactly the pulled-back kernel. -/
theorem ker_deformedConstraintProjection (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    LinearMap.ker (e.deformedConstraintProjection P) =
      (LinearMap.ker P).comap e.toLinearMap := by
  simp only [deformedConstraintProjection, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- Congruence distributes over the finite constraint sum. -/
theorem adjoint_congruence_sum {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F) :
    e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap =
      ∑ i, e.toLinearMap.adjoint ∘ₗ P i ∘ₗ e.toLinearMap := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-- The sum of the deformed constraints has the pulled-back kernel of the
original positive constraint sum. -/
theorem ker_sum_deformedConstraintProjection {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, e.deformedConstraintProjection (P i)) =
      (LinearMap.ker (∑ i, P i)).comap e.toLinearMap := by
  rw [WeightedPositiveKernel.ker_sum_eq_iInf
    (fun i => (e.deformedConstraintProjection_isSymmetricProjection (P i)).isPositive),
    WeightedPositiveKernel.ker_sum_eq_iInf hP, Submodule.comap_iInf]
  simp only [ker_deformedConstraintProjection]

end LinearEquiv

private theorem symmetricProjection_eq_orthogonal_ker_projection
    {P : F →ₗ[ℂ] F} (hP : P.IsSymmetricProjection) :
    P = (LinearMap.ker P)ᗮ.starProjection.toLinearMap := by
  have hrange : LinearMap.range P = (LinearMap.ker P)ᗮ := by
    rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  obtain ⟨_, h⟩ := P.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  simpa only [hrange] using h

namespace LinearMap.IsSymmetricProjection

/-- A single deformed constraint and the congruence of its original
projection bound one another with constants determined only by \(B,C\). -/
theorem deformedConstraintProjection_comparison
    {P : F →ₗ[ℂ] F} (hP : P.IsSymmetricProjection) (e : E ≃ₗ[ℂ] F)
    {B C : ℝ} (_hB : 0 < B) (hC : 0 < C)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖) :
    ((1 / C ^ 2 : ℝ) : ℂ) • e.deformedConstraintProjection P ≤
        e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap ∧
      e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap ≤
        ((B ^ 2 : ℝ) : ℂ) • e.deformedConstraintProjection P := by
  let G := e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap
  have hG : G.IsPositive := hP.isPositive.adjoint_conj e.toLinearMap
  have hPproj := symmetricProjection_eq_orthogonal_ker_projection hP
  have hcontract (w : F) : ‖P w‖ ≤ ‖w‖ := by
    rw [hPproj]
    exact Submodule.norm_starProjection_apply_le _ _
  have hunitGap : ∀ w ∈ (LinearMap.ker P)ᗮ, (1 : ℝ) * ‖w‖ ≤ ‖P w‖ := by
    intro w hw
    have hfix : P w = w := by
      rw [hPproj]
      exact Submodule.starProjection_eq_self_iff.mpr hw
    simp [hfix]
  have hGproj : (LinearMap.ker G)ᗮ.starProjection.toLinearMap =
      e.deformedConstraintProjection P := by
    rw [show LinearMap.ker G = (LinearMap.ker P).comap e.toLinearMap from
      e.ker_adjoint_congruence P]
    rfl
  constructor
  · have hgap := hP.isPositive.norm_gap_adjoint_congruence_of_inverse_bound
      e (by norm_num : (0 : ℝ) ≤ 1) hC hInverse hunitGap
    simpa only [hGproj] using
      hG.smul_orthogonal_ker_projection_le_of_norm_gap
        (show 0 ≤ (1 : ℝ) / C ^ 2 by positivity) hgap
  · have hbound (w : E) : (⟪G w, w⟫_ℂ).re ≤ B ^ 2 * ‖w‖ ^ 2 := by
      change (⟪e.toLinearMap.adjoint (P (e w)), w⟫_ℂ).re ≤ _
      rw [LinearMap.adjoint_inner_left]
      calc
        _ ≤ ‖P (e w)‖ * ‖e w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
        _ ≤ ‖e w‖ * ‖e w‖ :=
          mul_le_mul_of_nonneg_right (hcontract (e w)) (norm_nonneg _)
        _ ≤ B ^ 2 * ‖w‖ ^ 2 := by
          simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            mul_self_le_mul_self (norm_nonneg (e w)) (hForward w)
    rw [← hGproj]
    refine ⟨((LinearMap.ker G)ᗮ.starProjection_isSymmetric.smul (by simp)).sub
      hG.isSymmetric, ?_⟩
    intro v
    have hproj : G ((LinearMap.ker G).starProjection v) = 0 :=
      LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
    have henergy : ⟪G v, v⟫_ℂ =
        ⟪G ((LinearMap.ker G)ᗮ.starProjection v),
          (LinearMap.ker G)ᗮ.starProjection v⟫_ℂ := by
      simp only [Submodule.starProjection_orthogonal_val, map_sub,
        hG.isSymmetric v, hproj, sub_zero]
    have hnorm : (⟪(LinearMap.ker G)ᗮ.starProjection v, v⟫_ℂ).re =
        ‖(LinearMap.ker G)ᗮ.starProjection v‖ ^ 2 :=
      Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ) _ _
    change 0 ≤ (⟪((B ^ 2 : ℝ) : ℂ) • (LinearMap.ker G)ᗮ.starProjection v - G v,
      v⟫_ℂ).re
    simpa only [inner_sub_left, inner_smul_left, Complex.sub_re,
      Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hnorm, henergy, sub_nonneg] using
      hbound ((LinearMap.ker G)ᗮ.starProjection v)

end LinearMap.IsSymmetricProjection

namespace LinearEquiv

/-- Two-sided comparison of the actual finite sums, with constants
independent of the number of constraints. -/
theorem sum_deformedConstraintProjection_comparison {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖) :
    ((1 / C ^ 2 : ℝ) : ℂ) • (∑ i, e.deformedConstraintProjection (P i)) ≤
        e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap ∧
      e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap ≤
        ((B ^ 2 : ℝ) : ℂ) • (∑ i, e.deformedConstraintProjection (P i)) := by
  have h := fun i => (hP i).deformedConstraintProjection_comparison
    e hB hC hForward hInverse
  rw [e.adjoint_congruence_sum P]
  constructor
  · simpa only [Finset.smul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).1)
  · simpa only [Finset.smul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).2)

/-- A uniform forward bound and inverse bound transfer a gap of the
original projection sum to the canonical deformed constraint sum, with
explicit ratio \(\delta/(B^2C^2)\). -/
theorem norm_gap_sum_deformedConstraintProjection {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    {B C δ : ℝ} (hB : 0 < B) (hC : 0 < C) (hδ : 0 < δ)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ w ∈ (LinearMap.ker (∑ i, P i))ᗮ,
      δ * ‖w‖ ≤ ‖(∑ i, P i) w‖) :
    ∀ v ∈ (LinearMap.ker (∑ i, e.deformedConstraintProjection (P i)))ᗮ,
      (δ / (B ^ 2 * C ^ 2)) * ‖v‖ ≤
        ‖(∑ i, e.deformedConstraintProjection (P i)) v‖ := by
  let G := e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap
  let S := ∑ i, e.deformedConstraintProjection (P i)
  have hsum : (∑ i, P i).IsPositive :=
    LinearMap.isPositive_sum Finset.univ fun i _ => (hP i).isPositive
  have hG : G.IsPositive := hsum.adjoint_conj e.toLinearMap
  have hGGap := hsum.norm_gap_adjoint_congruence_of_inverse_bound
    e hδ.le hC hInverse hGap
  have hBS : ((B ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hB.ne'
  have hker : LinearMap.ker G = LinearMap.ker (((B ^ 2 : ℝ) : ℂ) • S) := by
    rw [LinearMap.ker_smul _ _ hBS]
    exact (e.ker_adjoint_congruence (∑ i, P i)).trans
      (e.ker_sum_deformedConstraintProjection P (fun i => (hP i).isPositive)).symm
  have hUpper : G ≤ ((B ^ 2 : ℝ) : ℂ) • S :=
    (e.sum_deformedConstraintProjection_comparison P hP hB hC hForward hInverse).2
  have hTransfer := hG.norm_gap_of_le_of_ker_eq
    (by positivity : 0 ≤ δ / C ^ 2) hUpper hker hGGap
  intro v hv
  have hv' : v ∈ (LinearMap.ker (((B ^ 2 : ℝ) : ℂ) • S))ᗮ := by
    simpa only [LinearMap.ker_smul _ _ hBS] using hv
  have h := hTransfer v hv'
  have hratio : δ / (B ^ 2 * C ^ 2) = (δ / C ^ 2) / B ^ 2 := by
    rw [div_div, mul_comm (C ^ 2)]
  rw [hratio, div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
  simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg B), mul_comm (B ^ 2)] using h

end LinearEquiv
