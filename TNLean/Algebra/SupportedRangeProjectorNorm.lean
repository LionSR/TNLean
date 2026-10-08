/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SupportedRangeProjector
import Mathlib.Topology.Order.Basic

/-!
# Norm estimates for supported range-projector cancellation

Suppose the difference of two overlapping range projections and their common
range projection has the supported factorization
\(P_TP_L-P_C=T H_T R H_L L^\dagger\).
Its norm is at most
\(\|T\|\|H_T\|\|H_L\|\|L\|\|R\|\).
Thus uniformly bounded boundary and supported inverse norms transfer a
vanishing mixed Gram residual to a vanishing projection difference. The
spaces may vary with the index, and the filter is arbitrary.

The exact factorization is supplied explicitly here; it follows from the
supported Gram inverse equations in `SupportedRangeProjector`. This module
proves only the norm implication and does not assume injectivity of the
boundary maps. The residual decay and inverse bounds for a particular tensor
remain separate hypotheses.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531. These operator norm consequences are reconstructed for
that projector comparison.
-/

open scoped InnerProductSpace
namespace ContinuousLinearMap
variable {𝕜 E F G W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] [CompleteSpace W]
omit [CompleteSpace E] [CompleteSpace W] in
/-- An exact supported factorization bounds the range-projector difference
by the two boundary norms, the two supported inverse norms, and the mixed
residual norm. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. -/
theorem norm_starProjection_comp_sub_le_of_supported_factorization
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : W →L[𝕜] F)
    (HT : E →L[𝕜] E) (HL : G →L[𝕜] G) (R : G →L[𝕜] E)
    (hFactor : T.range.starProjection.comp L.range.starProjection - C.range.starProjection =
      T.comp (HT.comp (R.comp (HL.comp L.adjoint)))) :
    ‖T.range.starProjection.comp L.range.starProjection - C.range.starProjection‖ ≤
      (‖T‖ * ‖HT‖ * ‖HL‖ * ‖L‖) * ‖R‖ := by
  rw [hFactor]
  calc
    ‖T.comp (HT.comp (R.comp (HL.comp L.adjoint)))‖ ≤
        ‖T‖ * ‖HT.comp (R.comp (HL.comp L.adjoint))‖ := opNorm_comp_le _ _
    _ ≤ ‖T‖ * (‖HT‖ * (‖R‖ * (‖HL‖ * ‖L.adjoint‖))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      refine (opNorm_comp_le HT (R.comp (HL.comp L.adjoint))).trans ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg HT)
      refine (opNorm_comp_le R (HL.comp L.adjoint)).trans ?_
      exact mul_le_mul_of_nonneg_left (opNorm_comp_le HL L.adjoint) (norm_nonneg R)
    _ = _ := by rw [adjoint.norm_map]; ring

/-- Uniformly bounded boundary and supported inverse norms turn vanishing
mixed residuals into vanishing range-projector differences. The Hilbert
spaces may vary, and the filter is arbitrary. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem tendsto_norm_starProjection_comp_sub_zero_of_supported_factorizations
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E G W F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
    [∀ i, FiniteDimensional 𝕜 (G i)] [∀ i, CompleteSpace (G i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
    [∀ i, FiniteDimensional 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i) (L : (i : ι) → G i →L[𝕜] F i)
    (C : (i : ι) → W i →L[𝕜] F i)
    (HT : (i : ι) → E i →L[𝕜] E i) (HL : (i : ι) → G i →L[𝕜] G i)
    (R : (i : ι) → G i →L[𝕜] E i) {K : ℝ}
    (hFactor : ∀ᶠ i in l,
      (T i).range.starProjection.comp (L i).range.starProjection -
        (C i).range.starProjection =
      (T i).comp ((HT i).comp ((R i).comp ((HL i).comp (L i).adjoint))))
    (hBound : ∀ᶠ i in l, ‖T i‖ * ‖HT i‖ * ‖HL i‖ * ‖L i‖ ≤ K)
    (hResidual : Filter.Tendsto (fun i => ‖R i‖) l (nhds 0)) :
    Filter.Tendsto (fun i =>
      ‖(T i).range.starProjection.comp (L i).range.starProjection -
        (C i).range.starProjection‖) l (nhds 0) := by
  have hUpper : Filter.Tendsto (fun i => K * ‖R i‖) l (nhds 0) := by
    simpa only [mul_zero] using hResidual.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hFactor, hBound] with i hiFactor hiBound
  exact (norm_starProjection_comp_sub_le_of_supported_factorization
    (T i) (L i) (C i) (HT i) (HL i) (R i) hiFactor).trans
    (mul_le_mul_of_nonneg_right hiBound (norm_nonneg _))
end ContinuousLinearMap
