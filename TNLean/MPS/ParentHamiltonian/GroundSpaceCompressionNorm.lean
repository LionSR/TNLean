/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.InjectiveRangeProjector
import Mathlib.Topology.Order.Basic

/-!
# Norm estimates for compression to an injective range

Let \(T\) be an injective map with finite-dimensional Hilbert domain,
let \(K=(T^\dagger T)^{-1}\), and let \(P=TKT^\dagger\) be its range projection.
For every bounded operator \(X\) on the codomain,
\[
  \|PXP\|\leq\|K\|\,\|T^\dagger X T\|.
\]
The same bound holds for the defects \(PXP-cP\) and
\(T^\dagger XT-cT^\dagger T\). These are Hilbert-space estimates; no
transfer-operator convergence or spectral-gap assertion is assumed.
-/

open Filter
open scoped Topology InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Compression to the range of an injective map is controlled by the inverse Gram operator
and the pullback of the compressed operator. -/
theorem norm_starProjection_comp_le_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) (X : F →L[𝕜] F) :
    ‖T.range.starProjection.comp (X.comp T.range.starProjection)‖ ≤
      ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp T)‖ := by
  rw [← injectiveRangeProjector_eq_starProjection T hT]
  change ‖(T.comp (inverseGram T hT)).comp
    ((T.adjoint.comp (X.comp T)).comp ((inverseGram T hT).comp T.adjoint))‖ ≤ _
  refine le_trans (opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)) ?_
  rw [norm_T_comp_inverseGram_eq_sqrt, norm_inverseGram_comp_adjoint_eq_sqrt,
    ← mul_assoc, mul_right_comm (Real.sqrt ‖inverseGram T hT‖),
    Real.mul_self_sqrt (norm_nonneg _)]

/-- The defect of scalar compression is controlled by the corresponding defect of the pulled
back operator relative to the Gram operator. -/
theorem norm_starProjection_comp_sub_smul_le_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) (X : F →L[𝕜] F) (c : 𝕜) :
    ‖T.range.starProjection.comp (X.comp T.range.starProjection) -
        c • T.range.starProjection‖ ≤
      ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp T) - c • (T.adjoint.comp T)‖ := by
  have h := norm_starProjection_comp_le_inverseGram T hT (X - c • ContinuousLinearMap.id 𝕜 F)
  simpa only [sub_comp, comp_sub, smul_comp, comp_smul, id_comp,
    Submodule.starProjection_comp_starProjection_of_le le_rfl] using h

/-- Eventual injectivity and a bound for the inverse Gram operators transfer
convergence of scalar pullback defects to convergence of the compressed operators.
The Hilbert spaces may vary with the index, and the filter is arbitrary. -/
theorem tendsto_starProjection_comp_sub_smul_zero_of_inverseGram_bound
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i)
    (X : (i : ι) → F i →L[𝕜] F i) (c : ι → 𝕜) {C : ℝ}
    (hBound : ∀ᶠ i in l, ∃ hT : Function.Injective (T i),
      ‖inverseGram (T i) hT‖ ≤ C)
    (hDefect : Tendsto (fun i =>
      ‖(T i).adjoint.comp ((X i).comp (T i)) -
        c i • ((T i).adjoint.comp (T i))‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖(T i).range.starProjection.comp ((X i).comp (T i).range.starProjection) -
        c i • (T i).range.starProjection‖) l (𝓝 0) := by
  have hUpper : Tendsto (fun i => C *
      ‖(T i).adjoint.comp ((X i).comp (T i)) -
        c i • ((T i).adjoint.comp (T i))‖) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hDefect
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hBound] with i hi
  obtain ⟨hT, hi⟩ := hi
  exact (norm_starProjection_comp_sub_smul_le_inverseGram (T i) hT (X i) (c i)).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _))

omit [CompleteSpace E] in
/-- Compression controls the action of an observable on a unit ground vector. -/
theorem norm_starProjection_apply_sub_smul_le_compression
    (G : Submodule 𝕜 E) (X : E →L[𝕜] E) (c : 𝕜)
    (v : E) (hv : v ∈ G) (hUnit : ‖v‖ = 1) :
    ‖G.starProjection (X v) - c • v‖ ≤
      ‖G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection‖ := by
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, G.starProjection_eq_self_iff.mpr hv, hUnit, mul_one] using
      (G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection).le_opNorm v

omit [CompleteSpace E] in
/-- Scalar compression bounds the deviation of the expectation on a unit vector. -/
theorem norm_inner_sub_scalar_le_compression
    (G : Submodule 𝕜 E) (X : E →L[𝕜] E) (c : 𝕜)
    (v : E) (hv : v ∈ G) (hUnit : ‖v‖ = 1) :
    ‖⟪v, X v⟫_𝕜 - c‖ ≤
      ‖G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection‖ := by
  have hInner : ⟪v, G.starProjection (X v) - c • v⟫_𝕜 = ⟪v, X v⟫_𝕜 - c := by
    simp only [inner_sub_right, inner_smul_right,
      ← G.inner_starProjection_left_eq_right, G.starProjection_eq_self_iff.mpr hv,
      inner_self_eq_norm_sq_to_K, hUnit, RCLike.ofReal_one, one_pow, mul_one]
  have hBound : ‖⟪v, X v⟫_𝕜 - c‖ ≤ ‖G.starProjection (X v) - c • v‖ := by
    simpa only [hInner, hUnit, one_mul] using
      norm_inner_le_norm (𝕜 := 𝕜) v (G.starProjection (X v) - c • v)
  exact hBound.trans (norm_starProjection_apply_sub_smul_le_compression G X c v hv hUnit)

end ContinuousLinearMap
