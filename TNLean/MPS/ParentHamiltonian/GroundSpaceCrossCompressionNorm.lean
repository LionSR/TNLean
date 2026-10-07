/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.InjectiveRangeProjector
import Mathlib.Topology.Order.Basic

/-!
# Compression between two injective ranges

For injective maps \(T\) and \(S\) from finite-dimensional Hilbert spaces to a
common Hilbert space, their range projections satisfy
\(\|P_T X P_S\|\leq\|(T^\dagger T)^{-1}\|^{1/2}
\|T^\dagger X S\|\|(S^\dagger S)^{-1}\|^{1/2}\).
Thus a vanishing rectangular pullback gives vanishing cross compression
whenever the inverse Gram norms remain bounded. These are Hilbert-space
estimates with explicit hypotheses; they make no assertion of mixed-transfer
decay for a particular tensor family.
-/

open Filter
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E G F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The compression between two injective ranges is controlled by their inverse
Gram operators and the rectangular pullback of the observable. -/
theorem norm_starProjection_comp_starProjection_le_inverseGram
    (T : E →L[𝕜] F) (S : G →L[𝕜] F)
    (hT : Function.Injective T) (hS : Function.Injective S) (X : F →L[𝕜] F) :
    ‖T.range.starProjection.comp (X.comp S.range.starProjection)‖ ≤
      Real.sqrt ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp S)‖ *
        Real.sqrt ‖inverseGram S hS‖ := by
  rw [← injectiveRangeProjector_eq_starProjection T hT,
    ← injectiveRangeProjector_eq_starProjection S hS]
  change ‖(T.comp (inverseGram T hT)).comp
    ((T.adjoint.comp (X.comp S)).comp ((inverseGram S hS).comp S.adjoint))‖ ≤ _
  refine le_trans (opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)) ?_
  rw [norm_T_comp_inverseGram_eq_sqrt, norm_inverseGram_comp_adjoint_eq_sqrt, mul_assoc]


/-- Eventual inverse Gram bounds transfer decay of the rectangular pullback
to operator-norm decay of the cross compression. The Hilbert spaces may vary
with the index and the filter is arbitrary. -/
theorem tendsto_starProjection_comp_starProjection_zero_of_inverseGram_bounds
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E G F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
    [∀ i, FiniteDimensional 𝕜 (G i)] [∀ i, CompleteSpace (G i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i) (S : (i : ι) → G i →L[𝕜] F i)
    (X : (i : ι) → F i →L[𝕜] F i) {C D : ℝ}
    (hT : ∀ᶠ i in l, ∃ hInj : Function.Injective (T i), ‖inverseGram (T i) hInj‖ ≤ C)
    (hS : ∀ᶠ i in l, ∃ hInj : Function.Injective (S i), ‖inverseGram (S i) hInj‖ ≤ D)
    (hCross : Tendsto (fun i => ‖(T i).adjoint.comp ((X i).comp (S i))‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖(T i).range.starProjection.comp ((X i).comp (S i).range.starProjection)‖) l (𝓝 0) := by
  have hUpper : Tendsto (fun i => Real.sqrt C *
      ‖(T i).adjoint.comp ((X i).comp (S i))‖ * Real.sqrt D) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := Real.sqrt C)).mul hCross).mul_const (Real.sqrt D)
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hT, hS] with i hiT hiS
  obtain ⟨hInjT, hiT⟩ := hiT
  obtain ⟨hInjS, hiS⟩ := hiS
  refine (norm_starProjection_comp_starProjection_le_inverseGram
    (T i) (S i) hInjT hInjS (X i)).trans ?_
  gcongr

end ContinuousLinearMap
