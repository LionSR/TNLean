/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.InjectiveRangeProjector
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of finite-dimensional range projectors

For a continuous family of injective maps from a fixed finite-dimensional
Hilbert space, the orthogonal projectors onto their ranges vary continuously.
This is the analytic step needed to control finite-window parent terms along
an injective MPS deformation. It follows from the inverse-Gram formula in
QICLean and continuity of inversion at units of a Banach algebra.
-/

namespace ContinuousLinearMap

/-- A family of maps out of a finite coordinate Hilbert space is continuous
when its values on every coordinate vector are continuous. -/
theorem continuous_of_euclideanSingle
    {X F ι : Type*} [TopologicalSpace X] [Finite ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : X → EuclideanSpace ℂ ι →L[ℂ] F)
    (h : ∀ i, Continuous fun x => T x (EuclideanSpace.single i 1)) :
    Continuous T := by
  have := Fintype.ofFinite ι
  refine continuous_clm_apply.2 fun y => ?_
  have hy : (fun x => T x y) =
      fun x => ∑ i, y i • T x (EuclideanSpace.single i 1) := by
    funext x
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr y]
    simp [map_sum, map_smul]
  rw [hy]
  exact continuous_finsetSum _ fun i _ => (h i).const_smul _

/-- At an injective finite-dimensional map, the orthogonal range projector is
continuous even if nearby maps have not been supplied with injectivity proofs.
Injectivity persists in a neighborhood by openness. -/
theorem continuousAt_range_starProjection_of_injective
    {X 𝕜 E F : Type*} [TopologicalSpace X] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : X → E →L[𝕜] F) {x₀ : X} (hT : ContinuousAt T x₀)
    (hInj : Function.Injective (T x₀)) :
    ContinuousAt (fun x => (T x).range.starProjection) x₀ := by
  have hAdj : ContinuousAt (fun x => (T x).adjoint) x₀ :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp hT
  have hGram := hAdj.clm_comp hT
  let u : (E →L[𝕜] E)ˣ :=
    ⟨(T x₀).adjoint.comp (T x₀), inverseGram (T x₀) hInj,
      adjoint_comp_self_comp_inverseGram (T x₀) hInj,
      inverseGram_comp_adjoint_comp_self (T x₀) hInj⟩
  have hInv : ContinuousAt (fun x => Ring.inverse ((T x).adjoint.comp (T x))) x₀ :=
    (NormedRing.inverse_continuousAt u).comp'
      (f := fun x => (T x).adjoint.comp (T x)) hGram
  have hProj := hT.clm_comp (hInv.clm_comp hAdj)
  have hEv : ∀ᶠ x in nhds x₀, Function.Injective (T x) :=
    hT.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hInj)
  apply hProj.congr_of_eventuallyEq
  filter_upwards [hEv] with x hx
  rw [← injectiveRangeProjector_eq_starProjection (T x) hx]
  simp only [injectiveRangeProjector, inverseGram_eq_ringInverse]

/-- The orthogonal range projector of a continuous family of injective
finite-dimensional maps depends continuously on the parameter. -/
theorem continuous_injectiveRangeProjector
    {X 𝕜 E F : Type*} [TopologicalSpace X] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : X → E →L[𝕜] F) (hT : Continuous T)
    (hInj : ∀ x, Function.Injective (T x)) :
    Continuous fun x => injectiveRangeProjector (T x) (hInj x) := by
  have hRange : Continuous fun x => (T x).range.starProjection :=
    continuous_iff_continuousAt.mpr fun x =>
      continuousAt_range_starProjection_of_injective T hT.continuousAt (hInj x)
  convert hRange using 1
  funext x
  exact injectiveRangeProjector_eq_starProjection (T x) (hInj x)

end ContinuousLinearMap
