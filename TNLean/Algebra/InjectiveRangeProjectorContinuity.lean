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
  let : Fintype ι := Fintype.ofFinite ι
  let e := EuclideanSpace.equiv ι ℂ
  let p := ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := F) ι
  have hp : Continuous fun x => p ((T x).comp e.symm.toContinuousLinearMap) := by
    apply continuous_pi
    intro i
    convert h i using 1
    ext x
    simp [p, ContinuousLinearEquiv.piRing, e, LinearEquiv.piRing_apply]
  have hcomp : Continuous fun x => (T x).comp e.symm.toContinuousLinearMap := by
    convert p.symm.continuous.comp hp using 1
    funext x
    simp
  have hback : Continuous fun x =>
      ((T x).comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap :=
    hcomp.clm_comp_const e.toContinuousLinearMap
  convert hback using 1
  ext x v
  simp

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
  have hAdj : Continuous fun x => (T x).adjoint :=
    ContinuousLinearMap.adjoint.continuous.comp hT
  have hGram : Continuous fun x => (T x).adjoint.comp (T x) :=
    hAdj.clm_comp hT
  let hGramUnit (x : X) : (E →L[𝕜] E)ˣ :=
    ⟨(T x).adjoint.comp (T x), inverseGram (T x) (hInj x),
      adjoint_comp_self_comp_inverseGram (T x) (hInj x),
      inverseGram_comp_adjoint_comp_self (T x) (hInj x)⟩
  have hInv : Continuous fun x => Ring.inverse ((T x).adjoint.comp (T x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hInvAt : ContinuousAt
        (Ring.inverse : (E →L[𝕜] E) → E →L[𝕜] E)
        ((T x).adjoint.comp (T x)) := by
      exact NormedRing.inverse_continuousAt (hGramUnit x)
    exact hInvAt.comp' (f := fun y : X => (T y).adjoint.comp (T y))
      hGram.continuousAt
  have hProj : Continuous fun x =>
      (T x).comp ((Ring.inverse ((T x).adjoint.comp (T x))).comp (T x).adjoint) :=
    hT.clm_comp (hInv.clm_comp hAdj)
  convert hProj using 1
  ext x
  simp only [injectiveRangeProjector, inverseGram_eq_ringInverse]

end ContinuousLinearMap
