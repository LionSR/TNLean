/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.FramedLeftIdealRealization
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousOn

/-!
# Continuity of a framed left action

Continuous multiplication coefficients, rectangular frames, left inverses, and letter
coordinates give continuous matrices for the left action. This is a finite-dimensional
continuity statement towards tensor reconstruction in arXiv:1010.3732, Section II.F.2,
lines 953–993 of the local source. The frame and left inverse are explicit inputs here;
no continuous pointwise matrix-algebra identification or physical-gap implication is assumed.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

namespace Matrix

/-- Explicit framed matrices are continuous on the common domain of their multiplication,
frame, inverse, and letter coefficients. No algebraic assumptions are needed for continuity. -/
theorem continuousOn_leftIdealFrameAction
    {T : Type*} [TopologicalSpace T] {r D : ℕ} (S : Set T)
    (μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (M : T → Matrix (Fin r) (Fin r × Fin r) ℂ) (hM : ContinuousOn M S)
    (hμ : ∀ t x y, μ t x y = M t *ᵥ (fun ab => x ab.1 * y ab.2))
    (J : T → Matrix (Fin r) (Fin D) ℂ) (hJ : ContinuousOn J S)
    (H : T → Matrix (Fin D) (Fin r) ℂ) (hH : ContinuousOn H S)
    (x : T → Fin r → ℂ) (hx : ContinuousOn x S) :
    ContinuousOn (fun t => leftIdealFrameAction (μ t) (J t).mulVecLin
      (H t).mulVecLin (x t)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM hJ hH hx ⊢
  apply continuous_matrix
  intro i j
  have hJs : Continuous fun t : S => J t *ᵥ (Pi.single j 1 : Fin D → ℂ) :=
    hJ.matrix_mulVec continuous_const
  have hTen : Continuous fun t : S => fun ab : Fin r × Fin r =>
      x t ab.1 * (J t *ᵥ (Pi.single j 1 : Fin D → ℂ)) ab.2 :=
    continuous_pi fun ab => ((continuous_apply ab.1).comp hx).mul
      ((continuous_apply ab.2).comp hJs)
  have hCont := (continuous_apply i).comp (hH.matrix_mulVec (hM.matrix_mulVec hTen))
  simpa only [Set.domRestrict_apply, leftIdealFrameAction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.toMatrix'_apply, LinearMap.compr₂_apply,
    LinearMap.compl₂_apply, Matrix.mulVecLin_apply, hμ, Function.comp_def] using hCont

end Matrix
