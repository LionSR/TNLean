/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

/-!
# Left inverses of injective rectangular matrices

For an injective complex matrix C, the Hermitian Gram matrix C†C is positive
definite. Thus H=(C†C)⁻¹C† satisfies HC=I. The formula does not require C to be
isometric and applies also to a zero-dimensional domain.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- The Gram left inverse of an injective rectangular complex matrix is a left inverse. -/
theorem gramLeftInverse_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (C : Matrix m n ℂ) (hInj : Function.Injective C.mulVec) :
    ((Cᴴ * C)⁻¹ * Cᴴ) * C = 1 := by
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.PosDef.conjTranspose_mul_self _ hInj).isUnit)

/-- The Gram left inverse of a continuous injective matrix family is continuous. -/
theorem continuous_gramLeftInverse
    {T : Type*} [TopologicalSpace T] {m n : ℕ}
    (C : T → Matrix (Fin m) (Fin n) ℂ) (hC : Continuous C)
    (hInj : ∀ t, Function.Injective (C t).mulVec) :
    Continuous fun t => ((C t)ᴴ * C t)⁻¹ * (C t)ᴴ := by
  have hGram : Continuous fun t => (C t)ᴴ * C t :=
    hC.matrix_conjTranspose.matrix_mul hC
  have hInv : Continuous fun t => ((C t)ᴴ * C t)⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨u, hu⟩ := (Matrix.PosDef.conjTranspose_mul_self _ (hInj t)).isUnit
    have hAt : ContinuousAt Ring.inverse ((C t)ᴴ * C t) :=
      hu ▸ NormedRing.inverse_continuousAt u
    simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using
      hAt.comp' (f := fun s : T => (C s)ᴴ * C s) hGram.continuousAt
  exact hInv.matrix_mul hC.matrix_conjTranspose

end Matrix
