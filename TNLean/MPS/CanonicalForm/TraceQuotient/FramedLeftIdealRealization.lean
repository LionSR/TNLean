/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs
import QICLean.Algebra.MatrixAlgebra.SkolemNoether
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousOn
import QICLean.Analysis.Topology.TraceQuotientCoordinates

/-!
# Matrix realization from a framed principal left ideal

A finite-dimensional complex algebra identified pointwise with a full matrix algebra can be
represented on a principal left ideal of the defining matrix dimension. A supplied frame and
left inverse give explicit matrices for this representation. The representation is an inner
conjugate of the pointwise identification, and therefore preserves its trace.

This is an algebraic auxiliary result towards reconstruction from finite-ring trace data,
motivated by arXiv:1010.3732, Section II.F.2, lines 953–993 of the local source. The frame and its
left inverse are supplied. Their continuous construction is separate; no continuous choice of
the pointwise matrix-algebra identification is required. No physical-gap implication or
varying-rank phase invariance is asserted here.

The inner-conjugacy and matrix-algebra equivalence statements concern positive matrix dimension.
Idempotence of the element defining the ideal is unnecessary for these algebraic statements.

## Continuity of a framed left action

Continuous multiplication coefficients, rectangular frames, left inverses, and letter
coordinates give continuous matrices for the left action. This is a finite-dimensional
continuity statement towards tensor reconstruction in arXiv:1010.3732, Section II.F.2,
lines 953–993 of the local source. The frame and left inverse are explicit inputs here;
no continuous pointwise matrix-algebra identification or physical-gap implication is assumed.
-/

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix BigOperators

namespace MPSTensor

/-- Evaluating letters in a framed principal left ideal preserves their tensor gauge class.
The letters are compared with their supplied pointwise matrix-algebra identification; no
claim about all positive-length vectors of an unrelated ambient tensor is made. -/
theorem gaugeEquiv_leftIdealFrameAction {d r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) (v : Fin d → Fin r → ℂ) :
    GaugeEquiv (fun i => E (v i)) (fun i => Matrix.leftIdealFrameAction μ J H (v i)) := by
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_leftIdealFrame μ E hE p J H hHJ hRange
  exact ⟨X, fun i => hX (v i)⟩

end MPSTensor

end
