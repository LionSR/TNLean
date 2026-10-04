/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Structure.TraceQuotientLetterCoordinates
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of reconstructed letter coordinates

The Gram left inverse of an injective fixed trace section varies continuously. Hence the
coordinates of all physical letters vary continuously with the two-site trace form. This is
an auxiliary finite-dimensional step towards reconstruction in arXiv:1010.3732,
Section II.F.2, lines 953–993 of the local source; no continuity of a minimal tensor or
physical-gap implication is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- Reconstructed letter coordinates are continuous wherever the fixed section is injective. -/
theorem continuousOn_traceQuotientLetterCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ} (S : Set T)
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : ContinuousOn G S)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hInj : ∀ t ∈ S, Function.Injective (G t * F).mulVec) :
    ContinuousOn (fun t => traceQuotientLetterCoordinates (G t) F) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hG ⊢
  have hC : Continuous fun t : S => G t * F := hG.matrix_mul continuous_const
  exact (continuous_gramLeftInverse _ hC (fun t => hInj t t.property)).matrix_mul hG

end Matrix
