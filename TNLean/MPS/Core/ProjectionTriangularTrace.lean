/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.ProjectionTriangularTrace
import TNLean.MPS.Defs

/-!
# Projection-triangular trace bridge

This file connects the generic projection-triangular word-trace theorem to
`MPSTensor.SameMPV`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If the lower-left blocks vanish with respect to a projection `P`, then dropping the
off-diagonal blocks does not change the MPV family. -/
theorem sameMPV_diagPart_of_lowerZero
    (A : MPSTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hLower : ∀ i : Fin d, (1 - P) * A i * P = 0) :
    SameMPV A (Kraus.diagPart A P) := by
  intro N σ
  simp only [mpv, coeff]
  exact Kraus.trace_evalWord_diagPart_eq A P hP hLower (List.ofFn σ)

end MPSTensor
