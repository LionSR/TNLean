/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing matrix projections

Changing the finite index set of a square matrix preserves its
self-adjointness and idempotence. This identifies the same projection
in the physical and virtual coordinates of a tensor network.
-/

namespace Matrix

/-- A simultaneous change of row and column indices preserves a
self-adjoint idempotent matrix. -/
theorem isStarProjection_reindex {R ι κ : Type*}
    [AddCommMonoid R] [Mul R] [Star R] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι R) (hA : IsStarProjection A) :
    IsStarProjection (Matrix.reindex e e A) := by
  refine ⟨hA.isIdempotentElem.map (Matrix.reindexRingEquiv R e), ?_⟩
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex] using
    congrArg (Matrix.reindex e e) hA.isSelfAdjoint.star_eq

end Matrix
