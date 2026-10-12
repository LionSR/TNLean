/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Boundary

/-!
# Length-independent arbitrary-boundary adjoint closure

This predicate records one output boundary for all positive chain lengths.
It is shared by the normal periodic-duality and star-compatible coalgebra
representation criteria, neither of which is part of its definition.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5,
lines 1236--1320; Molnár et al., arXiv:2204.05940v1, Section 5.5, following
Proposition 5.4.
-/

open scoped Matrix

namespace MPOTensor

/-- Arbitrary-boundary adjoint closure asks for one output boundary valid
simultaneously at all positive lengths. -/
def IsBoundaryAdjointClosed {d D : ℕ} (T : MPOTensor d D) : Prop :=
  ∀ X : Matrix (Fin D) (Fin D) ℂ,
    ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      ∀ N : ℕ, 0 < N → (mpoWithBoundary T X N)ᴴ = mpoWithBoundary T Y N

end MPOTensor
