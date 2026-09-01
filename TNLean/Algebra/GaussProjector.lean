/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteGroupUnitaryAverage
import TNLean.Algebra.GaussRepresentation

/-!
# Local Gauss projector

The normalized average of the local Gauss representation is the unplaced local
projector kernel from FBC25, Equation `eq:gauge_projs` (arXiv:2502.20257,
lines 3494--3499). Finite-chain placement on sites `(j, j + 1)` and invariance
of the gauged matrix product state are not treated here.
-/

noncomputable section

open scoped BigOperators

namespace TNLean.Algebra

variable {G n : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype n] [DecidableEq n]

/-- The unplaced local Gauss projector kernel obtained by averaging the Gauss
representation over the finite group, as in FBC25, Equation `eq:gauge_projs`
(arXiv:2502.20257, lines 3494--3499). -/
def gaussProjector (R : G → G → Matrix.unitaryGroup n ℂ) :
    Matrix (n × (G × G)) (n × (G × G)) ℂ :=
  finiteGroupUnitaryAverage (gaussRepresentation R)

/-- The local Gauss projector is the normalized sum of the local Gauss
operators from FBC25, Equation `eq:gauge_projs`. -/
theorem gaussProjector_eq_average (R : G → G → Matrix.unitaryGroup n ℂ) :
    gaussProjector R =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, gaussOperator R g := by
  simp [gaussProjector, finiteGroupUnitaryAverage]

/-- The unplaced local Gauss projector kernel is a star projection. -/
theorem isStarProjection_gaussProjector
    (R : G → G → Matrix.unitaryGroup n ℂ) :
    IsStarProjection (gaussProjector R) :=
  isStarProjection_finiteGroupUnitaryAverage (gaussRepresentation R)

end TNLean.Algebra
