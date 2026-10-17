/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchSupply
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.PEPS.AreaLaw.Geometry.ClosedSquare

/-!
# Square samples in integer coordinates

The maximum metric on the plane identifies the square samples of an encoded
patch with the coordinate inequalities used for finite integer domains.
The integer embedding of the open square starts at zero; translation by
\((1,1)\) gives the positions used in the polynomial-PEPS manuscript.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25,
and `03-patches.tex`, lines 14–22 and 53–54, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The metric square sample equals the closed coordinate sample on any finite
integer domain. No restriction on the center or radius is required.

Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 14–22. -/
theorem squareSample_integerCoordinates (Λ : Finset (ℤ × ℤ))
    (center : ℝ × ℝ) (r : ℝ) :
    EncodedFrame.squareSample
      (fun x : AreaLaw.Site Λ ↦ ((x.1.1 : ℝ), (x.1.2 : ℝ))) center r =
      AreaLaw.Geometry.closedSquareSample Λ center r := by
  ext x
  simp [EncodedFrame.squareSample, AreaLaw.Geometry.mem_closedSquareSample,
    Prod.dist_eq, Real.dist_eq]

/-- Translating the integer embedding by one in each coordinate gives the
physical lattice positions of the polynomial-PEPS manuscript.

Source: polynomial-PEPS manuscript, `00-introduction.tex`, lines 21–25. -/
theorem integerCoordinates_add_one_eq_latticePos (L : ℕ) :
    (fun v : SquareLatticeVertex L L ↦
      (((AreaLaw.rectangleSiteEquiv L L v).1.1 : ℝ),
        ((AreaLaw.rectangleSiteEquiv L L v).1.2 : ℝ)) + (1, 1)) =
      latticePos L := by
  funext v
  simp [latticePos, AreaLaw.rectangleEmbedding]

end TNLean.PEPS.Approximation
