/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicLayers
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd

/-!
# Closures of dyadic cells and layers

A half-open dyadic cell has a closed rectangular closure. Since each actual
layer is a finite union of cells, its closure is the union of these closed
rectangles. This uses closure of a finite union, rather than a rule for the
closure of a set difference. The formulas are preliminary to the layer-distance
estimates, which are not established here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families` and
`geometry:layer-distance`, lines 151–189.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/10-geometry.tex
Labels: prop:two-families, geometry:layer-distance.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.closure_dyadiccell
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.closure_dyadicCell
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.closure_dyadiclayer_eq_iunion
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.closure_dyadicLayer_eq_iUnion
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The closure of a translated half-open dyadic cell is its closed rectangle.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
theorem closure_dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) :
    closure (dyadicCell o k z) =
      Set.Icc (o.1 + (2 : ℝ) ^ k * z.1) (o.1 + (2 : ℝ) ^ k * (z.1 + 1)) ×ˢ
        Set.Icc (o.2 + (2 : ℝ) ^ k * z.2) (o.2 + (2 : ℝ) ^ k * (z.2 + 1)) := by
  have h (a : ℝ) (i : ℤ) :
      a + (2 : ℝ) ^ k * i ≠ a + (2 : ℝ) ^ k * (i + 1) := by
    have hp : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
    linarith
  rw [dyadicCell, closure_prod_eq, closure_Ico (h _ _), closure_Ico (h _ _)]

/-- The closure of a dyadic layer is the finite union of its cell closures.
Source: area-law Section 11, `prop:two-families`, `geometry:layer-distance`,
lines 179–189. -/
theorem closure_dyadicLayer_eq_iUnion (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    closure (dyadicLayer o k Z C) =
      ⋃ z ∈ dyadicLayerIndices o k Z C, closure (dyadicCell o k z) := by
  rw [dyadicLayer_eq_iUnion, Finset.closure_biUnion]

end TNLean.PEPS.AreaLaw.Geometry
