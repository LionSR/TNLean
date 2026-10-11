/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRegularity
import Mathlib.Analysis.Convex.Combination

/-!
# Affine coordinates for actual fan triangles

The center and the two perimeter vertices of every actual fan triangle form
an affine basis of the plane. This basis is derived from the nonempty interior
of the triangle; it is not additional geometric data. The origin, dyadic
exponent, signed cell index and optional midpoint subdivisions are arbitrary.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, especially
308–316, and `geometry:initial-stars`, lines 352–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Three points whose convex hull has nonempty interior form an affine basis
of the plane. Auxiliary to area-law Section 11, `prop:two-families`,
lines 308–316, and `geometry:initial-stars`, lines 352–363. -/
private theorem triangle_exists_affineBasis_of_nonempty_interior (c a b : ℝ × ℝ)
    (h : (interior (convexHull ℝ ({c, a, b} : Set (ℝ × ℝ)))).Nonempty) :
    ∃ B : AffineBasis (Fin 3) ℝ (ℝ × ℝ),
      (B : Fin 3 → ℝ × ℝ) = ![c, a, b] := by
  have hspan : affineSpan ℝ ({c, a, b} : Set (ℝ × ℝ)) = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior h
  have hvspan : vectorSpan ℝ ({c, a, b} : Set (ℝ × ℝ)) = ⊤ :=
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ (ℝ × ℝ) (ℝ × ℝ) hspan
  have hrange : Set.range (![c, a, b] : Fin 3 → ℝ × ℝ) = {c, a, b} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  have hrank : Module.finrank ℝ
      (vectorSpan ℝ (Set.range (![c, a, b] : Fin 3 → ℝ × ℝ))) = 2 := by
    rw [hrange]
    rw [hvspan]
    simp only [finrank_top, Module.finrank_prod, Module.finrank_self]
  have hind : AffineIndependent ℝ (![c, a, b] : Fin 3 → ℝ × ℝ) :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ
      (![c, a, b] : Fin 3 → ℝ × ℝ) (n := 2) (by simp)).mpr hrank
  exact ⟨⟨![c, a, b], hind, (congrArg (affineSpan ℝ) hrange).trans hspan⟩, rfl⟩

/-- The three actual fan vertices form an affine basis of the plane.
The basis is derived from actual fan regularity, for every optional subdivision.
Source: area-law Section 11, `prop:two-families`, lines 308–316, and
`geometry:initial-stars`, lines 352–363. -/
theorem cellFanPolygon_exists_affineBasis (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    ∃ B : AffineBasis (Fin 3) ℝ (ℝ × ℝ),
      (B : Fin 3 → ℝ × ℝ) =
        ![cellFanCenter o ℓ z, cellFanStart o ℓ z split i, cellFanEnd o ℓ z split i] := by
  exact triangle_exists_affineBasis_of_nonempty_interior
    (cellFanCenter o ℓ z) (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)
    (cellFanPolygon_interior_nonempty_and_closure_eq o ℓ z split i).1

end TNLean.PEPS.AreaLaw.Geometry
