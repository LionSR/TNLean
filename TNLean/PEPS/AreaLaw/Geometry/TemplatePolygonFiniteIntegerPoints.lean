/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygons
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Finite lattice points in an allowed polygon

A permitted closed triangle or rectangle contains finitely many ambient
integer points. This is an elementary consequence of its coordinate bounds;
no lattice alignment or scale parameter is required.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Definition 9.3 (`scanner:template`), `08-scanner.tex`,
lines 546–569: the permitted closed polygons and their integer samples.
The bounded-box consequence here does not construct a template or assert any
scanner-scale or separation estimate.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The ambient integer points of an allowed polygon form a finite set.
Auxiliary to area-law Definition 9.3 (`scanner:template`), `08-scanner.tex`,
lines 546–569. This is the elementary bounded-box consequence of the allowed
triangle and rectangle definition, using their coordinate supporting bounds. -/
theorem TemplatePolygon.finite_integerPoints (P : TemplatePolygon) :
    Set.Finite {z : ℤ × ℤ | integerPoint z ∈ P.region} := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, hP⟩ := P.exists_four_strip_bounds
  refine ((Set.finite_Icc ⌈lx⌉ ⌊ux⌋).prod (Set.finite_Icc ⌈ly⌉ ⌊uy⌋)).subset ?_
  intro z hz
  have hz' := (hP (integerPoint z)).mp hz
  exact ⟨⟨Int.ceil_le.mpr hz'.1.1, Int.le_floor.mpr hz'.1.2⟩,
    ⟨Int.ceil_le.mpr hz'.2.1.1, Int.le_floor.mpr hz'.2.1.2⟩⟩

end TNLean.PEPS.AreaLaw.Geometry
