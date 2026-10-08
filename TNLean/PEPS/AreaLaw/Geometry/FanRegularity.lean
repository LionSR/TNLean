/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.fan_triangle_regularity
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_interior_nonempty_and_closure_eq
Source labels: prop:two-families, geometry:initial-stars
Source: Section 11, prop:two-families, lines 299–323, especially 308–316; geometry:initial-stars,
lines 333–370, especially 352–363.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFans
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Nonempty interiors of dyadic fan triangles

Every actual fan triangle has nonempty interior and equals the closure of
that interior. The nonzero determinant in the triangle definition supplies
a basis of the plane; convexity and closedness then give the closure equality.
The origin, dyadic exponent, signed cell index and midpoint subdivisions are
arbitrary.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323,
especially 308–316, and `geometry:initial-stars`, lines 352–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A nonzero planar determinant gives nonempty interior of the triangle hull.
Auxiliary to Section 11, `prop:two-families`, lines 308–316. -/
private theorem triangle_interior_nonempty (a b c : ℝ × ℝ)
    (hdet : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0) :
    (interior (convexHull ℝ {a, b, c})).Nonempty := by
  have hli : LinearIndependent ℝ ![b - a, c - a] := by
    apply LinearIndependent.pair_iff.mpr
    intro r s hrs
    have h₁ := congrArg Prod.fst hrs
    have h₂ := congrArg Prod.snd hrs
    change r * (b.1 - a.1) + s * (c.1 - a.1) = 0 at h₁
    change r * (b.2 - a.2) + s * (c.2 - a.2) = 0 at h₂
    have hr : r * ((b.1 - a.1) * (c.2 - a.2) -
        (b.2 - a.2) * (c.1 - a.1)) = 0 := by
      linear_combination (c.2 - a.2) * h₁ - (c.1 - a.1) * h₂
    have hs : s * ((b.1 - a.1) * (c.2 - a.2) -
        (b.2 - a.2) * (c.1 - a.1)) = 0 := by
      linear_combination -(b.2 - a.2) * h₁ + (b.1 - a.1) * h₂
    exact ⟨(mul_eq_zero.mp hr).resolve_right hdet,
      (mul_eq_zero.mp hs).resolve_right hdet⟩
  have hspan : Submodule.span ℝ ({b - a, c - a} : Set (ℝ × ℝ)) = ⊤ := by
    simpa only [Matrix.range_cons_cons_empty] using
      hli.span_eq_top_of_card_eq_finrank' (by norm_num)
  have haff := affineSpan_singleton_union_vadd_eq_top_of_span_eq_top (k := ℝ) a
    (s := ({b - a, c - a} : Set (ℝ × ℝ)))
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan)
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  simpa only [Set.image_pair, vadd_eq_add, sub_add_cancel, Set.singleton_union] using haff

/-- An actual fan triangle has nonempty interior and is its closure.
Auxiliary to Section 11, `prop:two-families`, lines 308–316. -/
theorem cellFanPolygon_interior_nonempty_and_closure_eq (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) :
    (interior (cellFanPolygon o ℓ z split i).region).Nonempty ∧
      closure (interior (cellFanPolygon o ℓ z split i).region) =
        (cellFanPolygon o ℓ z split i).region := by
  have h (P : TemplatePolygon) :
      match P with
      | .triangle a b c _ _ _ _ =>
          (interior (convexHull ℝ {a, b, c})).Nonempty ∧
            closure (interior (convexHull ℝ {a, b, c})) = convexHull ℝ {a, b, c}
      | .rectangle _ _ _ _ _ _ _ _ => True := by
    cases P with
    | triangle a b c hd _ _ _ =>
      have hn := triangle_interior_nonempty a b c hd
      have hf : ({a, b, c} : Set (ℝ × ℝ)).Finite :=
        ((Set.finite_singleton c).insert b).insert a
      have hconv := convex_convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))
      refine ⟨hn, ?_⟩
      simpa only [(hf.isClosed_convexHull ℝ).closure_eq] using
        hconv.closure_interior_eq_closure_of_nonempty_interior hn
    | rectangle => trivial
  exact h (cellFanPolygon o ℓ z split i)

end TNLean.PEPS.AreaLaw.Geometry
