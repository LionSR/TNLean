/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.SideSubdivision
import QICLean.ManyBody.Sites.Dyadic.DyadicClosure
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.SideSubdivisionMask
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Convex.Combination
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellFans
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The eight open sectors of a midpoint-subdivided fan

The interior of each triangle in the actual all-midpoint fan avoids the
four allowed lines through the cell center. The four coordinate functionals
place the defining vertices on one weak side of each such line. Openness
then makes the half-plane inequality strict in the triangle interior.

The assertion holds for every origin, natural dyadic exponent and signed
cell index. It concerns the existing fan triangles, without an angular
coordinate or a presumed local region assignment.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–310,
and `geometry:initial-stars`, lines 352–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_exists_affineBasis`: affine coordinates for actual
  fan triangles.
* `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon_interior_nonempty_and_closure_eq`: nonempty interiors
  of dyadic fan triangles.
-/

open ManyBody (IsAllowedSlope TemplatePolygon)

section CellFanSectors

namespace TNLean.PEPS.AreaLaw.Geometry

/-- An interior triangle point cannot remain on a functional level when its
vertices lie in one weak half-plane through the first vertex.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363. -/
private theorem interior_triangle_ne_functional_level
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (hf : Function.Surjective f) {c a b x : ℝ × ℝ}
    (hside : (f c ≤ f a ∧ f c ≤ f b) ∨ (f a ≤ f c ∧ f b ≤ f c))
    (hx : x ∈ interior (convexHull ℝ {c, a, b})) : f x ≠ f c := by
  have hstrict (g : (ℝ × ℝ) →L[ℝ] ℝ) (hg : Function.Surjective g)
      (ha : g c ≤ g a) (hb : g c ≤ g b) : g c < g x := by
    have hsub : convexHull ℝ {c, a, b} ⊆ g ⁻¹' Set.Ici (g c) := by
      have hconv : Convex ℝ (g ⁻¹' Set.Ici (g c)) :=
        (convex_Ici (𝕜 := ℝ) (β := ℝ) (g c)).linear_preimage g.toLinearMap
      refine convexHull_min (𝕜 := ℝ) (t := g ⁻¹' Set.Ici (g c)) ?_ hconv
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      change g c ≤ g y
      rcases hy with rfl | rfl | rfl
      · exact le_rfl
      · exact ha
      · exact hb
    have hxi := interior_mono hsub hx
    rw [g.interior_preimage hg, interior_Ici] at hxi
    exact hxi
  rcases hside with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ne_of_gt (hstrict f hf ha hb)
  · have hneg : Function.Surjective (-f) := by
      intro t
      obtain ⟨y, hy⟩ := hf (-t)
      refine ⟨y, ?_⟩
      change -(f y) = t
      rw [hy, neg_neg]
    have hlt := hstrict (-f) hneg (by simpa using neg_le_neg ha)
      (by simpa using neg_le_neg hb)
    change -(f c) < -(f x) at hlt
    exact ne_of_lt (by linarith)

/-- The four linear functionals whose kernels are the allowed directions.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363. -/
private def slopeFunctional (j : Fin 4) : (ℝ × ℝ) →L[ℝ] ℝ :=
  match j.val with
  | 0 => ContinuousLinearMap.fst ℝ ℝ ℝ
  | 1 => ContinuousLinearMap.snd ℝ ℝ ℝ
  | 2 => ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  | _ => ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Each prescribed direction functional is surjective.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363. -/
private theorem slopeFunctional_surjective (j : Fin 4) :
    Function.Surjective (slopeFunctional j) := by
  intro t
  fin_cases j
  · exact ⟨(t, 0), rfl⟩
  · exact ⟨(0, t), rfl⟩
  · exact ⟨(t, 0), by simp [slopeFunctional]⟩
  · exact ⟨(t, 0), by simp [slopeFunctional]⟩

/-- An allowed direction is annihilated by one of the four functionals.
Auxiliary to Section 11, `geometry:initial-stars`, lines 352–363. -/
private theorem exists_slopeFunctional_zero {u : ℝ × ℝ} (hu : IsAllowedSlope u) :
    ∃ j : Fin 4, slopeFunctional j u = 0 := by
  rcases hu with hu | hu | hu | hu
  · exact ⟨0, hu⟩
  · exact ⟨1, hu⟩
  · refine ⟨3, ?_⟩
    simpa [slopeFunctional, sub_eq_zero] using hu
  · refine ⟨2, ?_⟩
    change u.1 + u.2 = 0
    linarith

/-- The two perimeter vertices of an all-midpoint triangle lie in one weak
half-plane through the center for each allowed-direction functional.
Auxiliary to Section 11, `prop:two-families`, lines 299–310,
and `geometry:initial-stars`, lines 352–363. -/
private theorem fan_vertices_same_functional_side (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (i : CellFanSlot (fun _ ↦ true)) (j : Fin 4) :
    let c := cellFanCenter o ℓ z
    let a := cellFanStart o ℓ z (fun _ ↦ true) i
    let b := cellFanEnd o ℓ z (fun _ ↦ true) i
    (slopeFunctional j c ≤ slopeFunctional j a ∧
      slopeFunctional j c ≤ slopeFunctional j b) ∨
    (slopeFunctional j a ≤ slopeFunctional j c ∧
      slopeFunctional j b ≤ slopeFunctional j c) := by
  dsimp only
  rcases i with ⟨s, n⟩
  have hcoords := cellFan_unsplit_endpoints_coordinates o ℓ z s
  have ha := congrArg Prod.fst hcoords
  have hb := congrArg Prod.snd hcoords
  have ht : 0 < (2 : ℝ) ^ ℓ := pow_pos zero_lt_two _
  rcases cellFan_elementary_endpoints_cases o ℓ z (fun _ ↦ true) ⟨s, n⟩ with
    ⟨hf, _, _⟩ | ⟨_, hs, he⟩ | ⟨_, hs, he⟩
  · contradiction
  all_goals
    rw [hs, he]
    fin_cases s <;> fin_cases j <;> norm_num at ha hb
  all_goals
    rw [ha, hb]
    norm_num [slopeFunctional, cellFanCenter, midpoint_eq_smul_add,
      invOf_eq_inv, smul_eq_mul]; first
    | nlinarith
    | left
      first
      | nlinarith
      | apply And.intro <;> nlinarith
    | right
      first
      | nlinarith
      | apply And.intro <;> nlinarith

/-- The interior of each of the eight actual midpoint-subdivided fan triangles
avoids every allowed direction from the cell center.
Source: Section 11, `prop:two-families`, lines 299–310,
and `geometry:initial-stars`, lines 352–363. -/
theorem cellFanPolygon_interior_not_isAllowedSlope_sub_center
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fun _ ↦ true)) {x : ℝ × ℝ}
    (hx : x ∈ interior (cellFanPolygon o ℓ z (fun _ ↦ true) i).region) :
    ¬ IsAllowedSlope (x - cellFanCenter o ℓ z) := by
  intro hallowed
  obtain ⟨j, hj⟩ := exists_slopeFunctional_zero hallowed
  have hne := interior_triangle_ne_functional_level (slopeFunctional j)
    (slopeFunctional_surjective j) (fan_vertices_same_functional_side o ℓ z i j) hx
  apply hne
  exact sub_eq_zero.mp (by simpa only [map_sub] using hj)

end TNLean.PEPS.AreaLaw.Geometry

end CellFanSectors

section FanRegularity

/-!
## Nonempty interiors of dyadic fan triangles

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

end

end FanRegularity

section FanAffineCoordinates

/-!
## Affine coordinates for actual fan triangles

The center and the two perimeter vertices of every actual fan triangle form
an affine basis of the plane. This basis is derived from the nonempty interior
of the triangle; it is not additional geometric data. The origin, dyadic
exponent, signed cell index and optional midpoint subdivisions are arbitrary.

### References

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

end

end FanAffineCoordinates
