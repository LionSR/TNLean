/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SideEndpoints
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivisionMask
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Order.DenselyOrdered

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
-/

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
