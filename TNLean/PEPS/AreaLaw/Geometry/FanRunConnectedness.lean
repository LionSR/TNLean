/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanInactiveSeams
import Mathlib.Topology.Connected.Basic

/-!
# Connectedness of retained fan runs

After the color-change radials are removed from an all-midpoint fan, each
equally colored run remains connected both in the open dyadic square and in
the closed centered square whose half-side is one quarter of the cell side.
The retained triangles in the smaller square are convex and nonempty;
graph paths join them through the surviving midpoints of inactive radials.

The origin, signed cell index, dyadic exponent and binary coloring are
arbitrary. Exponent zero and an empty change set are permitted. Runs are
graph components, so separate runs bearing one color remain distinct.
These are auxiliary geometric statements for the initial stars.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 308–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The retained part of an all-midpoint fan triangle in the closed half-radius
square is connected. The retained triangle is convex, and a point in the
smaller open square supplies its nonemptiness.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and
`prop:two-families`, lines 308–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem cellFanClosedHalfPiece_isConnected
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (i : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    IsConnected (cellFanClosedHalfPiece o ℓ z family i) := by
  have hr : 0 < (2 : ℝ) ^ ℓ / 2 :=
    div_pos (pow_pos zero_lt_two ℓ) zero_lt_two
  obtain ⟨x, hx, hxb⟩ :=
    cellFanPolygon_sdiff_radials_inter_ball_nonempty o ℓ z i
      {t | family t ≠ family (cellFanNext t)} (((2 : ℝ) ^ ℓ / 2) / 2)
      (div_pos hr zero_lt_two)
  have hxcb := Metric.ball_subset_closedBall hxb
  have hconvex : Convex ℝ (cellFanClosedHalfPiece o ℓ z family i) :=
    ((cellFanPolygon_sdiff_radials_convex o ℓ z (fun _ ↦ true) i
      {t | family t ≠ family (cellFanNext t)}).inter
      (convex_ball (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2))).inter
      (convex_closedBall (cellFanCenter o ℓ z) (((2 : ℝ) ^ ℓ / 2) / 2))
  exact hconvex.isConnected ⟨x,
    ⟨hx, Metric.closedBall_subset_ball (half_lt_self hr) hxcb⟩, hxcb⟩

/-- A connected component of the existing equally colored fan graph gives a
connected union after the actual color-change radials are removed.

Auxiliary to the gluing step in OpenAI, *A two-dimensional area law from a
global spectral gap*, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 308–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The adjacent-piece theorem supplies the surviving intersections.
The component is not identified with its color. Empty cuts are allowed. -/
theorem cellFanRunRegion_cut_inter_ball_isConnected
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
    let c := cellFanCenter o ℓ z
    let r := (2 : ℝ) ^ ℓ / 2
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let L := ⋃ t ∈ A,
      segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
    IsConnected ((cellFanRunRegion o ℓ z (fun _ ↦ true) family R \ L) ∩
      Metric.ball c r) := by
  dsimp only
  let S := cellFanCutPiece o ℓ z family
  have hr : 0 < (2 : ℝ) ^ ℓ / 2 :=
    div_pos (pow_pos zero_lt_two ℓ) zero_lt_two
  let : Nonempty R.supp := R.nonempty_supp.to_subtype
  have hpieces (i : R.supp) : IsConnected (S i.val) :=
    cellFanPolygon_sdiff_radials_inter_ball_isConnected o ℓ z i.val
      {t | family t ≠ family (cellFanNext t)} ((2 : ℝ) ^ ℓ / 2) hr
  have hchain (i j : R.supp) :
      Relation.ReflTransGen
        (fun u v : R.supp ↦ (S u.val ∩ S v.val).Nonempty) i j := by
    have hpath : Relation.ReflTransGen R.toSimpleGraph.Adj i j :=
      (SimpleGraph.reachable_iff_reflTransGen (G := R.toSimpleGraph) i j).mp
        (R.reachable_toSimpleGraph i.property j.property)
    have hstep : R.toSimpleGraph.Adj ≤
        (fun u v : R.supp ↦ (S u.val ∩ S v.val).Nonempty) :=
      fun u v huv ↦ cellFanPolygon_cut_inter_nonempty_of_adj o ℓ z family u.val v.val
        ((R.toSimpleGraph_adj u.property v.property).mp huv)
    exact Relation.ReflTransGen.mono hstep i j hpath
  have hconnected : IsConnected (⋃ i : R.supp, S i.val) :=
    IsConnected.iUnion_of_reflTransGen hpieces hchain
  simpa only [S, cellFanCutPiece, ← Set.iUnion_inter, ← Set.iUnion_sdiff,
    Set.iUnion_subtype, cellFanRunRegion] using hconnected

/-- Every equally colored run of the all-midpoint fan is connected in the
closed half-radius square after the actual color-change radials are removed.
The elementary pieces are joined along the surviving intersections of
adjacent triangles in the run.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and
`prop:two-families`, lines 308–323, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The center is retained when the cut set is empty, and separate runs bearing
the same color are not identified. -/
theorem cellFanRunRegion_cut_inter_closedHalfBall_isConnected
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2)
    (R : CellFanRun o ℓ z (fun _ ↦ true) family) :
    let c := cellFanCenter o ℓ z
    let r := (2 : ℝ) ^ ℓ / 2
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let L := ⋃ t ∈ A,
      segment ℝ c (cellFanEnd o ℓ z (fun _ ↦ true) t)
    IsConnected ((cellFanRunRegion o ℓ z (fun _ ↦ true) family R \ L) ∩
      Metric.closedBall c (r / 2)) := by
  let : Nonempty R.supp := R.nonempty_supp.to_subtype
  have hconnected : IsConnected (⋃ i : R.supp, cellFanClosedHalfPiece o ℓ z family i.val) :=
    IsConnected.iUnion_of_reflTransGen
      (fun i : R.supp ↦ cellFanClosedHalfPiece_isConnected o ℓ z family i.val)
      (fun i j : R.supp ↦ Relation.ReflTransGen.mono
        (fun u v huv ↦ cellFanPolygon_cut_inter_closedHalfBall_nonempty_of_adj
          o ℓ z family u.val v.val ((R.toSimpleGraph_adj u.property v.property).mp huv))
        i j ((SimpleGraph.reachable_iff_reflTransGen (G := R.toSimpleGraph) i j).mp
          (R.reachable_toSimpleGraph i.property j.property)))
  have hinter :
      Metric.ball (cellFanCenter o ℓ z) ((2 : ℝ) ^ ℓ / 2) ∩
        Metric.closedBall (cellFanCenter o ℓ z) (((2 : ℝ) ^ ℓ / 2) / 2) =
      Metric.closedBall (cellFanCenter o ℓ z) (((2 : ℝ) ^ ℓ / 2) / 2) :=
    Set.inter_eq_right.mpr (Metric.closedBall_subset_ball
      (half_lt_self (div_pos (pow_pos zero_lt_two ℓ) zero_lt_two)))
  simpa only [cellFanClosedHalfPiece, cellFanCutPiece, Set.inter_assoc, hinter,
    ← Set.iUnion_inter, ← Set.iUnion_sdiff, Set.iUnion_subtype, cellFanRunRegion]
    using hconnected

end TNLean.PEPS.AreaLaw.Geometry
