/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanSlopes
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.DyadicOrigin
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFineCellCover
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import TNLean.PEPS.AreaLaw.Geometry.MeshGeometry
import Mathlib.Analysis.Convex.Topology

/-!
# Initial region boundaries avoid the integer lattice

Every boundary point of an actual initial birth region lies on an integer
translate of one of the four prescribed supporting lines. Dummy and primary
boundaries come from finitely many dyadic squares. A fan-triangle boundary
comes from the square boundary or from an intersection with another actual
triangle of the same fan; these intersections are radial edges or the center.
The boundary of a run is contained in the union of its constituent triangle
boundaries. Internal seams need not remain boundaries after the union.

The actual vertices lie on the translated integer mesh, and the four allowed
slopes give the supporting-line equations. At the prescribed origin (√2,√3),
these lines avoid all integer lattice sites. Consequently a lattice point
belongs to an initial birth region exactly when it belongs to its interior.
The assertion concerns the initial construction, before recursive repairs.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218, 299–323 and 545–559.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The four integer-translated supporting-line equations.
Auxiliary to area-law Section 11, `prop:two-families`, lines 545–556. -/
private def onSupportingLine (o x : ℝ × ℝ) : Prop :=
  ∃ m : ℤ, x.1 = o.1 + (m : ℝ) ∨ x.2 = o.2 + (m : ℝ) ∨
    x.1 + x.2 = o.1 + o.2 + (m : ℝ) ∨
    x.1 - x.2 = o.1 - o.2 + (m : ℝ)

/-- An allowed segment through a translated integral point lies on one of the
four supporting lines. Auxiliary to area-law Section 11, `prop:two-families`,
lines 545–556. -/
private theorem segment_onSupportingLine (o : ℝ × ℝ) {u v x : ℝ × ℝ}
    (hu : u ∈ affineMesh o 1) (hs : IsAllowedSlope (v - u))
    (hx : x ∈ segment ℝ u v) : onSupportingLine o x := by
  obtain ⟨n, rfl⟩ := hu
  simp only [one_smul] at hs hx
  rw [segment_eq_image' ℝ] at hx
  obtain ⟨r, _, rfl⟩ := hx
  dsimp [IsAllowedSlope, integerPoint] at hs
  rcases hs with hs | hs | hs | hs
  · refine ⟨n.1, Or.inl ?_⟩
    dsimp [integerPoint]
    rw [hs, mul_zero, add_zero]
  · refine ⟨n.2, Or.inr (Or.inl ?_)⟩
    dsimp [integerPoint]
    rw [hs, mul_zero, add_zero]
  · refine ⟨n.1 - n.2, Or.inr (Or.inr (Or.inr ?_))⟩
    dsimp [integerPoint]
    push_cast
    linear_combination r * hs
  · refine ⟨n.1 + n.2, Or.inr (Or.inr (Or.inl ?_))⟩
    dsimp [integerPoint]
    push_cast
    linear_combination r * hs

/-- A dyadic square frontier lies on translated integral coordinate lines.
Auxiliary to area-law Section 11, `prop:two-families`, lines 151–185 and 545–556. -/
private theorem cell_frontier_onSupportingLine (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) {x : ℝ × ℝ} (hx : x ∈ frontier (dyadicCell o ℓ z)) :
    onSupportingLine o x := by
  have ht : 0 < (2 : ℝ) ^ ℓ := pow_pos zero_lt_two ℓ
  have h₁ : o.1 + (2 : ℝ) ^ ℓ * z.1 < o.1 + (2 : ℝ) ^ ℓ * (z.1 + 1) := by
    nlinarith [ht]
  have h₂ : o.2 + (2 : ℝ) ^ ℓ * z.2 < o.2 + (2 : ℝ) ^ ℓ * (z.2 + 1) := by
    nlinarith [ht]
  rw [dyadicCell, frontier_prod_eq, frontier_Ico h₂, frontier_Ico h₁] at hx
  rcases hx with hx | hx
  · have hy := hx.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · refine ⟨(2 : ℤ) ^ ℓ * z.2, Or.inr (Or.inl ?_)⟩
      push_cast
      exact hy
    · refine ⟨(2 : ℤ) ^ ℓ * (z.2 + 1), Or.inr (Or.inl ?_)⟩
      push_cast
      exact hy
  · have hx' := hx.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with hx' | hx'
    · refine ⟨(2 : ℤ) ^ ℓ * z.1, Or.inl ?_⟩
      push_cast
      exact hx'
    · refine ⟨(2 : ℤ) ^ ℓ * (z.1 + 1), Or.inl ?_⟩
      push_cast
      exact hx'

/-- Every mark at positive dyadic exponent lies on the translated integer mesh.
Auxiliary to area-law Section 11, `prop:two-families`, lines 325–330 and 545–549. -/
private theorem mark_mem_unitMesh (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (hℓ : 1 ≤ ℓ) {x : ℝ × ℝ} (hx : x ∈ beltCellMarks o ℓ z) :
    x ∈ affineMesh o 1 := by
  have hxmarks : x ∈ (beltMarks o ℓ {z} : Set (ℝ × ℝ)) := by
    simpa [beltMarks] using hx
  have hmesh := beltMarks_subset_affineMesh o 2 ℓ {z} (by omega) hxmarks
  simpa only [show (2 : ℝ) ^ 2 / 4 = 1 by norm_num] using hmesh

/-- Actual fan-triangle frontiers lie on the prescribed supporting lines.
Auxiliary to area-law Section 11, `prop:two-families`, lines 308–323 and 545–559. -/
private theorem fan_frontier_onSupportingLine (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (hℓ : 1 ≤ ℓ) (i : CellFanSlot split)
    {x : ℝ × ℝ} (hx : x ∈ frontier (cellFanPolygon o ℓ z split i).region) :
    onSupportingLine o x := by
  have hvertices := cellFan_vertices_mem_beltCellMarks o ℓ z split
  have hemesh (j : CellFanSlot split) : cellFanEnd o ℓ z split j ∈ affineMesh o 1 :=
    mark_mem_unitMesh o ℓ z hℓ (hvertices.2 j).2
  rcases cellFanPolygon_frontier_subset_outer_and_radials o ℓ z split i hx with
    hxcell | hxradial
  · exact cell_frontier_onSupportingLine o ℓ z hxcell
  · obtain ⟨j, hxseg⟩ := Set.mem_iUnion.mp hxradial
    rw [segment_symm] at hxseg
    exact segment_onSupportingLine o (hemesh j)
      (cellFanPolygon_base_and_radial_isAllowedSlope o ℓ z split j).2 hxseg

/-- A run boundary is contained in the finite union of its triangle boundaries.
Auxiliary to area-law Section 11, `prop:two-families`, lines 313–323 and 545–559. -/
private theorem run_frontier_onSupportingLine (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (hℓ : 1 ≤ ℓ) (R : CellFanRun o ℓ z split family) {x : ℝ × ℝ}
    (hx : x ∈ frontier (cellFanRunRegion o ℓ z split family R)) :
    onSupportingLine o x := by
  rw [cellFanRunRegion] at hx
  have hfinite : R.supp.Finite := Set.toFinite _
  obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp
    (hfinite.frontier_biUnion_subset (fun i ↦ (cellFanPolygon o ℓ z split i).region) hx)
  exact fan_frontier_onSupportingLine o ℓ z split hℓ i hxi

/-- The dummy boundary comes from the actual finite union of coarse squares.
Auxiliary to area-law Section 11, `prop:two-families`, lines 154–177 and 545–559. -/
private theorem dummy_frontier_onSupportingLine (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ frontier (closure (dyadicNeighborhood o k₀ Z C))) :
    onSupportingLine o x := by
  have hn := frontier_closure_subset hx
  rw [dyadicNeighborhood] at hn
  obtain ⟨z, _, hxz⟩ := Set.mem_iUnion₂.mp
    ((ambientDilation (occupiedCellIndices o k₀ Z) C).frontier_biUnion_subset
      (dyadicCell o k₀) hn)
  exact cell_frontier_onSupportingLine o k₀ z hxz

/-- A primary boundary comes from its exact finite closed-cell decomposition.
Auxiliary to area-law Section 11, `prop:two-families`, lines 212–218,
299–323 and 545–559. -/
private theorem primary_frontier_onSupportingLine (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : Fin (2 ^ (p - ℓ))) (J : ℤ × ℤ)
    (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) {x : ℝ × ℝ}
    (hx : x ∈ frontier (primaryBirthRegion o k ℓ p Z C a.val b.val J)) :
    onSupportingLine o x := by
  classical
  rw [primaryBirthRegion_eq_iUnion_nonbeltCell_closure o k ℓ p Z C a b J hℓk hℓp] at hx
  let F := (fineLayerIndices o k ℓ Z C).filter (fun z ↦
    z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C) (2 ^ (p - ℓ)) a b ∧
      nonbeltPitchIndex ℓ p a.val b.val z = J)
  change x ∈ frontier (⋃ z ∈ F, closure (dyadicCell o ℓ z)) at hx
  obtain ⟨z, _, hxz⟩ := Set.mem_iUnion₂.mp
    (F.frontier_biUnion_subset (fun z ↦ closure (dyadicCell o ℓ z)) hx)
  exact cell_frontier_onSupportingLine o ℓ z (frontier_closure_subset hxz)

/-- The prescribed late layers have integral fine-cell halfsides and midpoints.
Auxiliary to area-law Section 11, `prop:two-families`, lines 200–207 and 545–549. -/
private theorem fineScaleIndex_one_le (k : ℕ) (hk : 50000000 ≤ k) :
    1 ≤ fineScaleIndex k := by
  unfold fineScaleIndex
  apply Nat.le_floor
  have hk' : (50000000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  norm_num [Exponents.zeta, Exponents.geometryDelta]
  linarith

/-- Every actual initial birth boundary has one of the prescribed supporting
lines. Auxiliary to area-law Section 11, `prop:two-families`, lines 545–559. -/
private theorem initial_frontier_onSupportingLine (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex o k₀ Z C a b hC h₀) {x : ℝ × ℝ}
    (hx : x ∈ frontier (initialBirthRegion o k₀ Z C a b hC h₀ i)) :
    onSupportingLine o x := by
  rcases i with u | (⟨k, J⟩ | ⟨k, z, R⟩)
  · exact dummy_frontier_onSupportingLine o k₀ Z C hx
  · exact primary_frontier_onSupportingLine o k.val (fineScaleIndex k.val)
      (pitchScaleIndex k.val) Z C (a k.val) (b k.val) J.val (fineScaleIndex_le k.val)
      ((fineScaleIndex_le k.val).trans (le_pitchScaleIndex k.val)) hx
  · exact run_frontier_onSupportingLine o (fineScaleIndex k.val) z.val
      (fineLayerSplitMask o k₀ k.val Z C z.val)
      (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property)
      (fineScaleIndex_one_le k.val (h₀.trans k.property)) R hx

/-- No integer lattice point lies on an actual initial birth-region boundary
at the prescribed origin. Source: area-law Section 11, `prop:two-families`,
lines 545–559, for the initial construction. -/
theorem initialBirthRegion_frontier_avoid_lattice (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex dyadicOrigin k₀ Z C a b hC h₀) (v : ℤ × ℤ) :
    integerPoint v ∉ frontier (initialBirthRegion dyadicOrigin k₀ Z C a b hC h₀ i) := by
  intro hx
  obtain ⟨m, hm⟩ := initial_frontier_onSupportingLine dyadicOrigin k₀ Z C a b hC h₀ i hx
  have havoid := dyadicOrigin_supporting_lines_avoid_lattice v m
  dsimp [integerPoint] at hm
  rcases hm with hm | hm | hm | hm
  · exact havoid.1 hm
  · exact havoid.2.1 hm
  · exact havoid.2.2.1 hm
  · exact havoid.2.2.2 hm

/-- Initial open-region boundaries also contain no integer lattice point.
Source: area-law Section 11, `prop:two-families`, lines 545–559,
for the initial construction. -/
theorem initialOpenRegion_frontier_avoid_lattice (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex dyadicOrigin k₀ Z C a b hC h₀) (v : ℤ × ℤ) :
    integerPoint v ∉ frontier (initialOpenRegion dyadicOrigin k₀ Z C a b hC h₀ i) := by
  intro hx
  exact initialBirthRegion_frontier_avoid_lattice k₀ Z C a b hC h₀ i v
    (frontier_interior_subset hx)

/-- A lattice point belongs to an actual initial birth region exactly when it
belongs to its initial open interior. Source: area-law Section 11,
`prop:two-families`, lines 545–559, for the initial construction. -/
theorem initialBirthRegion_lattice_mem_iff_initialOpenRegion (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex dyadicOrigin k₀ Z C a b hC h₀) (v : ℤ × ℤ) :
    integerPoint v ∈ initialBirthRegion dyadicOrigin k₀ Z C a b hC h₀ i ↔
      integerPoint v ∈ initialOpenRegion dyadicOrigin k₀ Z C a b hC h₀ i := by
  constructor
  · intro hv
    exact (mem_interior_iff_notMem_frontier hv).mpr
      (initialBirthRegion_frontier_avoid_lattice k₀ Z C a b hC h₀ i v)
  · intro hv
    exact interior_subset hv

end TNLean.PEPS.AreaLaw.Geometry
