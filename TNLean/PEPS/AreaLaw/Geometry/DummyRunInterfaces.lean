/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dummy_fan_polygon_interface
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.fineLayer_cellFanPolygon_inter_dummy_eq
Source labels: prop:two-families
Source: Section 11, lines 154–177 and 299–323.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dummy_belt_run_interface
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.beltCellFanRun_dummy_interface
Source labels: prop:two-families
Source: Section 11, lines 172–174 and 299–323.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BeltFanColors
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.FanSideContacts
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Dummy interfaces of actual belt runs

A fan triangle of an actual fine cell meets the closed initial dummy
neighborhood precisely through its elementary base. This identity holds
for every neighborhood width and optional midpoint subdivision, including
empty and single-point contacts. Actual layer disjointness puts each
contact on a whole square side, where the established own-side identity
reduces the contact to the base.

If an actual belt run and the dummy closure share a nondegenerate segment,
every constituent triangle of the run has the opposite dummy parity.
The shared segment supplies a contact away from the finite set of elementary
endpoints. The open-side continuation theorem extends that contact to the
whole base, and the local color rule and run constancy give the conclusion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177 and 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem mem_side_of_mem_frontier (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (x : ℝ × ℝ) (hx : x ∈ frontier (dyadicCell o ℓ z)) :
    ∃ s : Fin 4, x ∈ dyadicCellSide o ℓ z s := by
  let A := o.1 + (2 : ℝ) ^ ℓ * z.1
  let A' := o.1 + (2 : ℝ) ^ ℓ * (z.1 + 1)
  let B := o.2 + (2 : ℝ) ^ ℓ * z.2
  let B' := o.2 + (2 : ℝ) ^ ℓ * (z.2 + 1)
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  have hA : A < A' := by dsimp [A, A']; linarith
  have hB : B < B' := by dsimp [B, B']; linarith
  have hfront : frontier (dyadicCell o ℓ z) =
      (Set.Icc A A' ×ˢ {B, B'}) ∪ ({A, A'} ×ˢ Set.Icc B B') := by
    change frontier (Set.Ico A A' ×ˢ Set.Ico B B') = _
    rw [frontier_prod_eq, frontier_Ico hB, frontier_Ico hA,
      closure_Ico hA.ne, closure_Ico hB.ne]
  have hcoords (s : Fin 4) := congrArg
    (fun ab : (ℝ × ℝ) × (ℝ × ℝ) ↦ segment ℝ ab.1 ab.2)
    (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  rw [hfront] at hx
  rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩
  · rcases hx₂ with hx₂ | hx₂
    · refine ⟨3, ?_⟩
      have hs := hcoords 3
      norm_num at hs
      rw [dyadicCellSide, hs, ← Prod.image_mk_segment_left, segment_eq_Icc hA.le]
      exact ⟨x.1, hx₁, Prod.ext rfl hx₂.symm⟩
    · refine ⟨1, ?_⟩
      have hs := hcoords 1
      norm_num at hs
      rw [dyadicCellSide, hs, segment_symm, ← Prod.image_mk_segment_left,
        segment_eq_Icc hA.le]
      exact ⟨x.1, hx₁, Prod.ext rfl hx₂.symm⟩
  · rcases hx₁ with hx₁ | hx₁
    · refine ⟨2, ?_⟩
      have hs := hcoords 2
      norm_num at hs
      rw [dyadicCellSide, hs, segment_symm, ← Prod.image_mk_segment_right,
        segment_eq_Icc hB.le]
      exact ⟨x.2, hx₂, Prod.ext hx₁.symm rfl⟩
    · refine ⟨0, ?_⟩
      have hs := hcoords 0
      norm_num at hs
      rw [dyadicCellSide, hs, ← Prod.image_mk_segment_right, segment_eq_Icc hB.le]
      exact ⟨x.2, hx₂, Prod.ext hx₁.symm rfl⟩

/-- A fan triangle of an actual later fine cell meets the dummy closure exactly
where its elementary base does. The neighborhood width and optional midpoint
subdivision are arbitrary, and empty or singleton contacts are included.
Source: area-law Section 11, `prop:two-families`, lines 154–177 and 299–323. -/
theorem fineLayer_cellFanPolygon_inter_dummy_eq
    (o : ℝ × ℝ) (k₀ k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hk₀ : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    (cellFanPolygon o (fineScaleIndex k) z split i).region ∩
        closure (dyadicNeighborhood o k₀ Z C) =
      segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
          (cellFanEnd o (fineScaleIndex k) z split i) ∩
        closure (dyadicNeighborhood o k₀ Z C) := by
  have href := dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
    (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz
  have hd := (dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk₀).symm.mono_left href
  have hclosed := (hd.mono_left interior_subset).closure_right isOpen_interior
  apply Set.Subset.antisymm
  · intro x hx
    have hxcell : x ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
      (cellFanPolygons_cover o (fineScaleIndex k) z split) ▸
        Set.mem_iUnion.mpr ⟨i, hx.1⟩
    have hxfront : x ∈ frontier (dyadicCell o (fineScaleIndex k) z) := by
      rw [← closure_sdiff_interior]
      exact ⟨hxcell, fun hi ↦ Set.disjoint_left.mp hclosed hi hx.2⟩
    obtain ⟨s, hs⟩ := mem_side_of_mem_frontier o (fineScaleIndex k) z x hxfront
    have hface := cellFanPolygon_inter_dyadicCellSide o (fineScaleIndex k) z split i s
    exact ⟨((Set.ext_iff.mp hface x).mp ⟨hx.1, hs⟩).1, hx.2⟩
  · intro x hx
    have hjoin : convexJoin ℝ {cellFanCenter o (fineScaleIndex k) z}
        (segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
          (cellFanEnd o (fineScaleIndex k) z split i)) =
        (cellFanPolygon o (fineScaleIndex k) z split i).region :=
      convexJoin_singleton_segment _ _ _
    exact ⟨hjoin ▸ subset_convexJoin_right (Set.singleton_nonempty _) hx.1, hx.2⟩

/-- A nondegenerate segment shared by an actual belt run and the dummy closure
forces every constituent triangle to have the opposite dummy parity.
Source: area-law Section 11, `prop:two-families`, lines 172–174 and 299–323. -/
theorem beltCellFanRun_dummy_interface
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k : ℕ) (z : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      closure (dyadicNeighborhood o k₀ Z C)) :
    ∀ i ∈ R.supp, beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i =
        ((k₀ - 1 : ℕ) : Fin 2) + 1 ∧
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠
        ((k₀ - 1 : ℕ) : Fin 2) := by
  classical
  let split := fineLayerSplitMask o k₀ k Z C z
  let endpoints := ⋃ i : CellFanSlot split,
    ({cellFanStart o (fineScaleIndex k) z split i,
      cellFanEnd o (fineScaleIndex k) z split i} : Set (ℝ × ℝ))
  have hfinite : endpoints.Finite :=
    Set.finite_iUnion fun _ ↦ (Set.finite_singleton _).insert _
  have hinfinite : (segment ℝ u v).Infinite := by
    rw [segment_eq_image_lineMap]
    exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      (AffineMap.lineMap_injective ℝ huv).injOn
  obtain ⟨x, hxS, hxends⟩ := hinfinite.exists_notMem_finite hfinite
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hsegment hxS).1
  have hxN := (hsegment hxS).2
  have hxbase : x ∈ segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
      (cellFanEnd o (fineScaleIndex k) z split i) := by
    have hface := fineLayer_cellFanPolygon_inter_dummy_eq o k₀ k Z C z split i
      hk₀ (Finset.mem_of_mem_filter z hz)
    exact ((Set.ext_iff.mp hface x).mp ⟨hxi, hxN⟩).1
  have hxne (he : x = cellFanStart o (fineScaleIndex k) z split i ∨
      x = cellFanEnd o (fineScaleIndex k) z split i) : False := by
    apply hxends
    exact Set.mem_iUnion.mpr ⟨i, he⟩
  have hxopen := mem_openSegment_of_ne_left_right
    (fun he ↦ hxne (Or.inl he.symm)) (fun he ↦ hxne (Or.inr he.symm)) hxbase
  have hwhole := fineLayer_elementarySide_subset_dummy_of_mem_openSegment
    o k₀ k Z C z split i x hC hk₀ (Finset.mem_of_mem_filter z hz) hxopen hxN
  have hcolor := beltCellFanColor_dummy o k₀ Z C a b k z hC h₀ hk₀ hz i hwhole
  intro j hj
  have hsame := cellFanRun_color_eq o (fineScaleIndex k) z split
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) j i
    (SimpleGraph.ConnectedComponent.eq.mpr (R.reachable_of_mem_supp hj hi))
  exact ⟨hsame.trans hcolor.1, hsame.symm ▸ hcolor.2⟩

end TNLean.PEPS.AreaLaw.Geometry
