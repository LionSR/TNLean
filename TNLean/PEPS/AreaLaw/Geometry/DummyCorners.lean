/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DummyContacts
import TNLean.PEPS.AreaLaw.Geometry.SideSubdivisionMask
import TNLean.PEPS.AreaLaw.Geometry.SideEndpoints
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Dummy-neighborhood corners on fine-cell sides

A corner of a coarse cell contributing to the initial dummy neighborhood
can lie on a side of an actual later fine cell only at a side endpoint.
The common point forces the reference layer to be the initial layer.
The coarse corner and both side endpoints then lie on the full fine mesh.
The same endpoint conclusion holds for every optional midpoint subdivision.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 160–191, 200–207 and 299–310.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/10-geometry.tex
Labels: prop:two-families; geometry:layer-distance.
Source lines: 160–191; 200–207; 299–310.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicneighborhood_corner_on_side
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_side
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicneighborhood_corner_on_elementaryside
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_corner_on_elementarySide
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem mesh_segment_endpoints {o : ℝ × ℝ} {q : ℝ}
    (hq : 0 < q) {a b x : ℝ × ℝ}
    (ha : a ∈ affineMesh o q) (hb : b ∈ affineMesh o q) (hx : x ∈ affineMesh o q)
    (hseg : x ∈ segment ℝ a b) (hlen : dist a b ≤ q) : x = a ∨ x = b := by
  by_contra! hne
  have hax := affineMesh_dist_ge hq ha hx hne.1.symm
  have hxb := affineMesh_dist_ge hq hx hb hne.2
  have hsum := dist_add_dist_of_mem_segment hseg
  linarith

private theorem corner_mem_fullMesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (w : ℤ × ℤ) (ε : Fin 2 × Fin 2) (hℓj : ℓ ≤ j) :
    dyadicCellCorner o j w ε ∈ affineMesh o ((2 : ℝ) ^ ℓ) := by
  have hp : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (j - ℓ) = (2 : ℝ) ^ j := by
    rw [← pow_add, Nat.add_sub_of_le hℓj]
  refine ⟨((2 : ℤ) ^ (j - ℓ) * (w.1 + ε.1.val),
    (2 : ℤ) ^ (j - ℓ) * (w.2 + ε.2.val)), ?_⟩
  apply Prod.ext <;> dsimp [integerPoint, dyadicCellCorner] <;>
    push_cast <;> rw [← mul_assoc, hp]

private theorem whole_endpoints_mem_fullMesh (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (s : Fin 4) :
    cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ∈ affineMesh o ((2 : ℝ) ^ ℓ) ∧
      cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ ∈ affineMesh o ((2 : ℝ) ^ ℓ) := by
  obtain ⟨ε, η, ha, hb⟩ := cellFan_unsplit_endpoints_are_corners o ℓ z s
  rw [ha, hb]
  exact ⟨corner_mem_fullMesh o ℓ ℓ z ε le_rfl,
    corner_mem_fullMesh o ℓ ℓ z η le_rfl⟩

private theorem corner_mem_closure (o : ℝ × ℝ) (j : ℕ)
    (w : ℤ × ℤ) (ε : Fin 2 × Fin 2) :
    dyadicCellCorner o j w ε ∈ closure (dyadicCell o j w) := by
  have hbound (a : ℝ) (v : ℤ) (e : Fin 2) :
      a + (2 : ℝ) ^ j * ((v : ℝ) + e.val) ∈
        Set.Icc (a + (2 : ℝ) ^ j * v) (a + (2 : ℝ) ^ j * (v + 1)) := by
    have he0 : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
    have he1 : (e.val : ℝ) ≤ 1 := by exact_mod_cast (show e.val ≤ 1 by omega)
    have ht : 0 < (2 : ℝ) ^ j := by positivity
    constructor <;> nlinarith
  rw [closure_dyadicCell]
  exact ⟨hbound o.1 w.1 ε.1, hbound o.2 w.2 ε.2⟩

/-- A corner of an actual coarse cell contributing to the dummy neighborhood
on a whole actual fine-cell side is a side endpoint.
Source: area-law Section 11, lines 160–191, 200–207 and 299–310. -/
theorem dyadicNeighborhood_corner_on_side (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (s : Fin 4)
    (ε : Fin 2 × Fin 2) (hC : 2 ≤ C) (hk : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ ambientDilation (occupiedCellIndices o k₀ Z) C)
    (hside : dyadicCellCorner o k₀ w ε ∈ segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)
      (cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩)) :
    dyadicCellCorner o k₀ w ε =
        cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩ ∨
      dyadicCellCorner o k₀ w ε =
        cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨s, 0⟩ := by
  let x := dyadicCellCorner o k₀ w ε
  have hdummyCell : dyadicCell o k₀ w ⊆ dyadicNeighborhood o k₀ Z C := by
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩
  have hxN := closure_mono hdummyCell (corner_mem_closure o k₀ w ε)
  have hv := (cellFan_vertices_mem_beltCellMarks o (fineScaleIndex k) z
    (fun _ ↦ false)).2 ⟨s, 0⟩
  have ha := beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv.1
  have hb := beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv.2
  have hc : Convex ℝ (closure (dyadicCell o (fineScaleIndex k) z)) := by
    rw [closure_dyadicCell]
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hxCell := hc.segment_subset ha hb hside
  have hxD := closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices
    o k (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz) hxCell
  have he := dyadicNeighborhood_contact_layer_eq o k₀ k Z C x hC hk hxN hxD
  subst k
  obtain ⟨haM, hbM⟩ := whole_endpoints_mem_fullMesh o (fineScaleIndex k₀) z s
  have hxM := corner_mem_fullMesh o (fineScaleIndex k₀) k₀ w ε (fineScaleIndex_le k₀)
  have hlen := dyadicCell_dist_le o (fineScaleIndex k₀) z z 0
    (cellFanStart o (fineScaleIndex k₀) z (fun _ ↦ false) ⟨s, 0⟩)
    (cellFanEnd o (fineScaleIndex k₀) z (fun _ ↦ false) ⟨s, 0⟩) ha hb (by simp)
  exact mesh_segment_endpoints (by positivity) haM hbM hxM hside (by simpa using hlen)

/-- A contributing dummy-cell corner on any optional elementary side segment
of an actual fine-layer cell is an endpoint of that segment.
Source: area-law Section 11, lines 160–191, 200–207 and 299–310. -/
theorem dyadicNeighborhood_corner_on_elementarySide (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z w : ℤ × ℤ) (split : Fin 4 → Bool)
    (i : CellFanSlot split) (ε : Fin 2 × Fin 2) (hC : 2 ≤ C) (hk : k₀ ≤ k)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ ambientDilation (occupiedCellIndices o k₀ Z) C)
    (hside : dyadicCellCorner o k₀ w ε ∈ segment ℝ
      (cellFanStart o (fineScaleIndex k) z split i)
      (cellFanEnd o (fineScaleIndex k) z split i)) :
    dyadicCellCorner o k₀ w ε = cellFanStart o (fineScaleIndex k) z split i ∨
      dyadicCellCorner o k₀ w ε = cellFanEnd o (fineScaleIndex k) z split i := by
  have hwhole := cellFan_elementary_segment_subset_whole o (fineScaleIndex k) z split i hside
  have he := dyadicNeighborhood_corner_on_side o k₀ k Z C z w i.1 ε hC hk hz hw hwhole
  rcases cellFan_elementary_endpoints_cases o (fineScaleIndex k) z split i with ⟨_, ha, hb⟩ |
    ⟨_, ha, hm⟩ | ⟨_, hm, hb⟩
  · rwa [ha, hb]
  · rw [ha, hm] at hside ⊢
    rcases he with hx | hx
    · exact Or.inl hx
    · by_cases hab : cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩ =
          cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩
      · exact Or.inl (hx.trans hab.symm)
      · exact False.elim ((sbtw_midpoint_of_ne ℝ hab).not_swap_right
          (mem_segment_iff_wbtw.mp (hx ▸ hside)))
  · rw [hm, hb] at hside ⊢
    rcases he with hx | hx
    · by_cases hab : cellFanStart o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩ =
          cellFanEnd o (fineScaleIndex k) z (fun _ ↦ false) ⟨i.1, 0⟩
      · exact Or.inr (hx.trans hab)
      · exact False.elim ((sbtw_midpoint_of_ne ℝ hab).not_swap_left
          (mem_segment_iff_wbtw.mp (hx ▸ hside)))
    · exact Or.inr hx

end TNLean.PEPS.AreaLaw.Geometry
