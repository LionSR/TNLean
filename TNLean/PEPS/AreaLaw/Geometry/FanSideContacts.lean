/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellContacts
import TNLean.PEPS.AreaLaw.Geometry.ElementarySideOpponents
import Mathlib.Analysis.Convex.Topology

/-!
# Contacts of fan triangles along cell sides

A fan triangle meets any whole side of its own square only along its
elementary base. More generally, its intersection with the closure of a
distinct actual fine cell equals the intersection of its elementary base
with that closure. These equalities include empty and singleton contacts.
They hold for every origin, natural scale, integer cell index, optional
midpoint subdivision, and neighborhood width.

The center lies in the interior of the half-open square. Convexity places
every point of a fan triangle away from its base in that interior. Actual
half-open cell disjointness then excludes contact with the closure of any
distinct actual cell. No late-scale or positive-contact assumption is needed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 299–323, `prop:two-families`.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem convexJoin_subset_base_union_interior
    (Q S : Set (ℝ × ℝ)) (c : ℝ × ℝ) (hQ : Convex ℝ Q)
    (hc : c ∈ interior Q) (hS : S ⊆ closure Q) :
    convexJoin ℝ {c} S ⊆ S ∪ interior Q := by
  intro x hx
  obtain ⟨a, ha, u, hu, hseg⟩ := mem_convexJoin.mp hx
  have ha' : a = c := ha
  subst a
  by_cases hxu : x = u
  · exact Or.inl (hxu.symm ▸ hu)
  by_cases hxc : x = c
  · exact Or.inr (hxc.symm ▸ hc)
  exact Or.inr (hQ.openSegment_interior_closure_subset_interior hc (hS hu)
    (mem_openSegment_of_ne_left_right (Ne.symm hxc) (Ne.symm hxu) hseg))

private theorem center_mem_interior (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    cellFanCenter o ℓ z ∈ interior (dyadicCell o ℓ z) := by
  rw [dyadicCell, interior_prod_eq, interior_Ico, interior_Ico]
  have ht : 0 < (2 : ℝ) ^ ℓ := by positivity
  simp only [Set.mem_prod, Set.mem_Ioo, cellFanCenter]
  constructor <;> constructor <;> linarith

private theorem fan_inter_eq_of_disjoint_interior
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) (split : Fin 4 → Bool)
    (i : CellFanSlot split) (T : Set (ℝ × ℝ))
    (hT : Disjoint (interior (dyadicCell o ℓ z)) T) :
    (cellFanPolygon o ℓ z split i).region ∩ T =
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩ T := by
  have hjoin : convexJoin ℝ {cellFanCenter o ℓ z}
      (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i)) =
      (cellFanPolygon o ℓ z split i).region :=
    convexJoin_singleton_segment _ _ _
  have hbase : segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      (cellFanPolygon o ℓ z split i).region := by
    rw [← hjoin]
    exact subset_convexJoin_right (Set.singleton_nonempty _)
  have hclosed : segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ⊆
      closure (dyadicCell o ℓ z) := fun x hx ↦
    (cellFanPolygons_cover o ℓ z split) ▸ (Set.mem_iUnion.mpr ⟨i, hbase hx⟩)
  have hQ : Convex ℝ (dyadicCell o ℓ z) := by
    unfold dyadicCell
    exact (convex_Ico _ _).prod (convex_Ico _ _)
  have hboundary := convexJoin_subset_base_union_interior (dyadicCell o ℓ z)
    (segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i))
    (cellFanCenter o ℓ z) hQ (center_mem_interior o ℓ z) hclosed
  rw [hjoin] at hboundary
  apply Set.Subset.antisymm
  · intro x hx
    rcases hboundary hx.1 with hb | hi
    · exact ⟨hb, hx.2⟩
    · exact False.elim (Set.disjoint_left.mp hT hi hx.2)
  · exact fun _ hx ↦ ⟨hbase hx.1, hx.2⟩

private theorem whole_side_disjoint_interior (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (s : Fin 4) :
    Disjoint (interior (dyadicCell o ℓ z)) (dyadicCellSide o ℓ z s) := by
  apply Set.disjoint_left.mpr
  intro x hx hs
  let a := cellFanStart o ℓ z (fun _ ↦ false) ⟨s, 0⟩
  let b := cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩
  let p := dyadicCellCorner o ℓ z (0, 0)
  let q := dyadicCellCorner o ℓ z (1, 1)
  have hx' : (p.1 < x.1 ∧ x.1 < q.1) ∧ (p.2 < x.2 ∧ x.2 < q.2) := by
    simpa [p, q, dyadicCellCorner, dyadicCell, interior_prod_eq, interior_Ico] using hx
  have hseg : x ∈ segment ℝ a b := hs
  have hcoords := Prod.segment_subset (𝕜 := ℝ) a b hseg
  have haxis : (a.1 = b.1 ∧ (a.1 = p.1 ∨ a.1 = q.1)) ∨
      (a.2 = b.2 ∧ (a.2 = p.2 ∨ a.2 = q.2)) :=
    (cellFan_elementary_geometry o ℓ z (fun _ ↦ false) ⟨s, 0⟩).2
  rcases haxis with
    ⟨he, hboundary⟩ | ⟨he, hboundary⟩
  · have hxcoord : x.1 = a.1 := by
      simpa only [← he, segment_same, Set.mem_singleton_iff] using hcoords.1
    rcases hboundary with hboundary | hboundary <;> linarith [hx'.1.1, hx'.1.2]
  · have hxcoord : x.2 = a.2 := by
      simpa only [← he, segment_same, Set.mem_singleton_iff] using hcoords.2
    rcases hboundary with hboundary | hboundary <;> linarith [hx'.2.1, hx'.2.2]

/-- A fan triangle meets every whole side of its own square precisely where its
elementary base meets that side. All optional midpoint subdivisions are allowed.
Source: area-law Section 11, lines 299–323, `prop:two-families`. -/
theorem cellFanPolygon_inter_dyadicCellSide
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i : CellFanSlot split) (s : Fin 4) :
    (cellFanPolygon o ℓ z split i).region ∩ dyadicCellSide o ℓ z s =
      segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i) ∩
        dyadicCellSide o ℓ z s := by
  exact fan_inter_eq_of_disjoint_interior o ℓ z split i _
    (whole_side_disjoint_interior o ℓ z s)

/-- The intersection of a fan triangle with a distinct actual fine-cell closure
is exactly the intersection of its elementary base with that closure. This holds
at all layers and widths, including empty and singleton contacts.
Source: area-law Section 11, lines 299–323, `prop:two-families`. -/
theorem fineLayer_cellFanPolygon_inter_closedCell_eq
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z w : ℤ × ℤ) (split : Fin 4 → Bool) (i : CellFanSlot split)
    (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : w ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : (k, z) ≠ (h, w)) :
    (cellFanPolygon o (fineScaleIndex k) z split i).region ∩
        closure (dyadicCell o (fineScaleIndex h) w) =
      segment ℝ (cellFanStart o (fineScaleIndex k) z split i)
          (cellFanEnd o (fineScaleIndex k) z split i) ∩
        closure (dyadicCell o (fineScaleIndex h) w) := by
  apply fan_inter_eq_of_disjoint_interior
  exact ((fineLayer_cells_disjoint o k h Z C z w hz hw hne).mono_left
    interior_subset).closure_right isOpen_interior

end TNLean.PEPS.AreaLaw.Geometry
