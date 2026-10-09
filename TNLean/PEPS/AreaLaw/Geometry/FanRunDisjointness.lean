/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanCycle
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts

/-!
# Disjointness of retained fan runs

Removing the radial segments across which the family changes separates the
regions of distinct runs in the actual all-midpoint fan. The assertion holds
before restricting to a ball. The change set may be empty, and distinct runs
of one colour remain distinct.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–370,
and `prop:two-families`, lines 313–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Removing precisely the radials at changes of family makes the regions of
distinct actual midpoint-fan runs disjoint. The change set is defined from the
family, rather than supplied as a geometric hypothesis. This statement precedes
restriction to a ball and includes the case of an empty change set.

Auxiliary to OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, `geometry:initial-stars`, lines 352–370, and `prop:two-families`,
lines 313–323, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/
theorem cellFanRunRegion_sdiff_radials_pairwise_disjoint
    (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (family : CellFanSlot (fun _ : Fin 4 ↦ true) → Fin 2) :
    let A : Set (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
      {t | family t ≠ family (cellFanNext t)}
    let K : Set (ℝ × ℝ) :=
      ⋃ t ∈ A, segment ℝ (cellFanCenter o ℓ z)
        (cellFanEnd o ℓ z (fun _ ↦ true) t)
    Pairwise (fun R T : CellFanRun o ℓ z (fun _ ↦ true) family ↦
      Disjoint (cellFanRunRegion o ℓ z (fun _ ↦ true) family R \ K)
        (cellFanRunRegion o ℓ z (fun _ ↦ true) family T \ K)) := by
  classical
  intro A K R T hRT
  apply Set.disjoint_left.mpr
  intro x hxR hxT
  obtain ⟨i, hiR, hxi⟩ := Set.mem_iUnion₂.mp hxR.1
  obtain ⟨j, hjT, hxj⟩ := Set.mem_iUnion₂.mp hxT.1
  let G := cellFanRunGraph o ℓ z (fun _ ↦ true) family
  have hi : G.connectedComponentMk i = R :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff R i).mp hiR
  have hj : G.connectedComponentMk j = T :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff T j).mp hjT
  have hcomponents : G.connectedComponentMk i ≠ G.connectedComponentMk j :=
    fun h ↦ hRT ((hi.symm.trans h).trans hj)
  have hij : i ≠ j := ne_of_apply_ne G.connectedComponentMk hcomponents
  by_cases hxc : x = cellFanCenter o ℓ z
  · have hnext : ∀ s : CellFanSlot (fun _ : Fin 4 ↦ true),
        family s = family (cellFanNext s) := by
      intro s
      by_contra hchange
      apply hxR.2
      rw [hxc]
      exact Set.mem_iUnion₂.mpr ⟨s, hchange,
        left_mem_segment ℝ (cellFanCenter o ℓ z)
          (cellFanEnd o ℓ z (fun _ ↦ true) s)⟩
    let G₀ := cellFanRunGraph o ℓ z (fun _ ↦ true) (fun _ ↦ (0 : Fin 2))
    have hle : G₀ ≤ G := by
      intro s t h
      refine ⟨h.1, h.2.1, ?_⟩
      rcases h.2.1 with hst | hts
      · have ht := (cellFanEnd_eq_cellFanStart_iff o ℓ z s t).mp hst
        simpa only [ht] using hnext s
      · have hs := (cellFanEnd_eq_cellFanStart_iff o ℓ z t s).mp hts
        simpa only [hs] using (hnext t).symm
    have hconstant :=
      (cellFanRun_all_equal o ℓ z (fun _ ↦ true)
        (fun _ ↦ (0 : Fin 2)) (fun _ _ ↦ rfl)).1
    exact hcomponents
      (SimpleGraph.ConnectedComponent.sound
        ((SimpleGraph.ConnectedComponent.exact (hconstant i j)).mono hle))
  · have hc : cellFanCenter o ℓ z ∈
        (cellFanPolygon o ℓ z (fun _ ↦ true) i).region ∩
          (cellFanPolygon o ℓ z (fun _ ↦ true) j).region :=
      (cellFanPolygons_inter_eq o ℓ z (fun _ ↦ true) i j).symm ▸ Or.inl rfl
    have hcontact : ((cellFanPolygon o ℓ z (fun _ ↦ true) i).region ∩
        (cellFanPolygon o ℓ z (fun _ ↦ true) j).region).Nontrivial :=
      Set.nontrivial_of_mem_mem_ne ⟨hxi, hxj⟩ hc hxc
    rcases cellFanPolygons_nontrivial_inter_cases o ℓ z (fun _ ↦ true)
        i j hij hcontact with ⟨hadj, hinter⟩ | ⟨hadj, hinter⟩
    · have hcolors := cellFanRun_adjacent_colors_ne o ℓ z (fun _ ↦ true)
        family i j (Or.inl hadj) hcomponents
      have hjnext := (cellFanEnd_eq_cellFanStart_iff o ℓ z i j).mp hadj
      have hiA : i ∈ A := by
        simpa only [A, Set.mem_ofPred_eq, ← hjnext] using hcolors
      exact hxR.2 (Set.mem_iUnion₂.mpr ⟨i, hiA, hinter ▸ ⟨hxi, hxj⟩⟩)
    · have hcolors := cellFanRun_adjacent_colors_ne o ℓ z (fun _ ↦ true)
        family j i (Or.inl hadj) (Ne.symm hcomponents)
      have hinext := (cellFanEnd_eq_cellFanStart_iff o ℓ z j i).mp hadj
      exact hxR.2 (Set.mem_iUnion₂.mpr ⟨j,
        (by simpa only [A, Set.mem_ofPred_eq, ← hinext] using hcolors),
        hinter ▸ ⟨hxi, hxj⟩⟩)


end TNLean.PEPS.AreaLaw.Geometry
