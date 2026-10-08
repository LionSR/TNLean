/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.fan_run_disjoint_interiors
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_disjoint_interiors
Source labels: prop:two-families
Source: Section 11, lines 313–323.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.initial_open_region_disjoint
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion_pairwise_disjoint
Source labels: prop:two-families
Source: Section 11, lines 154–177, 212–218 and 299–323.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFineCellCover
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.GDelta.Basic

/-!
# Disjoint interiors of initial birth regions

Distinct runs of one fan have disjoint interiors: each pair of constituent
triangles meets only in a radial segment or the common center, and the finite
union of these planar sets has empty interior. For different actual cells,
half-open cell disjointness and density of the square interior justify taking
closures. The finite closed-cell decomposition of primaries then gives
pairwise disjointness of all initial open regions.

The endpoint set and residue functions are arbitrary. No nonemptiness, contact,
finite support, or partition hypothesis is imposed. These are the initial
regions before repairs; lattice coverage and repaired regions are separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, prop:two-families, lines 154–177,
212–218 and 299–323.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A planar segment is nowhere dense.
Auxiliary to Section 11, prop:two-families, lines 308–323. -/
private theorem segment_nowhereDense (u v : ℝ × ℝ) :
    IsNowhereDense (segment ℝ u v) := by
  have hfinite : ({u, v} : Set (ℝ × ℝ)).Finite :=
    (Set.finite_singleton v).insert u
  have hclosed : IsClosed (segment ℝ u v) := by
    rw [← convexHull_pair]
    exact hfinite.isClosed_convexHull ℝ
  apply hclosed.isNowhereDense_iff.mpr
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  have hspan : affineSpan ℝ ({u, v} : Set (ℝ × ℝ)) = ⊤ := by
    apply affineSpan_eq_top_of_nonempty_interior
    simpa only [convexHull_pair] using h
  have hcard : ({u, v} : Set (ℝ × ℝ)).encard ≤
      (Module.finrank ℝ (ℝ × ℝ) : ℕ) := by
    calc
      _ ≤ ({v} : Set (ℝ × ℝ)).encard + 1 := Set.encard_insert_le _ _
      _ = _ := by norm_num
  have hproper : affineSpan ℝ ({u, v} : Set (ℝ × ℝ)) ≠ ⊤ := by
    simpa only [Set.image_id] using
      affineSpan_image_ne_top_of_encard_le_finrank ℝ hfinite hcard
        (id : (ℝ × ℝ) → (ℝ × ℝ))
  exact hproper hspan

/-- Distinct fan triangles have a nowhere dense intersection.
Source: Section 11, prop:two-families, lines 308–323. -/
private theorem triangle_inter_nowhereDense (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (i j : CellFanSlot split) (hij : i ≠ j) :
    IsNowhereDense ((cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region) := by
  by_cases hc : ((cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region).Nontrivial
  · rcases cellFanPolygons_nontrivial_inter_cases o ℓ z split i j hij hc with h | h
    · rw [h.2]
      exact segment_nowhereDense _ _
    · rw [h.2]
      exact segment_nowhereDense _ _
  · have hs := Set.not_nontrivial_iff.mp hc
    have hcenter : cellFanCenter o ℓ z ∈
        (cellFanPolygon o ℓ z split i).region ∩
          (cellFanPolygon o ℓ z split j).region := by
      rw [cellFanPolygons_inter_eq]
      exact Or.inl rfl
    apply (segment_nowhereDense (cellFanCenter o ℓ z) (cellFanCenter o ℓ z)).mono
    intro x hx
    simpa only [segment_same, Set.mem_singleton_iff] using hs hx hcenter

/-- Distinct runs in one fan have disjoint interiors for every midpoint mask
and every assignment of two colors.
Source: Section 11, prop:two-families, lines 313–323. -/
theorem cellFanRunRegions_disjoint_interiors (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R T : CellFanRun o ℓ z split family) (hRT : R ≠ T) :
    Disjoint (interior (cellFanRunRegion o ℓ z split family R))
      (interior (cellFanRunRegion o ℓ z split family T)) := by
  classical
  let I := {i : CellFanSlot split // i ∈ R.supp}
  let J := {j : CellFanSlot split // j ∈ T.supp}
  let F (q : I × J) := (cellFanPolygon o ℓ z split q.1.val).region ∩
    (cellFanPolygon o ℓ z split q.2.val).region
  have hf : ∀ q, IsNowhereDense (F q) := by
    intro q
    apply triangle_inter_nowhereDense
    intro he
    have hi := (SimpleGraph.ConnectedComponent.mem_supp_iff R q.1.val).mp q.1.property
    have hj := (SimpleGraph.ConnectedComponent.mem_supp_iff T q.2.val).mp q.2.property
    exact hRT (hi.symm.trans ((congrArg
      (cellFanRunGraph o ℓ z split family).connectedComponentMk he).trans hj))
  have hsub : cellFanRunRegion o ℓ z split family R ∩
      cellFanRunRegion o ℓ z split family T ⊆ ⋃ q, F q := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx.1
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx.2
    exact Set.mem_iUnion.mpr ⟨(⟨i, hi⟩, ⟨j, hj⟩), hxi, hxj⟩
  have hthin := (IsNowhereDense.iUnion hf).mono hsub
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [← interior_inter]
  exact Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans
    (by rw [hthin]))

/-- The interior of a half-open dyadic square is dense in its closure.
Auxiliary to Section 11, prop:two-families, lines 154–177 and 299–306. -/
private theorem cell_closure_interior (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (interior (dyadicCell o ℓ z)) = closure (dyadicCell o ℓ z) := by
  have hconv : Convex ℝ (dyadicCell o ℓ z) := by
    unfold dyadicCell
    exact (convex_Ico _ _).prod (convex_Ico _ _)
  have hlt (v : ℝ) (j : ℤ) :
      v + (2 : ℝ) ^ ℓ * j < v + (2 : ℝ) ^ ℓ * (j + 1) := by
    simpa only [add_comm] using add_lt_add_left
      (mul_lt_mul_of_pos_left (lt_add_one (j : ℝ)) (pow_pos zero_lt_two ℓ)) v
  apply hconv.closure_interior_eq_closure_of_nonempty_interior
  rw [dyadicCell, interior_prod_eq, interior_Ico, interior_Ico]
  exact (Set.nonempty_Ioo.mpr (hlt o.1 z.1)).prod
    (Set.nonempty_Ioo.mpr (hlt o.2 z.2))

/-- Two open-set closure steps preserve disjointness with an open interior.
Auxiliary to Section 11, prop:two-families, lines 154–177 and 212–218. -/
private theorem closure_disjoint_interior_union {ι : Type*}
    (S : Set (ℝ × ℝ)) (T : ι → Set (ℝ × ℝ))
    (hS : closure (interior S) = closure S) (hd : ∀ i, Disjoint S (T i)) :
    Disjoint (closure S) (interior (⋃ i, closure (T i))) := by
  have hi : Disjoint (interior S) (⋃ i, closure (T i)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp
      (((hd i).mono_left interior_subset).closure_right isOpen_interior) hx hxi
  have h := (hi.mono_right interior_subset).closure_left isOpen_interior
  simpa only [hS] using h

/-- Unions of closures of distinct actual indexed fine cells have disjoint interiors.
Source: Section 11, prop:two-families, lines 154–177 and 299–306. -/
private theorem fineCellUnions_disjoint_interiors {ι κ : Type*}
    (o : ℝ × ℝ) (k h : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (z : ι → ℤ × ℤ) (w : κ → ℤ × ℤ)
    (hz : ∀ i, z i ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (hw : ∀ j, w j ∈ fineLayerIndices o h (fineScaleIndex h) Z C)
    (hne : ∀ i j, (k, z i) ≠ (h, w j)) :
    Disjoint (interior (⋃ i, closure (dyadicCell o (fineScaleIndex k) (z i))))
      (interior (⋃ j, closure (dyadicCell o (fineScaleIndex h) (w j)))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (interior_subset hx)
  have hd := closure_disjoint_interior_union
    (dyadicCell o (fineScaleIndex k) (z i))
    (fun j ↦ dyadicCell o (fineScaleIndex h) (w j))
    (cell_closure_interior o (fineScaleIndex k) (z i))
    (fun j ↦ fineLayer_cells_disjoint o k h Z C (z i) (w j) (hz i) (hw j) (hne i j))
  exact Set.disjoint_left.mp hd hxi hy

/-- The actual nonbelt cells with one prescribed primary index.
Source: Section 11, prop:two-families, lines 212–218 and 299–323. -/
private def primaryCells (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))) (J : ℤ × ℤ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (fineLayerIndices o k (fineScaleIndex k) Z C).filter (fun z ↦
    z ∉ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) a b ∧
    nonbeltPitchIndex (fineScaleIndex k) (pitchScaleIndex k) a.val b.val z = J)

/-- The verified primary decomposition, indexed by its actual filtered cells.
Source: Section 11, prop:two-families, lines 212–218 and 299–323. -/
private theorem primary_eq_union (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))) (J : ℤ × ℤ) :
    primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k) Z C a.val b.val J =
      ⋃ z : {z // z ∈ primaryCells o k Z C a b J},
        closure (dyadicCell o (fineScaleIndex k) z.val) := by
  rw [primaryBirthRegion_eq_iUnion_nonbeltCell_closure o k
    (fineScaleIndex k) (pitchScaleIndex k) Z C a b J (fineScaleIndex_le k)
    ((fineScaleIndex_le k).trans (le_pitchScaleIndex k))]
  exact Set.biUnion_eq_iUnion (primaryCells o k Z C a b J : Set (ℤ × ℤ)) _

/-- An actual run is contained in its actual closed cell.
Source: Section 11, prop:two-families, lines 308–316. -/
private theorem run_subset_cellClosure (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2)
    (R : CellFanRun o ℓ z split family) :
    cellFanRunRegion o ℓ z split family R ⊆ closure (dyadicCell o ℓ z) := by
  intro x hx
  rw [← cellFanRunRegions_cover o ℓ z split family]
  exact Set.mem_iUnion.mpr ⟨R, hx⟩

/-- The dummy interior is disjoint from any later actual fine-cell closure.
Source: Section 11, prop:two-families, lines 154–177. -/
private theorem dummy_cell_interiors (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (z : ℤ × ℤ)
    (hk : k₀ ≤ k) (hz : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C) :
    Disjoint (interior (closure (dyadicNeighborhood o k₀ Z C)))
      (closure (dyadicCell o (fineScaleIndex k) z)) := by
  have hd : Disjoint (dyadicCell o (fineScaleIndex k) z)
      (dyadicNeighborhood o k₀ Z C) :=
    (dyadicNeighborhood_disjoint_later_layer o Z C k₀ k hk).symm.mono_left
      (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k
        (fineScaleIndex k) Z C z (fineScaleIndex_le k) hz)
  have h := closure_disjoint_interior_union (dyadicCell o (fineScaleIndex k) z)
    (fun _ : Unit ↦ dyadicNeighborhood o k₀ Z C)
    (cell_closure_interior o (fineScaleIndex k) z) (fun _ ↦ hd)
  simpa only [Set.iUnion_const] using h.symm

/-- The dummy and an arbitrary primary at a later layer have disjoint interiors.
Source: Section 11, prop:two-families, lines 154–177 and 212–218. -/
private theorem dummy_primary_interiors (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))) (J : ℤ × ℤ)
    (hk : k₀ ≤ k) :
    Disjoint (interior (closure (dyadicNeighborhood o k₀ Z C)))
      (interior (primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
        Z C a.val b.val J)) := by
  rw [primary_eq_union]
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp (interior_subset hy)
  exact Set.disjoint_left.mp (dummy_cell_interiors o k₀ k Z C z.val hk
    (Finset.mem_filter.mp z.property).1) hx hxz

/-- Different primary identifiers have disjoint interiors.
Source: Section 11, prop:two-families, lines 212–218 and 299–323. -/
private theorem primaries_interiors (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (J K : ℤ × ℤ) (hne : (k, J) ≠ (h, K)) :
    Disjoint (interior (primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
      Z C (a k).val (b k).val J))
      (interior (primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
        Z C (a h).val (b h).val K)) := by
  rw [primary_eq_union, primary_eq_union]
  refine fineCellUnions_disjoint_interiors o k h Z C
    (fun z : {z // z ∈ primaryCells o k Z C (a k) (b k) J} ↦ z.val)
    (fun w : {w // w ∈ primaryCells o h Z C (a h) (b h) K} ↦ w.val) ?_ ?_ ?_
  · intro z
    exact (Finset.mem_filter.mp z.property).1
  · intro w
    exact (Finset.mem_filter.mp w.property).1
  · intro z w he
    have hkh : k = h := congrArg Prod.fst he
    subst h
    have hzw : z.val = w.val := congrArg Prod.snd he
    have hzJ := (Finset.mem_filter.mp z.property).2.2
    have hwK := (Finset.mem_filter.mp w.property).2.2
    have hJK : J = K := hzJ.symm.trans
      ((congrArg (nonbeltPitchIndex (fineScaleIndex k) (pitchScaleIndex k)
        (a k).val (b k).val) hzw).trans hwK)
    exact hne (Prod.ext rfl hJK)

/-- A primary interior is disjoint from the interior of an actual belt-cell closure.
Source: Section 11, prop:two-families, lines 212–218 and 299–323. -/
private theorem primary_beltCell_interiors (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (J w : ℤ × ℤ)
    (hw : w ∈ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h)) :
    Disjoint (interior (primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
      Z C (a k).val (b k).val J))
      (interior (closure (dyadicCell o (fineScaleIndex h) w))) := by
  rw [primary_eq_union]
  have hd := fineCellUnions_disjoint_interiors o k h Z C
    (fun z : {z // z ∈ primaryCells o k Z C (a k) (b k) J} ↦ z.val)
    (fun _ : Unit ↦ w) (fun z ↦ (Finset.mem_filter.mp z.property).1)
    (fun _ ↦ (Finset.mem_filter.mp hw).1) (by
      intro z _ he
      have hkh : k = h := congrArg Prod.fst he
      subst h
      have hzw : z.val = w := congrArg Prod.snd he
      have hnot := (Finset.mem_filter.mp z.property).2.1
      apply hnot
      simpa only [hzw] using hw)
  simpa only [Set.iUnion_const] using hd

/-- Distinct actual initial open regions are pairwise disjoint. No nonempty
endpoint-set, origin, contact, residue, or finite-support premise is required.
Source: Section 11, prop:two-families, lines 154–177, 212–218 and 299–323. -/
theorem initialOpenRegion_pairwise_disjoint (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    Pairwise (fun i j : InitialRegionIndex o k₀ Z C a b hC h₀ ↦
      Disjoint (initialOpenRegion o k₀ Z C a b hC h₀ i)
        (initialOpenRegion o k₀ Z C a b hC h₀ j)) := by
  classical
  rintro (⟨⟩ | (⟨k, J⟩ | ⟨k, z, R⟩)) (⟨⟩ | (⟨h, K⟩ | ⟨h, w, T⟩)) hne <;>
    simp only [initialOpenRegion, initialBirthRegion]
  · exact False.elim (hne rfl)
  · exact dummy_primary_interiors o k₀ h.val Z C (a h.val) (b h.val) K.val h.property
  · exact (dummy_cell_interiors o k₀ h.val Z C w.val h.property
      (Finset.mem_filter.mp w.property).1).mono_right
      (interior_subset.trans (run_subset_cellClosure _ _ _ _ _ T))
  · exact (dummy_primary_interiors o k₀ k.val Z C
      (a k.val) (b k.val) J.val k.property).symm
  · apply primaries_interiors
    intro he
    have hkh : k = h := Subtype.ext (congrArg Prod.fst he)
    subst h
    have hJK : J = K := Subtype.ext (congrArg Prod.snd he)
    subst K
    exact hne rfl
  · exact (primary_beltCell_interiors o k.val h.val Z C a b J.val w.val
      w.property).mono_right (interior_mono (run_subset_cellClosure _ _ _ _ _ T))
  · exact ((dummy_cell_interiors o k₀ k.val Z C z.val k.property
      (Finset.mem_filter.mp z.property).1).mono_right
      (interior_subset.trans (run_subset_cellClosure _ _ _ _ _ R))).symm
  · exact ((primary_beltCell_interiors o h.val k.val Z C a b K.val z.val
      z.property).mono_right (interior_mono (run_subset_cellClosure _ _ _ _ _ R))).symm
  · by_cases he : (k.val, z.val) = (h.val, w.val)
    · have hkh : k = h := Subtype.ext (congrArg Prod.fst he)
      subst h
      have hzw : z = w := Subtype.ext (congrArg Prod.snd he)
      subst w
      apply cellFanRunRegions_disjoint_interiors
      intro hRT
      subst T
      exact hne rfl
    · have hd := fineCellUnions_disjoint_interiors o k.val h.val Z C
        (fun _ : Unit ↦ z.val) (fun _ : Unit ↦ w.val)
        (fun _ ↦ (Finset.mem_filter.mp z.property).1)
        (fun _ ↦ (Finset.mem_filter.mp w.property).1) (fun _ _ ↦ he)
      simp only [Set.iUnion_const] at hd
      exact hd.mono (interior_mono (run_subset_cellClosure _ _ _ _ _ R))
        (interior_mono (run_subset_cellClosure _ _ _ _ _ T))

end TNLean.PEPS.AreaLaw.Geometry
