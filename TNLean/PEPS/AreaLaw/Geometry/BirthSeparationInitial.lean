/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationNormalization
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.RepairInduction
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationAtoms
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygons
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import TNLean.PEPS.AreaLaw.Geometry.CellSides
import TNLean.PEPS.AreaLaw.Geometry.FanSideContacts
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInterfaces
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionRegularity
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import TNLean.PEPS.AreaLaw.Geometry.InitialStars

/-!
# Birth separation of the initial belt tiles

Let `x` be an initial belt tile in a belt cell `Q` of side `u = t_k`. Its closed
birth is a union of fan triangles of `Q`. Every earlier or peer identifier `y`
of the same label, that is, every primary and every other initial belt tile,
has final actual region at distance at least `c₁ u^ρ₀` from the birth of `x`,
for one constant `c₁ > 0` chosen before all data.

Normalize `Q` to `[0, 4]²`. Near `Q` only the same and the adjacent layers
occur, so every fan triangle and every closed fine cell meeting the region
of interest is bounded by lines of the normalized belt arrangement. Each point
of the birth of `x` lies in an atom contained in that birth, and each point of
the open region of `y` near `Q` lies in an atom contained in the birth of `y`.

* *No common segments.* The two births of the same label share no
  nondegenerate segment, so the two atoms meet only in integer points.
* *Compactness.* The uniform atom dichotomy gives distance at least `η`, in
  normalized units, unless both points lie within `1/4` of a common integer
  point `q` of the two atoms, where the angular estimate holds.
* *Contacts are marks of `Q`.* A common point of the two births lies in the
  closed cell `Q`. If `y` is another run of `Q`, it is the center of `Q`. Otherwise
  it lies on the boundary of `Q`; a contact with a coordinate of odd normalized
  value would lie inside an elementary side of `Q`, and the atom of `y` would
  share a unit segment of that side with the fan triangle of `x`. Hence the
  contact is one of the nine marks of `Q`.
* *The following trim.* The first removal cuts from every old identifier the
  square of half-side `d(S) ≥ u^ρ₀ / 4` about each mark of `Q`, so the final
  region of `y` stays at distance more than `u^ρ₀ / 4` from the contact.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659,
with the belt case of the finite local patterns in lines 597–604; the belt
construction and its interfaces, lines 299–330; the trim, lines 380–399;
open actual regions and closed births, lines 545–561; and the order of
identifiers, lines 563–571.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry


/-! ### Initial regions near a belt cell -/

section Core

variable {o : ℝ × ℝ} {k₀ : ℕ} {Z : Finset (ℤ × ℤ)} {C : ℕ}
  {a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀}

/-- The initial identifier of a run of a selected belt cell: an initial belt
tile.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
abbrev initialBeltRun (k : ℕ) (hk : k₀ ≤ k) (z : ℤ × ℤ)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
    InitialRegionIndex o k₀ Z C a b hC h₀ :=
  .inr (.inr ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩)

variable {k : ℕ} {hk : k₀ ≤ k} {z : ℤ × ℤ}
  {hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)}

theorem initialBeltRun_birth_subset_closure
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
    initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) ⊆
      closure (dyadicCell o (fineScaleIndex k) z) := by
  change cellFanRunRegion _ _ _ _ _ R ⊆ _
  rw [← cellFanRunRegions_cover]
  exact Set.subset_iUnion (fun R ↦ cellFanRunRegion _ _ _ _ _ R) R

theorem cellFanPolygon_subset_initialBeltRun_birth
    {R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)}
    {t : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)} (ht : t ∈ R.supp) :
    (cellFanPolygon o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).region ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
  Set.subset_biUnion_of_mem (u := fun t ↦
    (cellFanPolygon o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).region) ht

/-- An initial identifier whose open region meets the interior of a belt cell
is a run of that cell.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem exists_eq_initialBeltRun_of_inter_interior (y : InitialRegionIndex o k₀ Z C a b hC h₀)
    (h : (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z))).Nonempty) :
    ∃ R, y = initialBeltRun k hk z hz R := by
  obtain ⟨w, hwy, hwQ⟩ := h
  have hwc := interior_subset hwQ
  rw [← cellFanPolygons_cover o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)] at hwc
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hwc
  have hU : IsOpen (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z))) :=
    isOpen_interior.inter isOpen_interior
  have hne : (interior (cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) t).region ∩ (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z)))).Nonempty := by
    rw [← closure_inter_open_nonempty_iff hU, (cellFanPolygon_interior_nonempty_and_closure_eq
      o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).2]
    exact ⟨w, ht, hwy, hwQ⟩
  obtain ⟨w', hw'T, hw'y, -⟩ := hne
  let R := (cellFanRunGraph o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)).connectedComponentMk t
  have hw'x : w' ∈ initialOpenRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
    interior_mono (cellFanPolygon_subset_initialBeltRun_birth
      ((SimpleGraph.ConnectedComponent.mem_supp_iff R t).mpr rfl)) hw'T
  refine ⟨R, ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀ hne)
    hw'y hw'x

/-- Two distinct initial identifiers of the same label share no nondegenerate
segment.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem not_segment_subset_initialBirthRegion_inter {x y : InitialRegionIndex o k₀ Z C a b hC h₀}
    (hyx : y ≠ x) (hcol : initialRegionColor o k₀ Z C a b hC h₀ y =
      initialRegionColor o k₀ Z C a b hC h₀ x) {p q : ℝ × ℝ} (hpq : p ≠ q)
    (hx : segment ℝ p q ⊆ initialBirthRegion o k₀ Z C a b hC h₀ x)
    (hy : segment ℝ p q ⊆ initialBirthRegion o k₀ Z C a b hC h₀ y) : False :=
  initialRegionColor_ne_of_segment_subset_inter o k₀ Z C a b hC h₀ y x hyx p q hpq
    (fun _ hw ↦ ⟨hy hw, hx hw⟩) hcol

/-- **Contacts are marks of the belt cell.** Let `x` be an initial belt tile of
a cell `Q`, let `y` be a distinct initial identifier of the same label, and let
`q` be an integer point, in the coordinates normalized at `Q`, lying in the
birth of `x` and in an atom contained in the normalized birth of `y`. Then `q`
is the normalized position of one of the nine marks of `Q`.
Source: area-law Section 11, `geometry:birth-separation`, lines 606–615, with
the belt construction, lines 299–330. -/
theorem beltNormalize_symm_mem_beltCellMarks
    {R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)}
    {y : InitialRegionIndex o k₀ Z C a b hC h₀} (hyx : y ≠ initialBeltRun k hk z hz R)
    (hcol : initialRegionColor o k₀ Z C a b hC h₀ y =
      initialRegionColor o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R))
    {c : ℤ × ℤ} {s : RepairFanSlot}
    (hB : beltAtom c s ⊆ beltNormalize o (fineScaleIndex k) z ''
      initialBirthRegion o k₀ Z C a b hC h₀ y)
    {i j : ℤ} (hqB : ((i : ℝ), (j : ℝ)) ∈ beltAtom c s)
    (hvx : (beltNormalize o (fineScaleIndex k) z).symm ((i : ℝ), (j : ℝ)) ∈
      initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R)) :
    (beltNormalize o (fineScaleIndex k) z).symm ((i : ℝ), (j : ℝ)) ∈
      beltCellMarks o (fineScaleIndex k) z := by
  set N := beltNormalize o (fineScaleIndex k) z
  set v := N.symm ((i : ℝ), (j : ℝ)) with hv
  have hNv : N v = ((i : ℝ), (j : ℝ)) := N.apply_symm_apply _
  have hvy : v ∈ initialBirthRegion o k₀ Z C a b hC h₀ y := by
    obtain ⟨v', hv', he⟩ := hB hqB
    rw [hv, ← he, N.symm_apply_apply]
    exact hv'
  have hvQ := initialBeltRun_birth_subset_closure R hvx
  by_cases hint : v ∈ interior (closure (dyadicCell o (fineScaleIndex k) z))
  · -- `y` is another run of the cell
    have hmeet : (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
        interior (closure (dyadicCell o (fineScaleIndex k) z))).Nonempty := by
      rw [initialBirthRegion_eq_closure_initialOpenRegion] at hvy
      obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hvy _ isOpen_interior hint
      exact ⟨w, hw₂, hw₁⟩
    obtain ⟨R', rfl⟩ := exists_eq_initialBeltRun_of_inter_interior (hk := hk) (hz := hz) y hmeet
    have hRR' : R' ≠ R := fun h ↦ hyx (h ▸ rfl)
    by_cases hc : v = cellFanCenter o (fineScaleIndex k) z
    · rw [hc]
      refine mem_beltCellMarks_of_beltNormalize_eq (m := 1) (n := 1) (by norm_num) (by norm_num) ?_
      have := beltNormalize_cellFanCenter_add (o := o) (ℓ := fineScaleIndex k) (z := z) 0
      simp only [smul_zero, add_zero] at this
      rw [this]; norm_num
    · exfalso
      have hcenter (S : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
          cellFanCenter o (fineScaleIndex k) z ∈
            initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz S) := by
        obtain ⟨t, ht⟩ := S.nonempty_supp
        exact cellFanPolygon_subset_initialBeltRun_birth ht
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
      have hnt : (cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz) R' ∩
          cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz) R).Nontrivial :=
        ⟨v, ⟨hvy, hvx⟩, _, ⟨hcenter R', hcenter R⟩, hc⟩
      have hne := cellFanRunRegions_contact_colors_ne o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)
        R' R hRR' hnt
      obtain ⟨t', ht'⟩ := R'.nonempty_supp
      obtain ⟨t, ht⟩ := R.nonempty_supp
      apply hne t' ht' t ht
      rw [← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk hz R' t' ht',
        ← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk hz R t ht]
      exact hcol
  · -- the contact lies on the boundary of the cell
    have hfr : v ∈ frontier (dyadicCell o (fineScaleIndex k) z) :=
      ⟨hvQ, fun h ↦ hint (interior_mono subset_closure h)⟩
    obtain ⟨side, hside⟩ := exists_dyadicCellSide_of_mem_frontier o (fineScaleIndex k) z v hfr
    obtain ⟨t, ht, hvt⟩ := Set.mem_iUnion₂.mp hvx
    have hseg : v ∈ segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t) := by
      have h := cellFanPolygon_inter_dyadicCellSide o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) t side
      exact (h.subset ⟨hvt, hside⟩).1
    obtain ⟨m₁, n₁, hS⟩ := exists_beltNormalize_cellFanStart_eq (o := o)
      (ℓ := fineScaleIndex k) (z := z) (fineLayerSplitMask o k₀ k Z C z) t
    obtain ⟨m₂, n₂, hE⟩ := exists_beltNormalize_cellFanEnd_eq (o := o)
      (ℓ := fineScaleIndex k) (z := z) (fineLayerSplitMask o k₀ k Z C z) t
    have hTseg : segment ℝ
        (N (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t))
        (N (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)) ⊆
        N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) := by
      rw [← beltNormalize_image_segment]
      refine Set.image_mono (Set.Subset.trans ?_ (cellFanPolygon_subset_initialBeltRun_birth ht))
      apply (convex_convexHull ℝ _).segment_subset
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hqseg : ((i : ℝ), (j : ℝ)) ∈ segment ℝ
        (N (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t))
        (N (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)) := by
      rw [← beltNormalize_image_segment, ← hNv]
      exact Set.mem_image_of_mem _ hseg
    rw [hS, hE] at hTseg hqseg
    have hax : m₁ = m₂ ∨ n₁ = n₂ := by
      rcases (cellFan_elementary_geometry o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) t).2 with ⟨h, -⟩ | ⟨h, -⟩
      · left
        have h' := congrArg Prod.fst hS
        have h'' := congrArg Prod.fst hE
        rw [beltNormalize_fst] at h' h''
        rw [h] at h'
        have : ((2 * m₁ : ℤ) : ℝ) = ((2 * m₂ : ℤ) : ℝ) := h'.symm.trans h''
        have := Int.cast_injective this
        omega
      · right
        have h' := congrArg Prod.snd hS
        have h'' := congrArg Prod.snd hE
        rw [beltNormalize_snd] at h' h''
        rw [h] at h'
        have : ((2 * n₁ : ℤ) : ℝ) = ((2 * n₂ : ℤ) : ℝ) := h'.symm.trans h''
        have := Int.cast_injective this
        omega
    by_cases heven : Even i ∧ Even j
    · obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := heven
      obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := beltNormalize_mem_Icc hvQ
      rw [hNv] at h₁ h₂ h₃ h₄
      simp only at h₁ h₂ h₃ h₄
      rw [hm] at h₁ h₂
      rw [hn] at h₃ h₄
      push_cast at h₁ h₂ h₃ h₄
      have a₁ : (0 : ℝ) ≤ m := by linarith
      have a₂ : (m : ℝ) ≤ 2 := by linarith
      have a₃ : (0 : ℝ) ≤ n := by linarith
      have a₄ : (n : ℝ) ≤ 2 := by linarith
      refine mem_beltCellMarks_of_beltNormalize_eq (m := m) (n := n)
        ⟨by exact_mod_cast a₁, by exact_mod_cast a₂⟩ ⟨by exact_mod_cast a₃, by exact_mod_cast a₄⟩
        ?_
      rw [hNv, hm, hn]; push_cast; ring_nf
    · exfalso
      rcases add_mem_segment_of_odd hax hqseg heven with ⟨hodd, hσ⟩ | ⟨hodd, hσ⟩
      · obtain ⟨⟨σ, hσ₁, hBseg⟩, -⟩ := beltAtom_axis_segments hodd hqB
        have h₁ : segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ) + σ, (j : ℝ)) ⊆
            N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
          ((convex_segment _ _).segment_subset hqseg (hσ σ hσ₁)).trans hTseg
        have hne : N.symm ((i : ℝ), (j : ℝ)) ≠ N.symm ((i : ℝ) + σ, (j : ℝ)) := by
          intro h
          have h' := congrArg Prod.fst (N.symm.injective h)
          simp only at h'
          rcases hσ₁ with rfl | rfl <;> linarith
        exact not_segment_subset_initialBirthRegion_inter hyx hcol hne
          (segment_symm_subset_of_subset_image h₁)
          (segment_symm_subset_of_subset_image (hBseg.trans hB))
      · obtain ⟨-, ⟨σ, hσ₁, hBseg⟩⟩ := beltAtom_axis_segments hodd hqB
        have h₁ : segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ), (j : ℝ) + σ) ⊆
            N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
          ((convex_segment _ _).segment_subset hqseg (hσ σ hσ₁)).trans hTseg
        have hne : N.symm ((i : ℝ), (j : ℝ)) ≠ N.symm ((i : ℝ), (j : ℝ) + σ) := by
          intro h
          have h' := congrArg Prod.snd (N.symm.injective h)
          simp only at h'
          rcases hσ₁ with rfl | rfl <;> linarith
        exact not_segment_subset_initialBirthRegion_inter hyx hcol hne
          (segment_symm_subset_of_subset_image h₁)
          (segment_symm_subset_of_subset_image (hBseg.trans hB))

/-- Every point of the birth of an initial identifier other than the dummy that
lies within one fine side of a point of a fine cell of layer `k` lies in an atom, in the
coordinates normalized at that cell, contained in the normalized birth.
Source: area-law Section 11, `geometry:birth-separation`, lines 592–604, with
`geometry:nonadjacent` and the scale comparison, lines 193–207. -/
theorem exists_beltAtom_subset_initialBirthRegion
    (hk' : k₀ ≤ k) (hzF : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (y : InitialRegionIndex o k₀ Z C a b hC h₀) (hyd : y ≠ .inl ())
    {p w : ℝ × ℝ} (hp : p ∈ closure (dyadicCell o (fineScaleIndex k) z))
    (hw : w ∈ initialBirthRegion o k₀ Z C a b hC h₀ y)
    (hpw : dist p w < (2 : ℝ) ^ fineScaleIndex k) :
    ∃ c s, beltNormalize o (fineScaleIndex k) z w ∈ beltAtom c s ∧
      beltAtom c s ⊆ beltNormalize o (fineScaleIndex k) z ''
        initialBirthRegion o k₀ Z C a b hC h₀ y := by
  have hpL : p ∈ closure (dyadicLayer o k Z C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k (fineScaleIndex k)
      Z C z (fineScaleIndex_le k) hzF) hp
  have hscale : ∀ h, w ∈ closure (dyadicLayer o h Z C) →
      fineScaleIndex k ≤ fineScaleIndex h + 1 := by
    intro h hwL
    have hnear : dist p w < 10 * (2 : ℝ) ^ fineScaleIndex k := by
      have : (0 : ℝ) < (2 : ℝ) ^ fineScaleIndex k := by positivity
      linarith
    obtain ⟨h₁, h₂⟩ := dyadicLayer_nearby_indices o k h Z C p w hC (h₀.trans hk') hpL hwL hnear
    rcases (show h + 1 = k ∨ k ≤ h by omega) with rfl | hkh
    · rcases fineScaleIndex_succ h with e | e <;> omega
    · have := fineScaleIndex_mono hkh; omega
  rcases y with ⟨⟩ | (⟨h, J⟩ | ⟨h, w', R'⟩)
  · exact absurd rfl hyd
  · change w ∈ primaryBirthRegion o h.val (fineScaleIndex h.val) (pitchScaleIndex h.val) Z C
      (a h.val).val (b h.val).val J.val at hw
    have hrw := primaryBirthRegion_eq_iUnion_nonbeltCell_closure o h.val (fineScaleIndex h.val)
      (pitchScaleIndex h.val) Z C (a h.val) (b h.val) J.val (fineScaleIndex_le h.val)
      ((fineScaleIndex_le h.val).trans (le_pitchScaleIndex h.val))
    rw [hrw] at hw
    obtain ⟨w', hw'F, hw'⟩ := Set.mem_iUnion₂.mp hw
    have hw'L : w ∈ closure (dyadicLayer o h.val Z C) :=
      closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h.val
        (fineScaleIndex h.val) Z C w' (fineScaleIndex_le h.val)
        (Finset.mem_filter.mp hw'F).1) hw'
    obtain ⟨c, s, h₁, h₂⟩ := exists_beltAtom_subset_closure_dyadicCell (o := o) (z := z)
      (hscale h.val hw'L) hw'
    refine ⟨c, s, h₁, h₂.trans (Set.image_mono ?_)⟩
    change _ ⊆ primaryBirthRegion o h.val (fineScaleIndex h.val) (pitchScaleIndex h.val) Z C
      (a h.val).val (b h.val).val J.val
    rw [hrw]
    exact Set.subset_biUnion_of_mem (u := fun w' ↦ closure (dyadicCell o (fineScaleIndex h.val) w'))
      hw'F
  · change w ∈ cellFanRunRegion _ _ _ _ _ R' at hw
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp hw
    have hw'F : w'.val ∈ fineLayerIndices o h.val (fineScaleIndex h.val) Z C :=
      Finset.mem_of_mem_filter _ w'.property
    have hwc : w ∈ closure (dyadicCell o (fineScaleIndex h.val) w'.val) := by
      rw [← cellFanPolygons_cover o (fineScaleIndex h.val) w'.val
        (fineLayerSplitMask o k₀ h.val Z C w'.val)]
      exact Set.mem_iUnion.mpr ⟨t, hwt⟩
    have hw'L : w ∈ closure (dyadicLayer o h.val Z C) :=
      closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h.val
        (fineScaleIndex h.val) Z C w'.val (fineScaleIndex_le h.val) hw'F) hwc
    obtain ⟨c, s, h₁, h₂⟩ := exists_beltAtom_subset_cellFanPolygon (o := o) (z := z)
      (hscale h.val hw'L) _ t hwt
    refine ⟨c, s, h₁, h₂.trans (Set.image_mono ?_)⟩
    exact Set.subset_biUnion_of_mem (u := fun t ↦ (cellFanPolygon o (fineScaleIndex h.val) w'.val
      (fineLayerSplitMask o k₀ h.val Z C w'.val) t).region) ht

end Core

/-- **The birth-template separation constant** `c₁ = 1/112`: a quarter of
`birthSeparationConstant`, since belt cells are normalized to side `4`. It is
the constant of the birth-template separation lemma for the initial belt
tiles, and it is also at most the constant `1/28` of the replacements.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
def birthTemplateSeparationConstant : ℝ := birthSeparationConstant / 4

theorem birthTemplateSeparationConstant_pos : 0 < birthTemplateSeparationConstant := by
  unfold birthTemplateSeparationConstant; linarith [birthSeparationConstant_pos]

theorem birthTemplateSeparationConstant_le :
    birthTemplateSeparationConstant ≤ birthSeparationConstant := by
  unfold birthTemplateSeparationConstant; linarith [birthSeparationConstant_pos]

/-- **Birth separation of an initial belt tile from its comparison regions.**
With `c₁ = birthTemplateSeparationConstant = 1/112` the following holds. Let
`x` be an initial belt tile in a belt cell of side `u = t_k`, and let `y` be
another initial identifier of the same label other than the dummy: a primary or
another initial belt tile. Let `Y` lie in the open region of `y` and avoid, at sup distance
`u^ρ₀ / 4`, the nine marks of the cell, as the first trim guarantees. Then every
point of the closed birth of `x` has distance at least `c₁ u^ρ₀` from `Y`.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem initialBeltRun_birth_separation :
    ∀ (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
      (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (hk : k₀ ≤ k) (z : ℤ × ℤ)
      (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
      (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz))
      (y : InitialRegionIndex o k₀ Z C a b hC h₀),
      y ≠ initialBeltRun k hk z hz R → y ≠ .inl () →
      initialRegionColor o k₀ Z C a b hC h₀ y =
        initialRegionColor o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) →
      ∀ Y ⊆ initialOpenRegion o k₀ Z C a b hC h₀ y,
      (∀ v ∈ beltCellMarks o (fineScaleIndex k) z, ∀ w ∈ Y,
        ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) / 4 < dist w v) →
      ∀ p ∈ initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R), ∀ w ∈ Y,
        birthTemplateSeparationConstant * ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) ≤
          dist p w := by
  unfold birthTemplateSeparationConstant
  have hdich := beltAtom_dichotomy
  set η := birthSeparationConstant
  have hη : 0 < η := birthSeparationConstant_pos
  have hη8 : η / 4 ≤ 1 / 8 := by linarith [birthSeparationConstant_le_quarter]
  intro o k₀ Z C a b hC h₀ k hk z hz R y hyx hyd hcol Y hY htrim p hp w hw
  set u : ℝ := (2 : ℝ) ^ fineScaleIndex k
  set N := beltNormalize o (fineScaleIndex k) z
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hu0 : 0 < u := by linarith
  have hρ : u ^ (Exponents.rho : ℝ) ≤ u := by
    calc u ^ (Exponents.rho : ℝ) ≤ u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu1 rho_pos_lt_one.2.le
      _ = u := Real.rpow_one u
  have hρ0 : 0 ≤ u ^ (Exponents.rho : ℝ) := Real.rpow_nonneg hu0.le _
  have hc₁ : (η / 4) * u ^ (Exponents.rho : ℝ) ≤ u ^ (Exponents.rho : ℝ) / 8 :=
    by nlinarith [hη8]
  have hnorm (p q : ℝ × ℝ) : ‖N p - N q‖ = 4 / u * dist p q := by
    rw [norm_beltNormalize_sub, dist_eq_norm]
  by_cases hfar : u ≤ dist p w
  · nlinarith
  push Not at hfar
  -- the atom of the belt tile
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨cA, sA, hpA, hA⟩ := exists_beltAtom_subset_cellFanPolygon (o := o) (z := z)
    (ℓ := fineScaleIndex k) (ℓ' := fineScaleIndex k) (by omega) _ t hpt
  have hAx : beltAtom cA sA ⊆ N '' initialBirthRegion o k₀ Z C a b hC h₀
      (initialBeltRun k hk z hz R) :=
    hA.trans (Set.image_mono (cellFanPolygon_subset_initialBeltRun_birth ht))
  -- the atom of the comparison region
  have hwy : w ∈ initialBirthRegion o k₀ Z C a b hC h₀ y := interior_subset (hY hw)
  obtain ⟨cB, sB, hwB, hBy⟩ := exists_beltAtom_subset_initialBirthRegion hk
    (Finset.mem_of_mem_filter z hz) y hyd (initialBeltRun_birth_subset_closure R hp) hwy hfar
  -- the two atoms meet only in integer points
  have hAB : ∀ q ∈ beltAtom cA sA, q ∈ beltAtom cB sB → ∃ i j : ℤ, q = ((i : ℝ), (j : ℝ)) := by
    intro q hqA hqB
    by_contra hne
    push Not at hne
    obtain ⟨a', b', hab, hseg⟩ := exists_segment_subset_beltAtom_inter hqA hqB hne
    exact not_segment_subset_initialBirthRegion_inter hyx hcol (N.symm.injective.ne hab)
      (segment_symm_subset_of_subset_image (hseg.trans (Set.inter_subset_left.trans hAx)))
      (segment_symm_subset_of_subset_image (hseg.trans (Set.inter_subset_right.trans hBy)))
  rcases hdich cA cB sA sB hAB (N p) hpA (N w) hwB with hd | ⟨q, ⟨hqA, hqB⟩, -, -, hang⟩
  · -- far from every contact
    rw [hnorm] at hd
    have : η * u ≤ 4 * dist p w := by
      have := mul_le_mul_of_nonneg_right hd hu0.le
      rwa [show 4 / u * dist p w * u = 4 * dist p w by field_simp] at this
    nlinarith
  · -- near a contact, which is a mark of the cell
    obtain ⟨i, j, rfl⟩ := hAB q hqA hqB
    have hvx : N.symm ((i : ℝ), (j : ℝ)) ∈
        initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) := by
      obtain ⟨v', hv', he⟩ := hAx hqA
      rw [← he, N.symm_apply_apply]
      exact hv'
    have hmark := beltNormalize_symm_mem_beltCellMarks hyx hcol hBy hqB hvx
    have hgap := htrim _ hmark w hw
    have hq : ((i : ℝ), (j : ℝ)) = N (N.symm ((i : ℝ), (j : ℝ))) := (N.apply_symm_apply _).symm
    rw [hq, hnorm, hnorm] at hang
    have : dist w (N.symm ((i : ℝ), (j : ℝ))) / 2 ≤ dist p w := by
      have h4 : 0 < 4 / u := by positivity
      nlinarith
    linarith

/-- **Birth separation of an initial belt tile from its comparison regions.**
There is one fixed `c₁ > 0` with the following property. Let `x` be an initial
belt tile in a belt cell of side `u = t_k`, and let `y` be another initial
identifier of the same label other than the dummy: a primary or another initial
belt tile. Let `Y` lie in the open region of `y` and avoid, at sup distance
`u^ρ₀ / 4`, the nine marks of the cell, as the first trim guarantees. Then every
point of the closed birth of `x` has distance at least `c₁ u^ρ₀` from `Y`. One
may take `c₁ = 1/112` (`initialBeltRun_birth_separation`).
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem exists_initialBeltRun_birth_separation :
    ∃ c₁ > 0, ∀ (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
      (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (hk : k₀ ≤ k) (z : ℤ × ℤ)
      (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
      (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz))
      (y : InitialRegionIndex o k₀ Z C a b hC h₀),
      y ≠ initialBeltRun k hk z hz R → y ≠ .inl () →
      initialRegionColor o k₀ Z C a b hC h₀ y =
        initialRegionColor o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) →
      ∀ Y ⊆ initialOpenRegion o k₀ Z C a b hC h₀ y,
      (∀ v ∈ beltCellMarks o (fineScaleIndex k) z, ∀ w ∈ Y,
        ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) / 4 < dist w v) →
      ∀ p ∈ initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R), ∀ w ∈ Y,
        c₁ * ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) ≤ dist p w :=
  ⟨_, birthTemplateSeparationConstant_pos, initialBeltRun_birth_separation⟩

/-! ### The actual initial stage -/

/-- The fine scale index of an initial belt tile; the other initial identifiers
have none. Its side is `t_k = 2 ^ fineScaleIndex k`.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
def InitialRegionIndex.beltScaleIndex {o : ℝ × ℝ} {k₀ : ℕ} {Z : Finset (ℤ × ℤ)} {C : ℕ}
    {a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))}
    {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} : InitialRegionIndex o k₀ Z C a b hC h₀ → Option ℕ
  | .inr (.inr ⟨k, _, _⟩) => some (fineScaleIndex k.val)
  | _ => none

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- **Birth separation of the initial belt tiles** with constant `c₁`: the closed
birth of every initial belt tile of side `u = t_k` is at distance at least
`c₁ u^ρ₀` from the final actual region of every earlier or peer identifier of
the same label, that is, of every primary and every other initial belt tile.
The dummy is excluded from the order of identifiers.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–582, with
the order of identifiers, lines 563–571. -/
def IsInitialBirthSeparated (c₁ : ℝ) : Prop :=
  ∀ (x y : (𝔇 0).regionIndex) (ℓ : ℕ), InitialRegionIndex.beltScaleIndex x = some ℓ →
    y ≠ x → y ≠ (𝔇 0).dummy → (𝔇 0).color y = (𝔇 0).color x →
    ∀ p ∈ (𝔇 0).birth x, ∀ w ∈ repairFinalRegion o Λ A C k₀ hC h₀ Sstar 0 y,
      c₁ * ((2 : ℝ) ^ ℓ) ^ (Exponents.rho : ℝ) ≤ dist p w

end Stages

private theorem quarter_rpow_le_repairHalfSide {u S : ℝ} (hu : 1 ≤ u) (hS : u / 2 ≤ S) :
    u ^ (Exponents.rho : ℝ) / 4 ≤ repairHalfSide S := by
  have hu0 : 0 < u := by linarith
  have hS0 : 0 < S := by linarith
  have h₁ := half_rpow_le_repairHalfSide hS0
  have h₂ : (u / 2) ^ (Exponents.rho : ℝ) ≤ S ^ (Exponents.rho : ℝ) :=
    Real.rpow_le_rpow (by positivity) hS rho_pos_lt_one.1.le
  have h₃ : (2 : ℝ) ^ (Exponents.rho : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (Exponents.rho : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) rho_pos_lt_one.2.le
      _ = 2 := Real.rpow_one 2
  have h₄ : (u / 2) ^ (Exponents.rho : ℝ) =
      u ^ (Exponents.rho : ℝ) / 2 ^ (Exponents.rho : ℝ) :=
    Real.div_rpow hu0.le (by norm_num) _
  have h₅ : 0 < (2 : ℝ) ^ (Exponents.rho : ℝ) := by positivity
  have h₆ : u ^ (Exponents.rho : ℝ) / 2 ≤ (u / 2) ^ (Exponents.rho : ℝ) := by
    rw [h₄, div_le_div_iff₀ (by norm_num) h₅]
    nlinarith [Real.rpow_nonneg hu0.le (Exponents.rho : ℝ)]
  linarith

/-- **Birth-template separation of the initial belt tiles.** With
`c₁ = birthTemplateSeparationConstant = 1/112`, for all domains, cuts, origins,
layer widths, lower layer indices and stopping scales, the closed birth of
every initial belt tile of side `u = t_k` has distance at least `c₁ u^ρ₀` from
the final actual region of every primary and every other initial belt tile with
the same label.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, for
the births of initial belt tiles. -/
theorem isInitialBirthSeparated_birthTemplateSeparationConstant (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) :
    IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant := by
  have hcore := initialBeltRun_birth_separation
  intro x y ℓ hx hyx hyd hcol p hp w hw
  let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2 o Λ A C k₀ hC h₀
  let hb := Classical.choose_spec h
  let hab := Classical.choose_spec hb
  let hM := hab.2.2
  have hMmem := (Classical.choose_spec hM).1
  have hspec := Classical.choose_spec (Classical.choose_spec hM).2.2
  obtain ⟨⟩ | ⟨⟩ | ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩ := x
  · cases hx
  · cases hx
  obtain rfl : fineScaleIndex k = ℓ := Option.some_injective _ hx
  refine hcore o k₀ (boundaryEndpoints Λ A) C _ _ hC h₀ k hk z hz R y hyx hyd hcol
    (repairFinalRegion o Λ A C k₀ hC h₀ Sstar 0 y)
    (fun w' hw' ↦ (repairFinalRegion_subset_remnant o Λ A C k₀ hC h₀ Sstar 0 y hw').1)
    ?_ p hp w hw
  intro v hv w' hw'
  have hrem := (repairFinalRegion_subset_remnant o Λ A C k₀ hC h₀ Sstar 0 y hw').2
  have hvM : v ∈ Classical.choose hM :=
    (hMmem v).mpr ⟨k, hk, Finset.mem_biUnion.mpr ⟨z, hz, hv⟩⟩
  have hout : w' ∉ repairSquare v ((initialRepairStage o Λ A C k₀ hC h₀).scale ⟨v, hvM⟩) :=
    fun h ↦ hrem (Set.mem_iUnion.mpr ⟨⟨v, hvM⟩, h⟩)
  obtain ⟨-, k', z', hk', hz', hv', hSv⟩ := hspec.1 ⟨v, hvM⟩
  change w' ∉ repairSquare v (Classical.choose (Classical.choose_spec hM).2.2 ⟨v, hvM⟩) at hout
  rw [hSv, repairSquare, Metric.mem_closedBall, not_le] at hout
  have hvk : v ∈ closure (dyadicLayer o k (boundaryEndpoints Λ A) C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k (fineScaleIndex k)
      _ C z (fineScaleIndex_le k) (Finset.mem_of_mem_filter z hz))
      (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k) z hv)
  have hvk' : v ∈ closure (dyadicLayer o k' (boundaryEndpoints Λ A) C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k' (fineScaleIndex k')
      _ C z' (fineScaleIndex_le k') (Finset.mem_of_mem_filter z' hz'))
      (beltCellMarks_subset_closure_dyadicCell o (fineScaleIndex k') z' hv')
  obtain ⟨h₁, h₂⟩ := dyadicLayer_nearby_indices o k k' _ C v v hC (h₀.trans hk) hvk hvk'
    (by rw [dist_self]; positivity)
  have hℓ : fineScaleIndex k ≤ fineScaleIndex k' + 1 := by
    rcases (show k' + 1 = k ∨ k ≤ k' by omega) with rfl | hkk
    · rcases fineScaleIndex_succ k' with e | e <;> omega
    · have := fineScaleIndex_mono hkk; omega
  have hS : (2 : ℝ) ^ fineScaleIndex k / 2 ≤ (2 : ℝ) ^ fineScaleIndex k' := by
    have : (2 : ℝ) ^ fineScaleIndex k ≤ (2 : ℝ) ^ (fineScaleIndex k' + 1) :=
      pow_le_pow_right₀ (by norm_num) hℓ
    rw [pow_succ] at this
    linarith
  have := quarter_rpow_le_repairHalfSide (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hS
  linarith

/-- **Birth-template separation of the initial belt tiles.** There is one fixed
`c₁ > 0` such that, for all domains, cuts, origins, layer widths, lower layer
indices and stopping scales, the closed birth of every initial belt tile of
side `u = t_k` has distance at least `c₁ u^ρ₀` from the final actual region of
every primary and every other initial belt tile with the same label.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, for
the births of initial belt tiles. One may take `c₁ = 1/112`. -/
theorem exists_isInitialBirthSeparated :
    ∃ c₁ > 0, ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ),
      IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ :=
  ⟨_, birthTemplateSeparationConstant_pos,
    isInitialBirthSeparated_birthTemplateSeparationConstant⟩

theorem IsInitialBirthSeparated.mono {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar c c' : ℝ}
    (h : IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c) (hc : c' ≤ c) :
    IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c' :=
  fun x y ℓ hx hyx hyd hcol p hp w hw ↦
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by positivity) _)).trans
      (h x y ℓ hx hyx hyd hcol p hp w hw)

theorem IsRepairBirthSeparated.mono {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar c c' : ℝ}
    (h : IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c) (hc : c' ≤ c) :
    IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c' :=
  fun j x y m hxm hyx hcol p hp w hw ↦
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (repairHalfSide_pos _).le _)).trans
      (h j x y m hxm hyx hcol p hp w hw)

/-- **Birth-template separation, from Lemma 11.4, with the explicit constant.**
If the uniform repair induction holds, `c₁ = birthTemplateSeparationConstant =
1/112` serves both cases of the birth-separation lemma, the births of the
initial belt tiles and the births of the replacements, for every sufficiently
large stopping scale and lower layer index.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:repair-induction`, lines 471–485. -/
theorem exists_threshold_birthSeparation_of_uniformRepairInductionStatement
    (h : UniformRepairInductionStatement) :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant := by
  obtain ⟨T, hT⟩ := exists_threshold_isRepairBirthSeparated_of_uniformRepairInductionStatement h
  refine ⟨T, fun Sstar hS C ↦ ?_⟩
  obtain ⟨K, hK⟩ := hT Sstar hS C
  exact ⟨K, fun o Λ A k₀ hC h₀ hk ↦
    ⟨isInitialBirthSeparated_birthTemplateSeparationConstant o Λ A C k₀ hC h₀ Sstar,
      (hK o Λ A k₀ hC h₀ hk).mono birthTemplateSeparationConstant_le⟩⟩

/-- **Birth-template separation, from Lemma 11.4.** If the uniform repair
induction holds, one fixed `c₁ > 0` serves both cases of the birth-separation
lemma: the births of the initial belt tiles and the births of the replacements,
for every sufficiently large stopping scale and lower layer index.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:repair-induction`, lines 471–485. One may take `c₁ = 1/112`. -/
theorem exists_birthSeparation_of_uniformRepairInductionStatement
    (h : UniformRepairInductionStatement) :
    ∃ c₁ > 0, ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ :=
  ⟨_, birthTemplateSeparationConstant_pos,
    exists_threshold_birthSeparation_of_uniformRepairInductionStatement h⟩

/-- **Birth-template separation, from Lemma 11.3.** If the jointly chosen initial
stage has isolated stars (the conclusion of Lemma 11.3 used by Lemma 11.4), one
fixed `c₁ > 0` serves both cases of the birth-separation lemma, for every
sufficiently large stopping scale and lower layer index.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:initial-stars`, lines 332–349, and `geometry:repair-induction`,
lines 471–543. -/
theorem exists_birthSeparation_of_initialIsolatedStars
    (h : InitialIsolatedStarsStatement) :
    ∃ c₁ > 0, ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ :=
  exists_birthSeparation_of_uniformRepairInductionStatement
    (uniformRepairInductionStatement_of_initialIsolatedStars h)


/-- **Birth-template separation** (Lemma 11.5). One fixed `c₁ > 0` serves both
cases of the lemma, for every sufficiently large stopping scale and lower layer
index, as in the standing choices of the repair induction: the closed birth of an
initial belt tile of side `u = t_k`, or of a replacement whose removal square has
half-side `u`, is at distance at least `c₁ u^ρ₀` from the final actual region of
every earlier or peer identifier of the same label.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–582, with
the proof in lines 584–659. -/
theorem exists_birthSeparation :
    ∃ c₁ > 0, ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ :=
  exists_birthSeparation_of_initialIsolatedStars initialIsolatedStarsStatement_holds

/-- **Birth-template separation, from Lemma 11.3, with the explicit constant.**
If the jointly chosen initial stage has isolated stars,
`c₁ = birthTemplateSeparationConstant = 1/112` serves both cases of the
birth-separation lemma, for every sufficiently large stopping scale and lower
layer index.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:initial-stars`, lines 332–349, and `geometry:repair-induction`,
lines 471–543. -/
theorem exists_threshold_birthSeparation_of_initialIsolatedStars
    (h : InitialIsolatedStarsStatement) :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant :=
  exists_threshold_birthSeparation_of_uniformRepairInductionStatement
    (uniformRepairInductionStatement_of_initialIsolatedStars h)

/-- **Birth-template separation with the explicit constant** (Lemma 11.5). The
constant `c₁ = birthTemplateSeparationConstant = 1/112` serves both cases of the
lemma, for every sufficiently large stopping scale and lower layer index: the
closed birth of an initial belt tile of side `u = t_k`, or of a replacement whose
removal square has half-side `u`, is at distance at least `c₁ u^ρ₀` from the
final actual region of every earlier or peer identifier of the same label.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–582, with
the proof in lines 584–659. -/
theorem exists_threshold_birthSeparation :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant ∧
            IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar birthTemplateSeparationConstant :=
  exists_threshold_birthSeparation_of_initialIsolatedStars initialIsolatedStarsStatement_holds

end TNLean.PEPS.AreaLaw.Geometry
