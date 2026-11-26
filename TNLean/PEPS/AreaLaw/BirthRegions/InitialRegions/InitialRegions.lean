/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.BeltFanColors
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanRuns
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.LayerPartition
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.FanRunContacts
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.DistanceLayers
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.PrimaryFineCellCover
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.GDelta.Basic
import TNLean.PEPS.AreaLaw.BirthRegions.Fans.CellFanSectors

/-!
# Initial region identifiers and their closed cover

The initial family consists of the dummy neighborhood, the retained primary
regions at every layer, and the equal-colored runs in every belt cell.
An identifier keeps its layer and its primary or cell index. A primary
may have disconnected pieces, while distinct runs remain distinct even when
their colors agree.

Each identifier determines its closed birth region, its initial open interior,
and its color. The run color descends through the connected component;
no representative triangle is selected. For a nonempty endpoint set the closed
birth regions cover the plane, by the fine-cell exhaustion. Coverage of
lattice sites by open interiors and disjointness of those interiors remain
separate assertions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.initialRegionColor_ne_of_segment_subset_inter`: opposite colors
  across initial interfaces.
* `TNLean.PEPS.AreaLaw.Geometry.cellFanRunRegions_disjoint_interiors`,
  `TNLean.PEPS.AreaLaw.Geometry.initialOpenRegion_pairwise_disjoint`: disjoint interiors of initial
  birth regions.
* `TNLean.PEPS.AreaLaw.Geometry.initialBirthRegion_eq_closure_initialOpenRegion`: regularity of
  initial birth regions.
-/

section InitialRegions

noncomputable section

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

private def runColor (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) (family : CellFanSlot split → Fin 2) :
    CellFanRun o ℓ z split family → Fin 2 :=
  SimpleGraph.ConnectedComponent.lift family fun i j p _ ↦
    cellFanRun_color_eq o ℓ z split family i j
      (SimpleGraph.ConnectedComponent.sound p.reachable)

/-- An initial identifier is the dummy, a retained primary together
with its layer, or a belt-cell run together with its layer and cell.
Source: area-law Section 11, `prop:two-families`, lines 172–177,
212–218 and 299–323. -/
def InitialRegionIndex (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) : Type :=
  Unit ⊕ ((Σ k : {k : ℕ // k₀ ≤ k},
    {J : ℤ × ℤ // J ∈ primaryPitchIndices o k.val (fineScaleIndex k.val)
      (pitchScaleIndex k.val) Z C (a k.val).val (b k.val).val}) ⊕
    (Σ k : {k : ℕ // k₀ ≤ k},
      Σ z : {z : ℤ × ℤ // z ∈ beltCellIndices
        (fineLayerIndices o k.val (fineScaleIndex k.val) Z C)
        (2 ^ (pitchScaleIndex k.val - fineScaleIndex k.val)) (a k.val) (b k.val)},
        CellFanRun o (fineScaleIndex k.val) z.val
          (fineLayerSplitMask o k₀ k.val Z C z.val)
          (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property)))

/-- The closed birth region of an initial identifier, before any repair.
Source: area-law Section 11, `prop:two-families`, lines 172–177,
212–218 and 308–316. -/
def initialBirthRegion (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → Set (ℝ × ℝ)
  | .inl _ => closure (dyadicNeighborhood o k₀ Z C)
  | .inr (.inl ⟨k, J⟩) => primaryBirthRegion o k.val (fineScaleIndex k.val)
      (pitchScaleIndex k.val) Z C (a k.val).val (b k.val).val J.val
  | .inr (.inr ⟨k, z, R⟩) => cellFanRunRegion o (fineScaleIndex k.val) z.val
      (fineLayerSplitMask o k₀ k.val Z C z.val)
      (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R

/-- The initial open region is the interior of its closed birth region.
Source: area-law Section 11, `prop:two-families`, lines 172–177,
212–218 and 313–316. -/
def initialOpenRegion (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex o k₀ Z C a b hC h₀) : Set (ℝ × ℝ) :=
  interior (initialBirthRegion o k₀ Z C a b hC h₀ i)

/-- Dummy and primary identifiers have their prescribed layer parity; a belt
run has the color descended from its component.
Source: area-law Section 11, `prop:two-families`, lines 172–174,
212–218 and 299–323. -/
def initialRegionColor (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → Fin 2
  | .inl _ => ((k₀ - 1 : ℕ) : Fin 2)
  | .inr (.inl ⟨k, _⟩) => (k.val : Fin 2)
  | .inr (.inr ⟨k, z, R⟩) => runColor o (fineScaleIndex k.val) z.val
      (fineLayerSplitMask o k₀ k.val Z C z.val)
      (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R

/-- The color of a belt-run identifier equals the color of every
constituent triangle. Source: area-law Section 11, `prop:two-families`,
lines 313–318. -/
theorem initialRegionColor_beltRun_eq (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (z : ℤ × ℤ) (hk₀ : k₀ ≤ k)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)) (hi : i ∈ R.supp) :
    initialRegionColor o k₀ Z C a b hC h₀ (.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hz⟩, R⟩)) =
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i := by
  change runColor o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R = _
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff R i).mp hi]
  exact SimpleGraph.ConnectedComponent.lift_mk

/-- The closed birth regions cover the plane when the endpoint set is
nonempty. Source: area-law Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–316. -/
theorem initialBirthRegions_cover (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hZ : Z.Nonempty) :
    (⋃ i : InitialRegionIndex o k₀ Z C a b hC h₀,
      initialBirthRegion o k₀ Z C a b hC h₀ i) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ dyadicNeighborhood o k₀ Z C
  · exact Set.mem_iUnion.mpr ⟨.inl (), subset_closure hx⟩
  · obtain ⟨⟨k, z⟩, ⟨hk₀, hz, hxz⟩, _⟩ :=
      exists_unique_fineCell_of_not_mem_dyadicNeighborhood o Z C k₀ hZ hC x hx
    have hclosed : x ∈ closure (dyadicCell o (fineScaleIndex k) z) := subset_closure hxz
    by_cases hb : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
    · have hcover := cellFanRunRegions_cover o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hb)
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hclosed)
      exact Set.mem_iUnion.mpr ⟨.inr (.inr ⟨⟨k, hk₀⟩, ⟨z, hb⟩, R⟩), hxR⟩
    · obtain ⟨J, ⟨hJ, hsub⟩, _⟩ := exists_unique_primary_of_nonbeltCell o k
        (fineScaleIndex k) (pitchScaleIndex k) Z C (a k) (b k) z
        (fineScaleIndex_le k) ((fineScaleIndex_le k).trans (le_pitchScaleIndex k)) hz hb
      exact Set.mem_iUnion.mpr ⟨.inr (.inl ⟨⟨k, hk₀⟩, ⟨J, hJ⟩⟩), hsub hclosed⟩

end TNLean.PEPS.AreaLaw.Geometry

end

end InitialRegions

section InitialRegionInterfaces

/-!
## Opposite colors across initial interfaces

Two distinct actual initial identifiers have opposite colors whenever their
birth regions share an entire nondegenerate segment. The established run
interface theorems handle contacts involving belt runs. A contact between two
primaries forces neighboring layers, since primaries in one layer and
nonadjacent layers are separated. A primary contacting the dummy belongs
to the first layer and therefore has the opposite dummy parity.

The origin, endpoint set, and selected residues are arbitrary. The hypothesis
is a shared nondegenerate segment; two isolated common points of disconnected
regions are not asserted to constitute a positive-length interface. This
concerns the initial construction before stars and recursive repairs.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, prop:two-families, lines 172–177,
212–218 and 299–323; geometry:nonadjacent, lines 193–198; and
geometry:primary-pieces, lines 246–249.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Consecutive natural indices have opposite parity.
Auxiliary to Section 11, prop:two-families, lines 172–174 and 319–323. -/
private theorem parity_succ_ne (k : ℕ) : (k : Fin 2) ≠ ((k + 1 : ℕ) : Fin 2) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natCast] at hv
  omega

/-- Actual contact between distinct primaries forces opposite layer parities.
Source: Section 11, geometry:nonadjacent, lines 193–198;
geometry:primary-pieces, lines 246–249; prop:two-families, lines 319–323. -/
private theorem primary_contact_parities_ne (o : ℝ × ℝ) (k h : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (J K : ℤ × ℤ) (hC : 2 ≤ C) (hk : 50000000 ≤ k)
    (hne : (k, J) ≠ (h, K)) (x : ℝ × ℝ)
    (hx : x ∈ primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
      Z C (a k).val (b k).val J)
    (hy : x ∈ primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
      Z C (a h).val (b h).val K) : (k : Fin 2) ≠ (h : Fin 2) := by
  have hxD : x ∈ closure (dyadicLayer o k Z C) :=
    closure_mono Set.inter_subset_left hx
  have hyD : x ∈ closure (dyadicLayer o h Z C) :=
    closure_mono Set.inter_subset_left hy
  have hnear := dyadicLayer_nearby_indices o k h Z C x x hC hk hxD hyD
    (by simp only [dist_self]; positivity)
  have hkh : k ≠ h := by
    intro he
    subst h
    have hJK : J ≠ K := fun hJK ↦ hne (Prod.ext rfl hJK)
    have hsep := primaryBirthRegion_dist_separation o k (fineScaleIndex k)
      (pitchScaleIndex k) Z C (a k).val (b k).val J K hJK x x hx hy
    exact not_le_of_gt (pow_pos zero_lt_two (fineScaleIndex k))
      (by simpa only [dist_self] using hsep)
  have hadj : h = k + 1 ∨ k = h + 1 := by omega
  rcases hadj with he | he
  · subst h
    exact parity_succ_ne k
  · subst k
    exact (parity_succ_ne h).symm

/-- A primary contacting the dummy has the opposite initial parity.
Source: Section 11, prop:two-families, lines 172–177 and 319–323;
geometry:layer-distance, lines 179–191. -/
private theorem dummy_primary_parities_ne (o : ℝ × ℝ) (k₀ k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))) (J : ℤ × ℤ)
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hk₀ : k₀ ≤ k) (x : ℝ × ℝ)
    (hx : x ∈ closure (dyadicNeighborhood o k₀ Z C))
    (hy : x ∈ primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
      Z C a.val b.val J) : ((k₀ - 1 : ℕ) : Fin 2) ≠ (k : Fin 2) := by
  have hyD : x ∈ closure (dyadicLayer o k Z C) :=
    closure_mono Set.inter_subset_left hy
  have he := dyadicNeighborhood_contact_layer_eq o k₀ k Z C x hC hk₀ hx hyD
  have hsucc : k = (k₀ - 1) + 1 := by omega
  rw [hsucc]
  exact parity_succ_ne (k₀ - 1)

/-- Distinct actual initial identifiers sharing a nondegenerate segment have
opposite colors. The whole segment is required, rather than merely two isolated
common points. Source: Section 11, prop:two-families, lines 299–323. -/
theorem initialRegionColor_ne_of_segment_subset_inter (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i j : InitialRegionIndex o k₀ Z C a b hC h₀) (hij : i ≠ j)
    (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ i ∩
        initialBirthRegion o k₀ Z C a b hC h₀ j) :
    initialRegionColor o k₀ Z C a b hC h₀ i ≠
      initialRegionColor o k₀ Z C a b hC h₀ j := by
  classical
  have hu := hsegment (left_mem_segment ℝ u v)
  have hv := hsegment (right_mem_segment ℝ u v)
  rcases i with ⟨⟩ | (⟨k, J⟩ | ⟨k, z, R⟩) <;>
    rcases j with ⟨⟩ | (⟨h, K⟩ | ⟨h, w, T⟩) <;>
    simp only [initialBirthRegion] at hsegment hu hv
  · exact False.elim (hij rfl)
  · exact dummy_primary_parities_ne o k₀ h.val Z C (a h.val) (b h.val) K.val
      hC h₀ h.property u hu.1 hu.2
  · obtain ⟨t, ht⟩ := T.nonempty_supp
    have hcolors := beltCellFanRun_dummy_interface o k₀ Z C a b h.val w.val
      hC h₀ h.property w.property T u v huv
      (by simpa only [Set.inter_comm] using hsegment)
    rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ h.val w.val
      h.property w.property T t ht]
    exact (hcolors t ht).2.symm
  · exact (dummy_primary_parities_ne o k₀ k.val Z C (a k.val) (b k.val) J.val
      hC h₀ k.property u hu.2 hu.1).symm
  · apply primary_contact_parities_ne o k.val h.val Z C a b J.val K.val
      hC (h₀.trans k.property) ?_ u hu.1 hu.2
    intro he
    have hkh : k = h := Subtype.ext (congrArg Prod.fst he)
    subst h
    have hJK : J = K := Subtype.ext (congrArg Prod.snd he)
    subst K
    exact hij rfl
  · obtain ⟨t, ht⟩ := T.nonempty_supp
    have hcolors := beltCellFanRun_primary_interface o k₀ Z C a b h.val k.val
      w.val J.val hC h₀ h.property k.property w.property T u v huv
      (fun x hx ↦ ⟨(hsegment hx).2, (hsegment hx).1⟩)
    rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ h.val w.val
      h.property w.property T t ht]
    exact (hcolors.2 t ht).2.symm
  · obtain ⟨r, hr⟩ := R.nonempty_supp
    have hcolors := beltCellFanRun_dummy_interface o k₀ Z C a b k.val z.val
      hC h₀ k.property z.property R u v huv hsegment
    rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k.val z.val
      k.property z.property R r hr]
    exact (hcolors r hr).2
  · obtain ⟨r, hr⟩ := R.nonempty_supp
    have hcolors := beltCellFanRun_primary_interface o k₀ Z C a b k.val h.val
      z.val K.val hC h₀ k.property h.property z.property R u v huv hsegment
    rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k.val z.val
      k.property z.property R r hr]
    exact (hcolors.2 r hr).2
  · by_cases he : (k.val, z.val) = (h.val, w.val)
    · have hkh : k = h := Subtype.ext (congrArg Prod.fst he)
      subst h
      have hzw : z = w := Subtype.ext (congrArg Prod.snd he)
      subst w
      have hRT : R ≠ T := by
        intro hRT
        subst T
        exact hij rfl
      have hcontact := Set.nontrivial_of_mem_mem_ne hu hv huv
      have hcolors := cellFanRunRegions_contact_colors_ne o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val)
        (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property)
        R T hRT hcontact
      obtain ⟨r, hr⟩ := R.nonempty_supp
      obtain ⟨t, ht⟩ := T.nonempty_supp
      rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k.val z.val
        k.property z.property R r hr,
        initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k.val z.val
          k.property z.property T t ht]
      exact hcolors r hr t ht
    · have hcolors := beltCellFanRuns_interface_colors_ne o k₀ Z C a b k.val h.val
        z.val w.val hC h₀ k.property h.property z.property w.property R T he u v huv hsegment
      obtain ⟨r, hr⟩ := R.nonempty_supp
      obtain ⟨t, ht⟩ := T.nonempty_supp
      rw [initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k.val z.val
        k.property z.property R r hr,
        initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ h.val w.val
          h.property w.property T t ht]
      exact hcolors r hr t ht

end TNLean.PEPS.AreaLaw.Geometry

end InitialRegionInterfaces

section InitialRegionInteriors

/-!
## Disjoint interiors of initial birth regions

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

end

end InitialRegionInteriors

section InitialRegionRegularity

/-!
## Regularity of initial birth regions

Each actual initial birth region is the closure of its open interior. The
dummy and primary regions are finite unions of closed dyadic squares; a belt
run is a finite union of nondegenerate closed fan triangles. Finite unions
preserve this regularity, including empty unions and disconnected regions.

The nonzero determinant carried by each triangle implies nonempty interior.
One actual fan triangle supplies the same fact for a closed dyadic square.
No additional nonemptiness or regularity hypothesis is imposed, and no
finiteness of the entire initial family is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218 and 299–323, especially 308–316.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open ManyBody (ambientDilation)

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A closed dyadic square is the closure of its interior, which contains
the interior of an actual fan triangle.
Auxiliary to Section 11, `prop:two-families`, lines 154–177 and 299–310. -/
private theorem closed_cell_regular (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    closure (interior (closure (dyadicCell o ℓ z))) = closure (dyadicCell o ℓ z) := by
  let split : Fin 4 → Bool := fun _ ↦ false
  let i : CellFanSlot split := ⟨0, 0⟩
  have hn := (cellFanPolygon_interior_nonempty_and_closure_eq o ℓ z split i).1
  have hsub : (cellFanPolygon o ℓ z split i).region ⊆
      closure (dyadicCell o ℓ z) := by
    intro x hx
    exact (cellFanPolygons_cover o ℓ z split) ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
  have hint : (interior (closure (dyadicCell o ℓ z))).Nonempty :=
    hn.mono (interior_mono hsub)
  have hconv : Convex ℝ (dyadicCell o ℓ z) := by
    unfold dyadicCell
    exact (convex_Ico _ _).prod (convex_Ico _ _)
  simpa only [closure_closure] using
    hconv.closure.closure_interior_eq_closure_of_nonempty_interior hint

/-- A finite union of regions equal to the closures of their interiors has
the same property, including the empty union.
Auxiliary to Section 11, `prop:two-families`, lines 154–177, 212–218 and 313–316. -/
private theorem finite_biUnion_regular {ι : Type*} (F : Set ι) (hF : F.Finite)
    (P : ι → Set (ℝ × ℝ))
    (hreg : ∀ i ∈ F, closure (interior (P i)) = P i) :
    closure (interior (⋃ i ∈ F, P i)) = ⋃ i ∈ F, P i := by
  have hclosed : ∀ i ∈ F, IsClosed (P i) := by
    intro i hi
    rw [← hreg i hi]
    exact isClosed_closure
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (hF.isClosed_biUnion hclosed)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    rw [← hreg i hi] at hxi
    exact closure_mono (interior_mono (fun y hy ↦ Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)) hxi

/-- Every actual initial birth region is the closure of its initial open
interior. Empty endpoint sets and empty or disconnected regions are allowed.
Source: Section 11, `prop:two-families`, lines 154–177, 212–218 and 299–323,
especially 308–316. -/
theorem initialBirthRegion_eq_closure_initialOpenRegion
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (i : InitialRegionIndex o k₀ Z C a b hC h₀) :
    initialBirthRegion o k₀ Z C a b hC h₀ i =
      closure (initialOpenRegion o k₀ Z C a b hC h₀ i) := by
  classical
  rcases i with ⟨⟩ | (⟨k, J⟩ | ⟨k, z, R⟩)
  · change closure (dyadicNeighborhood o k₀ Z C) =
      closure (interior (closure (dyadicNeighborhood o k₀ Z C)))
    have hN : closure (dyadicNeighborhood o k₀ Z C) =
        ⋃ w ∈ ambientDilation (occupiedCellIndices o k₀ Z) C,
          closure (dyadicCell o k₀ w) := by
      rw [dyadicNeighborhood, Finset.closure_biUnion]
    simp only [hN]
    exact (finite_biUnion_regular _ (Finset.finite_toSet _)
      (fun w ↦ closure (dyadicCell o k₀ w))
      (fun w _ ↦ closed_cell_regular o k₀ w)).symm
  · change primaryBirthRegion o k.val (fineScaleIndex k.val) (pitchScaleIndex k.val)
        Z C (a k.val).val (b k.val).val J.val =
      closure (interior (primaryBirthRegion o k.val (fineScaleIndex k.val)
        (pitchScaleIndex k.val) Z C (a k.val).val (b k.val).val J.val))
    have hP := primaryBirthRegion_eq_iUnion_nonbeltCell_closure o k.val
      (fineScaleIndex k.val) (pitchScaleIndex k.val) Z C (a k.val) (b k.val) J.val
      (fineScaleIndex_le k.val)
      ((fineScaleIndex_le k.val).trans (le_pitchScaleIndex k.val))
    simp only [hP]
    exact (finite_biUnion_regular _ (Finset.finite_toSet _)
      (fun w ↦ closure (dyadicCell o (fineScaleIndex k.val) w))
      (fun w _ ↦ closed_cell_regular o (fineScaleIndex k.val) w)).symm
  · change cellFanRunRegion o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val)
        (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R =
      closure (interior (cellFanRunRegion o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val)
        (beltCellFanColor o k₀ Z C a b k.val z.val hC h₀ k.property z.property) R))
    simp only [cellFanRunRegion]
    exact (finite_biUnion_regular R.supp R.supp.toFinite
      (fun j ↦ (cellFanPolygon o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val) j).region)
      (fun j _ ↦ (cellFanPolygon_interior_nonempty_and_closure_eq o (fineScaleIndex k.val) z.val
        (fineLayerSplitMask o k₀ k.val Z C z.val) j).2)).symm

end TNLean.PEPS.AreaLaw.Geometry

end

end InitialRegionRegularity
