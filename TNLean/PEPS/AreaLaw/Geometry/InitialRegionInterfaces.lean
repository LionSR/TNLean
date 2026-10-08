/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.initial_interface_colors
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.initialRegionColor_ne_of_segment_subset_inter
Source labels: prop:two-families, geometry:nonadjacent, geometry:primary-pieces,
geometry:layer-distance
Source: Section 11, prop:two-families, lines 172–177, 212–218 and 299–323; geometry:nonadjacent,
lines 193–198; geometry:primary-pieces, lines 246–249; geometry:layer-distance, lines 179–191.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.BeltRunInterfaces
import TNLean.PEPS.AreaLaw.Geometry.DummyRunInterfaces
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts
import TNLean.PEPS.AreaLaw.Geometry.LocalLayers

/-!
# Opposite colors across initial interfaces

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
