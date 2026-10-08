/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.belt_run_primary_interface
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.beltCellFanRun_primary_interface
Source labels: prop:two-families
Source: Section 11, lines 212–218 and 299–323.

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.belt_runs_interface_colors
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.beltCellFanRuns_interface_colors_ne
Source labels: prop:two-families
Source: Section 11, lines 299–323.

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
import TNLean.PEPS.AreaLaw.Geometry.PrimaryFineCellCover
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite

/-!
# Positive-length interfaces of actual belt runs

A closed segment with distinct endpoints shared by an actual belt run and
a primary birth region identifies a retained primary and forces every
triangle of the run to have the opposite primary parity. A segment shared
by runs in distinct actual belt cells forces all their constituent colors
to differ. Arbitrary belt residue functions are allowed.

The shared segment is covered by finitely many actual triangle and cell
intersections. Infinitude extracts a two-point constituent contact. The
triangle face equalities reduce it to elementary-base contact, and the
existing local color rules and run color constancy give the conclusions.
Two isolated common corners are not substituted for a shared segment.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, Section 11, prop:two-families, lines 212–218 and 299–323.
Source revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Fin.NatCast

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem exists_nontrivial_inter_of_infinite_cover
    {X I : Type*} [Finite I] {S : Set X} {A : I → Set X}
    (hS : S.Infinite) (hcover : S ⊆ ⋃ i, A i) :
    ∃ i, (S ∩ A i).Nontrivial := by
  classical
  exact Classical.byContradiction fun hn ↦ hS
    ((Set.finite_iUnion fun i ↦
      (Set.not_nontrivial_iff.mp (not_exists.mp hn i)).finite).subset fun x hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
        Set.mem_iUnion.mpr ⟨i, hx, hi⟩)

private theorem segment_infinite {u v : ℝ × ℝ} (huv : u ≠ v) :
    (segment ℝ u v).Infinite := by
  rw [segment_eq_image_lineMap]
  exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
    (AffineMap.lineMap_injective ℝ huv).injOn

/-- A shared nondegenerate segment with an actual primary birth region derives
its retained index and the opposite primary parity for every triangle of the run.
Source: area-law Section 11, prop:two-families, lines 212–218 and 299–323. -/
theorem beltCellFanRun_primary_interface
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z J : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h) Z C
        (a h).val (b h).val J) :
    J ∈ primaryPitchIndices o h (fineScaleIndex h) (pitchScaleIndex h) Z C
        (a h).val (b h).val ∧
      ∀ i ∈ R.supp, beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i =
          (h : Fin 2) + 1 ∧
        beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠ (h : Fin 2) := by
  classical
  let T := (fineLayerIndices o h (fineScaleIndex h) Z C).filter (fun w ↦
    w ∉ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h) ∧
      nonbeltPitchIndex (fineScaleIndex h) (pitchScaleIndex h) (a h).val (b h).val w = J)
  have hprimary : primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
      Z C (a h).val (b h).val J =
      ⋃ w ∈ T, closure (dyadicCell o (fineScaleIndex h) w) :=
    primaryBirthRegion_eq_iUnion_nonbeltCell_closure o h (fineScaleIndex h)
      (pitchScaleIndex h) Z C (a h) (b h) J (fineScaleIndex_le h)
      ((fineScaleIndex_le h).trans (le_pitchScaleIndex h))
  have hcover : segment ℝ u v ⊆
      ⋃ q : {i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z) // i ∈ R.supp} ×
        {w : ℤ × ℤ // w ∈ T},
        (cellFanPolygon o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) q.1.val).region ∩
          closure (dyadicCell o (fineScaleIndex h) q.2.val) := by
    intro x hx
    have hxR := (hsegment hx).1
    have hxP := (hsegment hx).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxR
    rw [hprimary] at hxP
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxP
    exact Set.mem_iUnion.mpr ⟨(⟨i, hi⟩, ⟨w, hw⟩), hxi, hxw⟩
  obtain ⟨q, hcontact⟩ :=
    exists_nontrivial_inter_of_infinite_cover (segment_infinite huv) hcover
  rcases q with ⟨⟨i, hi⟩, ⟨w, hw⟩⟩
  have htriangle : ((cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i).region ∩
      closure (dyadicCell o (fineScaleIndex h) w)).Nontrivial :=
    hcontact.mono (fun _ hx ↦ hx.2)
  obtain ⟨hwfine, hwnot, hindex⟩ := Finset.mem_filter.mp hw
  have hne : (k, z) ≠ (h, w) := by
    intro he
    cases he
    exact hwnot hz
  rw [fineLayer_cellFanPolygon_inter_closedCell_eq o k h Z C z w
    (fineLayerSplitMask o k₀ k Z C z) i (Finset.mem_of_mem_filter z hz)
    hwfine hne] at htriangle
  have hlocal := beltCellFanColor_nonbelt_opponent o k₀ Z C a b k h z w
    hC h₀ hk₀ hh₀ hz hwfine hwnot i htriangle
  refine ⟨by simpa only [hindex] using hlocal.1, ?_⟩
  intro j hj
  have hsame := cellFanRun_color_eq o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) j i
    (((SimpleGraph.ConnectedComponent.mem_supp_iff R j).mp hj).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff R i).mp hi).symm)
  exact ⟨hsame.trans hlocal.2.2.1, hsame.symm ▸ hlocal.2.2.2⟩

/-- A shared nondegenerate segment between actual runs in distinct indexed belt
cells forces every constituent color of one run to differ from every color of the other.
Source: area-law Section 11, prop:two-families, lines 299–323. -/
theorem beltCellFanRuns_interface_colors_ne
    (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (h : ℕ) → Fin (2 ^ (pitchScaleIndex h - fineScaleIndex h)))
    (k h : ℕ) (z w : ℤ × ℤ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hk₀ : k₀ ≤ k) (hh₀ : k₀ ≤ h)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (hw : w ∈ beltCellIndices (fineLayerIndices o h (fineScaleIndex h) Z C)
      (2 ^ (pitchScaleIndex h - fineScaleIndex h)) (a h) (b h))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz))
    (T : CellFanRun o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w)
      (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw))
    (hne : (k, z) ≠ (h, w)) (u v : ℝ × ℝ) (huv : u ≠ v)
    (hsegment : segment ℝ u v ⊆
      cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) R ∩
      cellFanRunRegion o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w)
        (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw) T) :
    ∀ i ∈ R.supp, ∀ j ∈ T.supp,
      beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz i ≠
        beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw j := by
  classical
  have hcover : segment ℝ u v ⊆
      ⋃ q : {i : CellFanSlot (fineLayerSplitMask o k₀ k Z C z) // i ∈ R.supp} ×
        {j : CellFanSlot (fineLayerSplitMask o k₀ h Z C w) // j ∈ T.supp},
        (cellFanPolygon o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z) q.1.val).region ∩
        (cellFanPolygon o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w) q.2.val).region := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hsegment hx).1
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hsegment hx).2
    exact Set.mem_iUnion.mpr ⟨(⟨i, hi⟩, ⟨j, hj⟩), hxi, hxj⟩
  obtain ⟨q, hcontact⟩ :=
    exists_nontrivial_inter_of_infinite_cover (segment_infinite huv) hcover
  rcases q with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have htriangles : ((cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) i).region ∩
      (cellFanPolygon o (fineScaleIndex h) w
        (fineLayerSplitMask o k₀ h Z C w) j).region).Nontrivial :=
    hcontact.mono (fun _ hx ↦ hx.2)
  have hi_eq := fineLayer_cellFanPolygon_inter_closedCell_eq o k h Z C z w
    (fineLayerSplitMask o k₀ k Z C z) i (Finset.mem_of_mem_filter z hz)
    (Finset.mem_of_mem_filter w hw) hne
  have hj_eq := fineLayer_cellFanPolygon_inter_closedCell_eq o h k Z C w z
    (fineLayerSplitMask o k₀ h Z C w) j (Finset.mem_of_mem_filter w hw)
    (Finset.mem_of_mem_filter z hz) hne.symm
  have hbases : (segment ℝ
      (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i)
      (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) i) ∩
      segment ℝ
        (cellFanStart o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)
        (cellFanEnd o (fineScaleIndex h) w (fineLayerSplitMask o k₀ h Z C w) j)).Nontrivial :=
    htriangles.mono fun x hx ↦ by
      have hclosed_z : x ∈ closure (dyadicCell o (fineScaleIndex k) z) :=
        (cellFanPolygons_cover o (fineScaleIndex k) z
          (fineLayerSplitMask o k₀ k Z C z)) ▸ Set.mem_iUnion.mpr ⟨i, hx.1⟩
      have hclosed_w : x ∈ closure (dyadicCell o (fineScaleIndex h) w) :=
        (cellFanPolygons_cover o (fineScaleIndex h) w
          (fineLayerSplitMask o k₀ h Z C w)) ▸ Set.mem_iUnion.mpr ⟨j, hx.2⟩
      exact ⟨((Set.ext_iff.mp hi_eq x).mp ⟨hx.1, hclosed_w⟩).1,
        ((Set.ext_iff.mp hj_eq x).mp ⟨hx.2, hclosed_z⟩).1⟩
  have hcolors := beltCellFanColor_belt_contact o k₀ Z C a b k h z w
    hC h₀ hk₀ hh₀ hz hw hne i j hbases
  intro i' hi' j' hj'
  have hsameR := cellFanRun_color_eq o (fineScaleIndex k) z
    (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk₀ hz) i' i
    (((SimpleGraph.ConnectedComponent.mem_supp_iff R i').mp hi').trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff R i).mp hi).symm)
  have hsameT := cellFanRun_color_eq o (fineScaleIndex h) w
    (fineLayerSplitMask o k₀ h Z C w)
    (beltCellFanColor o k₀ Z C a b h w hC h₀ hh₀ hw) j' j
    (((SimpleGraph.ConnectedComponent.mem_supp_iff T j').mp hj').trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff T j).mp hj).symm)
  simpa only [hsameR, hsameT] using hcolors

end TNLean.PEPS.AreaLaw.Geometry
