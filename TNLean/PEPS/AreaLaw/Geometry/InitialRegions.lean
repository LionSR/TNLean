/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BeltFanColors
import TNLean.PEPS.AreaLaw.Geometry.FanRuns
import TNLean.PEPS.AreaLaw.Geometry.FineCellPartition

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
-/

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
