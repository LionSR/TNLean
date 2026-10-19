/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairFinalLatticePartition
import TNLean.PEPS.AreaLaw.Geometry.RepairStageSites
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The ordered partition of a cut at an empty repair generation

At the prescribed origin, an empty generation of the repair construction
partitions the cut into its exceptional sites and the nonempty intersections
with the non-dummy current regions. Pairwise disjointness makes the retained
identifier family finite. Sorting its actual birth ranks then gives a common
order for the two inherited labels.

The resulting partition records an equivalence with the existing retained
identifiers, the exact regional pieces and labels, and the exact exceptional
set. Equal birth ranks are permitted, as is an empty family of pieces.
The metric hypotheses, lower stopping-scale bound, positive boundary, and
empty generation are supplied here. Template assignment and geometric
clearance are subsequent parts of the construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, the birth order, lines 565–568, and the
final restriction to the cut and finite partition, lines 777–780.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

namespace RepairMetricHypotheses

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar a₀ : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

/-- At a supplied empty generation, the actual retained regions form a finite
ordered partition of the cut, with their existing labels and with birth rank
nondecreasing along the common order. The residual set is exactly the actual
exceptional set. This is the partition step of the geometric construction.
Source: area-law Section 11, lines 565–568 and 777–780. -/
theorem exists_orderedTwoFamilyPartition_of_isEmpty
    (h : RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A)
      (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary Λ A).card)
    (N : ℕ) [IsEmpty (𝔇 N).markIndex] :
    ∃ P : OrderedTwoFamilyPartition A,
      ∃ e : Fin P.pieceCount ≃ (𝔇 N).RetainedRegionIndex Λ A,
        (∀ i, P.piece i = (𝔇 N).regionSites Λ A (e i).val) ∧
        (∀ i, P.family i = (𝔇 N).color (e i).val) ∧
        P.residual = repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N ∧
        Monotone (fun i ↦
          repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N (e i).val) := by
  classical
  let : Finite ((𝔇 N).RetainedRegionIndex Λ A) :=
    (𝔇 N).finite_retainedRegionIndex Λ A (h.current_pairwise_disjoint N)
  let e₀ := (Finite.equivFin ((𝔇 N).RetainedRegionIndex Λ A)).symm
  let e := (Tuple.sort (fun i ↦
    repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N (e₀ i).val)).trans e₀
  have hcover : A =
      repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N ∪
        Finset.univ.biUnion (fun i ↦ (𝔇 N).regionSites Λ A (e i).val) := by
    ext x
    simp only [repairStageExceptionalSites, RepairStage.regionSites, Finset.mem_union,
      Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_union]
    refine ⟨fun hx ↦ ?_, fun hx ↦ hx.elim And.left (fun hz ↦ hz.elim fun _ hi ↦ hi.1)⟩
    refine (h.lattice_mem_terminal_or_unique_final_of_isEmpty
      hSstar hboundary N x.val).elim
      (fun ht ↦ Or.inl ⟨hx, Or.inr ht.1⟩) (fun hc ↦ ?_)
    obtain ⟨i, hi, _⟩ := hc.2
    rw [repairFinalRegion_eq_current_of_isEmpty] at hi
    by_cases hid : i ≠ (𝔇 N).dummy
    · let r : (𝔇 N).RetainedRegionIndex Λ A :=
        ⟨i, hid, x, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
      refine Or.inr ⟨e.symm r, hx, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hi
    · exact Or.inl ⟨hx, Or.inl ((not_not.mp hid) ▸ hi)⟩
  refine ⟨{ pieceCount := Nat.card ((𝔇 N).RetainedRegionIndex Λ A)
            family := fun i ↦ (𝔇 N).color (e i).val
            piece := fun i ↦ (𝔇 N).regionSites Λ A (e i).val
            residual := repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N
            disjoint := ?_
            residual_disjoint := ?_
            cover := hcover }, e, fun _ ↦ rfl, fun _ ↦ rfl, rfl,
    Tuple.monotone_sort (fun i ↦
      repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N (e₀ i).val)⟩
  · exact fun i j hij ↦ Finset.disjoint_left.mpr fun _ hx hy ↦
      Set.disjoint_left.mp
        (h.current_pairwise_disjoint N (fun he ↦ hij (e.injective (Subtype.ext he))))
        (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  · exact fun i ↦ Finset.disjoint_left.mpr fun _ hx hxi ↦
      (Finset.mem_filter.mp hx).2.elim
        (fun hd ↦ Set.disjoint_left.mp (h.current_pairwise_disjoint N (e i).property.1)
          (Finset.mem_filter.mp hxi).2 hd)
        (fun ht ↦ Set.disjoint_left.mp (h.current_disjoint_terminalInteriors_of_isEmpty N _)
          (Finset.mem_filter.mp hxi).2 ht)

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
