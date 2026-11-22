/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FinalRegions.RepairCurrentDisjointness
import TNLean.PEPS.AreaLaw.FinalRegions.RepairCurrentTerminalDisjointness
import TNLean.PEPS.AreaLaw.FinalRegions.RepairFinalRegion
import TNLean.PEPS.AreaLaw.FinalRegions.RepairLatticeCoverage
import TNLean.PEPS.AreaLaw.FinalRegions.RepairTermination
import TNLean.PEPS.AreaLaw.RepairStages.RepairBirthRank
import TNLean.PEPS.AreaLaw.RepairStages.RepairStageSites
import TNLean.PEPS.AreaLaw.Templates.Templates
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Exclusive final lattice coverage at an empty generation

At a generation without remaining marks, every current region avoids the
original accumulated terminal interiors. The final regions equal these
current regions. At the prescribed origin, every lattice point therefore
belongs either to the terminal interiors or to exactly one final region.
The identifier family includes the retained dummy.

The generation is supplied as part of the hypotheses. The metric hypotheses
suffice for terminal avoidance; the lower stopping-scale and positive-boundary
conditions are used only for lattice coverage at the prescribed origin.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–417;
`geometry:repair-induction`, lines 474–478 and 526–541; final lattice regions,
lines 545–561; and terminal exceptional sites, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The ordered partition of a cut at an empty repair generation

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

section

noncomputable section

open TNLean.Lattice
open ManyBody (edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

namespace RepairMetricHypotheses

section ArbitraryOrigin

variable {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A)
  (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- At an empty generation, every actual current region avoids the original
accumulated terminal interiors.
Source: area-law Section 11, lines 398–417; `geometry:repair-induction`,
lines 474–478 and 526–541; and final regions, lines 558–561. -/
theorem current_disjoint_terminalInteriors_of_isEmpty (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] (i : (𝔇 N).regionIndex) :
    Disjoint ((𝔇 N).current i)
      (repairTerminalInteriors o Λ A C k₀ hC h₀ Sstar) := by
  refine (h.current_disjoint_earlierTerminalSquares N i).mono_right ?_
  rw [repairTerminalInteriors_eq_iUnion_lt_of_isEmpty o Λ A C k₀ hC h₀ Sstar N]
  exact Set.iUnion_mono fun _ ↦ Set.iUnion_mono fun _ ↦
    Set.iUnion_mono fun _ ↦ interior_subset

end ArbitraryOrigin

section PrescribedOrigin

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A)
  (C := C) (k₀ := k₀) (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- Each lattice point belongs either to the original terminal interiors and
to no final region, or to exactly one final region and not to the terminal
interiors. All actual identifiers at the supplied empty generation are used,
including the dummy.
Source: area-law Section 11, positive-boundary convention, lines 102–105;
replacement instructions, lines 398–417; and lattice partition, lines 545–561. -/
theorem lattice_mem_terminal_or_unique_final_of_isEmpty
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary (planeDomainGraph Λ) A).card)
    (N : ℕ) [IsEmpty (𝔇 N).markIndex] (z : ℤ × ℤ) :
    (integerPoint z ∈ repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar ∧
      ∀ i : (𝔇 N).regionIndex,
        integerPoint z ∉ repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N i) ∨
    (integerPoint z ∉ repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar ∧
      ∃! i : (𝔇 N).regionIndex,
        integerPoint z ∈ repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N i) := by
  classical
  simp only [repairFinalRegion_eq_current_of_isEmpty]
  by_cases hz : integerPoint z ∈
      repairTerminalInteriors dyadicOrigin Λ A C k₀ hC h₀ Sstar
  · exact Or.inl ⟨hz, fun i hi ↦
      Set.disjoint_left.mp (h.current_disjoint_terminalInteriors_of_isEmpty N i) hi hz⟩
  · rcases h.lattice_mem_current_or_terminal_before hSstar hboundary N z with
      ⟨i, hi⟩ | ⟨t, _, htz⟩
    · refine Or.inr ⟨hz, i, hi, ?_⟩
      intro k hk
      by_contra hki
      exact Set.disjoint_left.mp (h.current_pairwise_disjoint N hki) hk hi
    · exact (hz (Set.mem_iUnion.mpr ⟨t, htz⟩)).elim

end PrescribedOrigin

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

open TNLean.Lattice
open ManyBody (edgeBoundary planeDomainGraph)

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
    (hSstar : 1 ≤ Sstar) (hboundary : 0 < (edgeBoundary (planeDomainGraph Λ) A).card)
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
end

end
