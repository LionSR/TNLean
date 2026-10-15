/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairStage
import Mathlib.Data.Set.Finite.Lattice

/-!
# Lattice sites in the actual repair regions

A current region determines a finite subset of the cut by restricting its
lattice sites to that cut. The retained identifiers exclude the dummy and
require this subset to be nonempty. The exceptional sites are those in the
current dummy or in an accumulated terminal interior, restricted to the cut.

These families are defined at every generation. Their interpretation as the
final partition requires the repair induction and completed terminal processing.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 558–568;
`geometry:bad-sites`, lines 694–707; and the final restriction to the cut,
lines 777–789.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

open scoped Classical in
/-- The sites of the cut lying in the current region of a given identifier.
Source: area-law Section 11, final restriction to actual regions,
lines 777–789. -/
def RepairStage.regionSites (D : RepairStage) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (i : D.regionIndex) : Finset (Site Λ) :=
  A.filter (fun x ↦ integerPoint x.val ∈ D.current i)

/-- The non-dummy identifiers whose current regions meet the cut.
Source: area-law Section 11, dummy exclusion in the ordering preceding
`geometry:birth-separation`, lines 565–568, and retained identifiers,
lines 777–780. -/
def RepairStage.RetainedRegionIndex (D : RepairStage) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) : Type :=
  {i : D.regionIndex // i ≠ D.dummy ∧ (D.regionSites Λ A i).Nonempty}

open scoped Classical in
/-- Sites of the cut in the current dummy at generation N or in a terminal
interior from any generation. The expression is defined for every N; its use
as the final exceptional set requires all terminal removals to be processed.
Source: area-law Section 11, final lattice partition, lines 558–561, and
`geometry:bad-sites`, lines 694–707. -/
def repairStageExceptionalSites (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) (N : ℕ) : Finset (Site Λ) :=
  let D := repairStage o Λ A C k₀ hC h₀ Sstar N
  A.filter (fun x ↦ integerPoint x.val ∈
    D.current D.dummy ∪ repairTerminalInteriors o Λ A C k₀ hC h₀ Sstar)

open scoped Classical in
/-- Pairwise disjoint current regions have only finitely many non-dummy
identifiers meeting a finite cut. No finiteness of the ambient identifier
family is required.
Source: area-law Section 11, final restriction to actual regions,
lines 777–780. -/
theorem RepairStage.finite_retainedRegionIndex (D : RepairStage)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (hdisj : Pairwise fun i j ↦ Disjoint (D.current i) (D.current j)) :
    Finite (D.RetainedRegionIndex Λ A) := by
  exact Set.finite_coe_iff.mpr
    (((show {i : D.regionIndex | i ≠ D.dummy}.PairwiseDisjoint
        (fun i ↦ (D.regionSites Λ A i : Set (Site Λ))) from
      fun i _ j _ hij ↦ Set.disjoint_left.mpr
        (fun _ hx hy ↦ Set.disjoint_left.mp (hdisj hij)
          (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)).finite_biUnion_iff.mp
      (A.finite_toSet.subset (fun _ hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        let ⟨_, hxi⟩ := Set.mem_iUnion.mp hi
        (Finset.mem_filter.mp hxi).1))).2)

end TNLean.PEPS.AreaLaw.Geometry
