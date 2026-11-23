/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RepairStages.RepairStage
import Mathlib.Data.Set.Finite.Lattice
import TNLean.PEPS.AreaLaw.Fans.FanRuns
import TNLean.PEPS.AreaLaw.InitialRegions.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.RepairStages.RepairDescendantCounts

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

## Counting retained sampled regions after finitely many repairs

At every generation, only finitely many non-dummy current regions meet a
fixed finite cut. Their number is at most the initial number plus eight
times the total number of marks in the preceding generations. Old sampled
regions shrink, and every fresh region retains a parent mark and one of at
most eight fan runs. The estimate uses these identifiers even when later
regions overlap or parent locations coincide.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:total-repairs`, lines 682–691; and restriction to identifiers
meeting the cut, lines 777–789.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

open scoped Classical in
/-- The sites of the cut lying in the current region of a given identifier.
Source: area-law Section 11, final restriction to actual regions,
lines 777–789. -/
def RepairStage.regionSites (D : RepairStage) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (i : D.regionIndex) : Finset ↥Λ :=
  A.filter (fun x ↦ integerPoint x.val ∈ D.current i)

/-- The non-dummy identifiers whose current regions meet the cut.
Source: area-law Section 11, dummy exclusion in the ordering preceding
`geometry:birth-separation`, lines 565–568, and retained identifiers,
lines 777–780. -/
def RepairStage.RetainedRegionIndex (D : RepairStage) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) : Type :=
  {i : D.regionIndex // i ≠ D.dummy ∧ (D.regionSites Λ A i).Nonempty}

open scoped Classical in
/-- Sites of the cut in the current dummy at generation N or in a terminal
interior from any generation. The expression is defined for every N; its use
as the final exceptional set requires all terminal removals to be processed.
Source: area-law Section 11, final lattice partition, lines 558–561, and
`geometry:bad-sites`, lines 694–707. -/
def repairStageExceptionalSites (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) (N : ℕ) : Finset ↥Λ :=
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
    (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
    (hdisj : Pairwise fun i j ↦ Disjoint (D.current i) (D.current j)) :
    Finite (D.RetainedRegionIndex Λ A) := by
  exact Set.finite_coe_iff.mpr
    (((show {i : D.regionIndex | i ≠ D.dummy}.PairwiseDisjoint
        (fun i ↦ (D.regionSites Λ A i : Set ↥Λ)) from
      fun i _ j _ hij ↦ Set.disjoint_left.mpr
        (fun _ hx hy ↦ Set.disjoint_left.mp (hdisj hij)
          (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)).finite_biUnion_iff.mp
      (A.finite_toSet.subset (fun _ hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        let ⟨_, hxi⟩ := Set.mem_iUnion.mp hi
        (Finset.mem_filter.mp hxi).1))).2)

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The actual retained sampled identifiers are finite, and their number
at generation `N` is at most the initial number plus eight times the number
of preceding mark occurrences. Source: area-law Section 11, lines 393–417,
`geometry:total-repairs`, lines 682–691, and lines 777–789. This is the
finite-generation counting estimate. -/
theorem finite_and_card_repairStage_retainedRegionIndex_le (N : ℕ) :
    Finite ((𝔇 N).RetainedRegionIndex Λ A) ∧
      Nat.card ((𝔇 N).RetainedRegionIndex Λ A) ≤
        Nat.card ((𝔇 0).RetainedRegionIndex Λ A) +
          8 * ∑ j ∈ Finset.range N, Nat.card (𝔇 j).markIndex := by
  classical
  induction N with
  | zero =>
    refine ⟨RepairStage.finite_retainedRegionIndex (𝔇 0) Λ A ?_, by simp⟩
    exact initialOpenRegion_pairwise_disjoint o k₀ (boundaryEndpoints Λ A) C _ _ hC h₀
  | succ j ih =>
    let D := 𝔇 j
    let : Nonempty D.regionIndex := ⟨D.dummy⟩
    let σ := repairCurrentAssignments D.current D.location D.scale
    let F := RepairReplacementIndex j D.scale Sstar D.color σ
    let : Finite (D.RetainedRegionIndex Λ A) := ih.1
    let : Finite D.markIndex :=
      finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j
    let : Finite F := inferInstance
    let P (i : (repairNextStage j Sstar D).regionIndex) : Prop :=
      i ≠ (repairNextStage j Sstar D).dummy ∧
        ((repairNextStage j Sstar D).regionSites Λ A i).Nonempty
    have hOld (i : D.regionIndex) (hi : P (.inl i)) :
        i ≠ D.dummy ∧ (D.regionSites Λ A i).Nonempty := by
      refine ⟨fun he ↦ hi.1 (congrArg Sum.inl he), ?_⟩
      obtain ⟨x, hx⟩ := hi.2
      exact ⟨x, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩⟩
    let f : (𝔇 (j + 1)).RetainedRegionIndex Λ A → D.RetainedRegionIndex Λ A ⊕ F :=
      Sum.map (Subtype.map id hOld) Subtype.val ∘ (Equiv.subtypeSum (p := P))
    have hf : Function.Injective f :=
      (Sum.map_injective.mpr
        ⟨Subtype.map_injective hOld Function.injective_id, Subtype.val_injective⟩).comp
        (Equiv.subtypeSum (p := P)).injective
    let : Finite ((𝔇 (j + 1)).RetainedRegionIndex Λ A) := Finite.of_injective f hf
    refine ⟨inferInstance, ?_⟩
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at hcard
    have hF : Nat.card F ≤ 8 * Nat.card D.markIndex := by
      let : Fintype {p : D.markIndex // Sstar ≤ repairHalfSide (D.scale p)} :=
        Fintype.ofFinite _
      have htag : Nat.card {n : ℕ // n = j + 1} = 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
      dsimp only [F, RepairReplacementIndex]
      rw [Nat.card_prod, htag, one_mul, Nat.card_sigma]
      calc
        _ ≤ 8 * Nat.card {p : D.markIndex // Sstar ≤ repairHalfSide (D.scale p)} := by
          simpa only [Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
            Nat.card_eq_fintype_card, mul_comm]
            using (Finset.sum_le_card_nsmul Finset.univ
              (fun p : {p : D.markIndex // Sstar ≤ repairHalfSide (D.scale p)} ↦
                Nat.card (RepairFanRun D.color (σ p.val))) 8
              (fun _ _ ↦ card_cellFanRun_le_eight _ _ _ _ _))
        _ ≤ 8 * Nat.card D.markIndex := Nat.mul_le_mul_left 8 (Finite.card_subtype_le _)
    simpa only [Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc] using
      hcard.trans (Nat.add_le_add ih.2 hF)

end TNLean.PEPS.AreaLaw.Geometry
end

end
