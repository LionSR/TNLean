/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellFanRunCount
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.Geometry.RepairStageSites

/-!
# Counting retained sampled regions after finitely many repairs

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

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
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
