/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialBeltCount
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.RepairStageSites
import TNLean.PEPS.AreaLaw.Geometry.RepairTotalMarkPrefixCount

/-!
# Counting initial belts and replacement regions

The identifiers of positive birth rank are precisely the initial belts and
the replacement regions. Their number at any finite generation is bounded
by the initial belt count plus eight times the number of preceding marks.
This count includes identifiers whose current regions have become empty.
Only the positive-rank subtype is asserted to be finite; the full initial
primary family is not counted.

Restricting to the existing retained sampled identifiers can only decrease
the count. The uniform mark estimate therefore gives a boundary bound for
the retained identifiers of positive rank, under the same metric hypotheses.
Its coefficient is chosen before all geometric data and the generation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, birth classes, lines 565–568;
`geometry:total-repairs`, lines 685–692; and the nonprimary contribution to
the final error sum, lines 796–798.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Positive-rank prefix count with an explicit coefficient.** The identifiers
of positive birth rank at generation `N` form a finite set, of size at most
`initialBeltCountConstant (2 C₀ + 1) ^ 2 |∂A|` plus eight times the preceding
actual mark count.
Source: area-law Section 11, birth classes, lines 565–568, and
`geometry:total-repairs`, lines 685–692. -/
theorem repairStage_positive_rank_prefix_le (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ) (N : ℕ) :
    let I : Type := {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex //
      0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i}
    Finite I ∧ (Nat.card I : ℝ) ≤
      initialBeltCountConstant * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card +
        8 * ∑ j ∈ Finset.range N,
          (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) := by
  classical
  set B := initialBeltCountConstant
  have hbelt := initial_belt_card_le
  induction N with
  | zero =>
    obtain ⟨hfinite, hcard⟩ := hbelt o Λ A C k₀ hC h₀
    let R := {i : (repairStage o Λ A C k₀ hC h₀ Sstar 0).regionIndex //
      0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar 0 i}
    let f : R → _ := fun
      | ⟨.inl _, hi⟩ => (Nat.not_lt_zero _ hi).elim
      | ⟨.inr (.inl _), hi⟩ => (Nat.not_lt_zero _ hi).elim
      | ⟨.inr (.inr i), _⟩ => i
    let g : _ → R := fun i ↦ ⟨.inr (.inr i), Nat.zero_lt_one⟩
    have hf : Function.Injective f :=
      (show Function.LeftInverse g f from by
        rintro ⟨i, hi⟩
        rcases i with _ | (_ | i)
        · exact (Nat.not_lt_zero _ hi).elim
        · exact (Nat.not_lt_zero _ hi).elim
        · rfl).injective
    let : Finite _ := hfinite
    let : Finite R := Finite.of_injective f hf
    refine ⟨inferInstance, ?_⟩
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] using
      ((Nat.cast_le (α := ℝ)).mpr (Nat.card_le_card_of_injective f hf)).trans hcard
  | succ j ih =>
    let D := repairStage o Λ A C k₀ hC h₀ Sstar j
    let R := {i : D.regionIndex // 0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar j i}
    let : Finite R := ih.1
    let : Nonempty D.regionIndex := ⟨D.dummy⟩
    let σ := repairCurrentAssignments D.current D.location D.scale
    let F := RepairReplacementIndex j D.scale Sstar D.color σ
    let : Finite D.markIndex :=
      finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j
    let : Finite F := inferInstance
    let P (i : (repairNextStage j Sstar D).regionIndex) : Prop :=
      0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (j + 1) i
    have hOld (i : D.regionIndex) (hi : P (.inl i)) :
        0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar j i := hi
    let f : {i // P i} → R ⊕ F :=
      Sum.map (Subtype.map id hOld) Subtype.val ∘ (Equiv.subtypeSum (p := P))
    have hf : Function.Injective f :=
      (Sum.map_injective.mpr
        ⟨Subtype.map_injective (f := id) hOld Function.injective_id, Subtype.val_injective⟩).comp
        (Equiv.subtypeSum (p := P)).injective
    refine ⟨show Finite {i // P i} from Finite.of_injective f hf, ?_⟩
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
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at hcard
    have hstep : (Nat.card {i // P i} : ℝ) ≤
        (Nat.card R : ℝ) + 8 * (Nat.card D.markIndex : ℝ) := by
      exact_mod_cast hcard.trans (Nat.add_le_add_left hF (Nat.card R))
    change (Nat.card {i : (repairStage o Λ A C k₀ hC h₀ Sstar (j + 1)).regionIndex //
      0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (j + 1) i} : ℝ) ≤ _ at hstep
    simpa only [D, Finset.sum_range_succ, mul_add, add_assoc] using
      hstep.trans (_root_.add_le_add ih.2 le_rfl)

/-- The ambient identifiers of positive birth rank are finite at every
generation. Their number is bounded by the uniform initial belt estimate
plus eight times the preceding actual mark count. No metric or termination
hypothesis is required. The coefficient is `initialBeltCountConstant`
(`repairStage_positive_rank_prefix_le`).
Source: area-law Section 11, birth classes, lines 565–568, and
`geometry:total-repairs`, lines 685–692. -/
theorem exists_uniform_repairStage_positive_rank_prefix_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ) (N : ℕ),
        let I : Type := {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex //
          0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i}
        Finite I ∧ (Nat.card I : ℝ) ≤
          B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card +
            8 * ∑ j ∈ Finset.range N,
              (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) :=
  ⟨_, initialBeltCountConstant_pos, repairStage_positive_rank_prefix_le⟩

/-- The retained positive-rank count coefficient `B + 8 M_t`, where
`B = initialBeltCountConstant` and `M_t = repairMarkCountConstant S_*`. It is
the coefficient `L_q` of the two-family decomposition. Auxiliary to the
explicit constant of Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`).
Source: area-law Section 11, `geometry:total-repairs`, lines 685–692, and the
nonprimary error contribution, lines 796–798. -/
def repairRetainedCountConstant (Sstar : ℝ) : ℝ :=
  initialBeltCountConstant + 8 * repairMarkCountConstant Sstar

/-- The retained positive-rank count coefficient is positive. -/
theorem repairRetainedCountConstant_pos (Sstar : ℝ) :
    0 < repairRetainedCountConstant Sstar :=
  add_pos initialBeltCountConstant_pos (mul_pos (by norm_num) (repairMarkCountConstant_pos _))

/-- **Retained positive-rank count with an explicit coefficient.** Under the
metric hypotheses, the retained sampled identifiers of positive birth rank at
every generation form a finite set of size at most
`repairRetainedCountConstant S_* (2 C₀ + 1) ^ 2 |∂A|`.
Source: area-law Section 11, `geometry:total-repairs`, lines 685–692, and
the nonprimary error contribution, lines 796–798. -/
theorem repairStage_retained_positive_rank_le {Sstar : ℝ} (hSstar : 1 < Sstar)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ)
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀) (N : ℕ) :
    let I : Type :=
      {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
        0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val}
    Finite I ∧ (Nat.card I : ℝ) ≤
      repairRetainedCountConstant Sstar * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  unfold repairRetainedCountConstant
  intro I
  set B := initialBeltCountConstant
  set M := repairMarkCountConstant Sstar
  have hprefix := repairStage_positive_rank_prefix_le
  have hmark := repairStage_markIndex_prefix_le hSstar
  let R := {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex //
    0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i}
  obtain ⟨hfinite, hcount⟩ := hprefix o Λ A C k₀ hC h₀ Sstar N
  let : Finite R := hfinite
  let f : I → R := fun i ↦ ⟨i.val.val, i.property⟩
  have hf : Function.Injective f := fun x y hxy ↦
    Subtype.ext (Subtype.ext (congrArg (fun z : R ↦ z.val) hxy))
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc
    (Nat.card I : ℝ) ≤ (Nat.card R : ℝ) := by
      exact_mod_cast Nat.card_le_card_of_injective f hf
    _ ≤ B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card +
        8 * ∑ j ∈ Finset.range N,
          (Nat.card (repairStage o Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) := hcount
    _ ≤ B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card +
        8 * (M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (hmark o Λ A C k₀ hC h₀ a₀ h N) (by norm_num))
    _ = _ := by ring

/-- A coefficient chosen before all geometric data bounds the retained
sampled identifiers of positive birth rank at every generation. Finiteness
is established for the actual subtype, and the metric hypotheses are exactly
those of the uniform mark estimate. No empty generation is assumed. The coefficient
is `repairRetainedCountConstant S_*` (`repairStage_retained_positive_rank_le`).
Source: area-law Section 11, `geometry:total-repairs`, lines 685–692, and
the nonprimary error contribution, lines 796–798. -/
theorem exists_uniform_repairStage_retained_positive_rank_bound {Sstar : ℝ}
    (hSstar : 1 < Sstar) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
        RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
          (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
        ∀ N : ℕ,
          let I : Type :=
            {i : (repairStage o Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
              0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i.val}
          Finite I ∧ (Nat.card I : ℝ) ≤
            L * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card :=
  ⟨_, repairRetainedCountConstant_pos Sstar, repairStage_retained_positive_rank_le hSstar⟩

end TNLean.PEPS.AreaLaw.Geometry
