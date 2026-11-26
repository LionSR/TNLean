/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairStage
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.TwoFamilyExplicitThresholds

/-!
# Retained identifiers and the order of birth

Each repair stage retains the old identifiers and adjoins the new replacement
identifiers. Iterating these inclusions compares an identifier at its birth
with the same identifier at a later stage. The natural-number rank places
primaries before initial belt regions and replacements in their generation
order. Identifiers born in the same class have the same rank.

The dummy is assigned rank zero so that the rank is defined on every
identifier. It remains excluded from the order on physical tile identifiers.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
and the ordering preceding `geometry:birth-separation`, lines 565–571.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Decrease of retained current regions

The current region of a retained identifier decreases at each repair step.
No metric estimate or termination assumption is needed: each old region loses
the common removal union.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 398–409,
and comparison with earlier actual regions, lines 584–591.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Coherence of retained current regions across generations

Retaining an identifier over two successive intervals gives the same current
region as retaining it over their combined interval. This equality of subsets
compares the existing canonical inclusions without identifying their dependent
codomain types.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Section 11, replacement instructions, lines 398–409, and current regions,
lines 558–561. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.initialRegionCharacteristicLength`,
  `TNLean.PEPS.AreaLaw.Geometry.repairStageCharacteristicLength`: characteristic lengths remembered
  at birth.
* `TNLean.PEPS.AreaLaw.Geometry.repairStage_positive_rank_length_lower_bound`,
  `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_repairStage_positive_rank_length_lower_bound`:
  uniform lower bounds for nonprimary birth lengths.
-/

section RepairBirthRank

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Initial primaries have rank zero and initial belt regions have rank one.
The dummy has rank zero for totality and is excluded from the physical order.
Source: area-law Section 11, ordering preceding `geometry:birth-separation`,
lines 565–568. -/
def initialRegionBirthRank (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => 1

/-- The canonical inclusion of an old identifier into the next repair stage.
Source: area-law Section 11, lines 398–407, and
`geometry:birth-separation`, lines 584–591. -/
def repairNextOldInclusion (j : ℕ) (Sstar : ℝ) (D : RepairStage) :
    D.regionIndex → (repairNextStage j Sstar D).regionIndex :=
  Sum.inl

/-- The canonical inclusion from generation j to generation j + l, obtained
by retaining the old identifier at each intervening step.
Source: area-law Section 11, lines 398–409, and the ordering preceding
`geometry:birth-separation`, lines 565–571. -/
def repairStageOldInclusion (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) (j : ℕ) :
    (l : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex →
      (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)).regionIndex :=
  Nat.rec
    (motive := fun l ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex →
        (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)).regionIndex)
    (fun i ↦ i)
    (fun l inclusion i ↦
      repairNextOldInclusion (j + l) Sstar
        (repairStage o Λ A C k₀ hC h₀ Sstar (j + l)) (inclusion i))

/-- Birth rank in the actual repair family. Initial ranks are inherited from
the same jointly chosen initial identifiers. Old identifiers retain their
rank, and a replacement born at step j receives rank j + 2.
Source: area-law Section 11, lines 404–409, and the ordering preceding
`geometry:birth-separation`, lines 565–568. -/
def repairStageBirthRank (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) :
    (j : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℕ :=
  Nat.rec
    (motive := fun j ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℕ)
    (let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
        o Λ A C k₀ hC h₀
      let a := Classical.choose h
      let hb := Classical.choose_spec h
      let b := Classical.choose hb
      initialRegionBirthRank o k₀ (boundaryEndpoints Λ A) C a b hC h₀)
    (fun j rank ↦ fun
      | .inl i => rank i
      | .inr _ => j + 2)

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Retaining an identifier can only decrease its current region.
Source: area-law Section 11, lines 398–409 and 584–591. -/
theorem repairStage_current_oldInclusion_subset (j n : ℕ)
    (i : (𝔇 j).regionIndex) :
    (𝔇 (j + n)).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i) ⊆
        (𝔇 j).current i := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact Set.sdiff_subset.trans ih

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The current region obtained by retaining an identifier over a combined
interval equals the current region obtained over the two successive intervals.
No mark-emptiness assumption is required. Source: area-law Section 11,
lines 398–409 and 558–561. -/
theorem repairStage_current_oldInclusion_add (j n m : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 (j + (n + m))).current
      (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j (n + m) i) =
        (𝔇 ((j + n) + m)).current
          (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar (j + n) m
            (repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar j n i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact congrArg₂ (fun U V : Set (ℝ × ℝ) ↦ U \ V) ih
      (congrArg (fun t ↦ repairRemovalSet (𝔇 t).location (𝔇 t).scale)
        (Nat.add_assoc j n m).symm)

end TNLean.PEPS.AreaLaw.Geometry
end

end

end RepairBirthRank

section RepairCharacteristicLength

/-!
## Characteristic lengths remembered at birth

An initial primary has its layer length r, an initial belt region has its
cell side u, and a replacement has the half-side u of its removal square.
These lengths are retained when an old identifier passes to a later stage.
For a replacement, the scanner template uses primitive scale 2u.

The dummy is assigned zero for totality and is excluded from the retained
physical identifiers. The order of identifiers is determined separately by
their initial class and generation of birth.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-scale`, lines 709–721;
belt and replacement scanner scales, lines 732–740; and the ordering
preceding `geometry:birth-separation`, lines 565–568.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The characteristic length of an initial identifier: r = 2^k for a
primary and u = t_k for a belt region. The primary length is the layer
length; the whole primary can have a larger pitch diameter. The dummy
has value zero for totality and is excluded from retained identifiers.
Source: area-law Section 11, `geometry:primary-scale`, lines 709–721;
initial belt scale, lines 732–734; and dummy exclusion, lines 565–568. -/
def initialRegionCharacteristicLength (o : ℝ × ℝ) (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    InitialRegionIndex o k₀ Z C a b hC h₀ → ℝ
  | .inl _ => 0
  | .inr (.inl ⟨k, _⟩) => (2 : ℝ) ^ k.val
  | .inr (.inr ⟨k, _, _⟩) => (2 : ℝ) ^ fineScaleIndex k.val

/-- The characteristic birth length in the actual repair family. Old
identifiers keep their value, and a fresh replacement receives the removal
half-side u computed from its parent scale at birth. Its scanner template
has primitive scale 2u. The initial identifiers use the same joint choice
as the actual initial stage.
Source: area-law Section 11, replacement creation, lines 398–409;
`geometry:primary-scale`, lines 709–721; and belt and replacement scanner
scales, lines 732–740. -/
def repairStageCharacteristicLength (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) :
    (j : ℕ) → (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℝ :=
  Nat.rec
    (motive := fun j ↦
      (repairStage o Λ A C k₀ hC h₀ Sstar j).regionIndex → ℝ)
    (let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
        o Λ A C k₀ hC h₀
      let a := Classical.choose h
      let hb := Classical.choose_spec h
      let b := Classical.choose hb
      initialRegionCharacteristicLength o k₀ (boundaryEndpoints Λ A) C a b hC h₀)
    (fun j length ↦ fun
      | .inl i => length i
      | .inr q =>
        repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar j).scale q.2.1.val))

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairCharacteristicLength

section RepairCharacteristicLengthLowerBound

/-!
## Uniform lower bounds for nonprimary birth lengths

Initial belt lengths tend to infinity with their dyadic layer. A replacement
is created only when its removal half-side is at least the stopping scale.
Old identifiers retain their characteristic lengths. Consequently, for any
prescribed lower bound, a sufficiently large initial layer and stopping scale
give that bound for every identifier of positive birth rank at every stage.
The initial-layer threshold depends only on the prescribed lower bound `U`; it
is the explicit layer `fineScaleIndexThreshold U = ⌈dyadicIndexThreshold U / ζ⌉₊`.

This is an auxiliary for the choice of scanner thresholds. It applies to all
actual identifiers of positive birth rank, including those whose current
regions are empty. It requires no metric or termination assertion.
Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, nonterminal replacements,
lines 398–409; belt and replacement scales, lines 732–740; and the threshold
choice following `geometry:fine-clearance`, lines 761–771.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry


/-- **Explicit uniform lower bound for nonprimary lengths.** Every prescribed
real lower bound `U` holds for the remembered lengths of all positive-rank
identifiers once the initial layer is at least `fineScaleIndexThreshold U` and
the stopping scale is at least `U`. The usual formation assumptions of the
actual repair family are retained.
Source: area-law Section 11, `10-geometry.tex`, lines 398–409, 732–740
and 761–771. -/
theorem repairStage_positive_rank_length_lower_bound (U : ℝ) (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C)
    (h₀ : 50000000 ≤ k₀) (hk : fineScaleIndexThreshold U ≤ k₀) (Sstar : ℝ)
    (hSstar : U ≤ Sstar) (N : ℕ) (i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex)
    (hi : 0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i) :
    U ≤ repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N i := by
  induction N with
  | zero =>
    rcases i with u | (p | b)
    · exact (Nat.lt_irrefl 0 hi).elim
    · exact (Nat.lt_irrefl 0 hi).elim
    · exact le_two_pow_fineScaleIndex_of_fineScaleIndexThreshold_le
        (hk.trans b.1.property)
  | succ N ih =>
    rcases i with i | q
    · exact ih i hi
    · exact hSstar.trans q.2.1.property

/-- Every prescribed real lower bound holds uniformly for the remembered
lengths of all positive-rank identifiers once the initial layer and stopping
scale are sufficiently large. The threshold is chosen before all geometric
data, the stopping scale and the generation; it is `fineScaleIndexThreshold U`
(`repairStage_positive_rank_length_lower_bound`).
Source: area-law Section 11, `10-geometry.tex`, lines 398–409, 732–740
and 761–771. -/
theorem exists_uniform_repairStage_positive_rank_length_lower_bound (U : ℝ) :
    ∃ K : ℕ, ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
      (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
      ∀ Sstar : ℝ, U ≤ Sstar → ∀ (N : ℕ)
        (i : (repairStage o Λ A C k₀ hC h₀ Sstar N).regionIndex),
        0 < repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N i →
        U ≤ repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N i :=
  ⟨fineScaleIndexThreshold U, repairStage_positive_rank_length_lower_bound U⟩

end TNLean.PEPS.AreaLaw.Geometry

end RepairCharacteristicLengthLowerBound
