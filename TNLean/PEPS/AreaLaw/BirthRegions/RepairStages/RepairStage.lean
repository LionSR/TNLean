/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.InitialMarkFamily
import TNLean.PEPS.AreaLaw.BirthRegions.InitialRegions.InitialRegions
import TNLean.PEPS.AreaLaw.BirthRegions.RepairStages.RepairCurrentAssignments
import Mathlib.Algebra.BigOperators.Finprod
import TNLean.PEPS.AreaLaw.BirthRegions.Layers.PolynomialBudget

/-!
# The recursive repair family

A stage remembers the identifiers, closed birth regions, current open regions,
and labels of all regions created so far. It also records the current mark
occurrences with their locations and assigned scales. The distinguished dummy
identifier provides a value for the total sector choice. No coverage,
separation, star, coloring, or termination assertion is part of these data.

The initial stage uses one joint choice of belt residues, finite initial marks,
and least incident scales. At each later stage the sector assignment is read
from that stage's current open regions. All old regions are cut by the same
removal union before new regions are added. Fresh identifiers keep their
generation, parent occurrence, and connected run; mark occurrences keep their
generation, parent occurrence, and one of the nine offsets.

The definitions are total. Their agreement with the geometric construction
requires the local assignment and repair induction. In particular, neither
the existence of an assigned region for each working wedge nor eventual
termination is asserted here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial marks, lines 325–363; replacement
instructions, lines 393–417; `geometry:repair-induction`, lines 471–514;
open actual regions and closed births, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Facts about the chosen initial repair marks

The initial repair stage uses one joint choice of belt residues, a finite
mark set, and incident scales. The theorem below records the sparse cell
counts, finite layer support, incidence, scale minimality, separation, and
injectivity for those same choices. It introduces no new mark family or
choice of residues. Its incidence and scale facts serve both the geometric
induction and the weighted count of descendants.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:belt-count` and
`geometry:initial-stars`, lines 212–233 and 325–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Geometry.initialRepairStage_weighted_sum_le`,
  `TNLean.PEPS.AreaLaw.Geometry.exists_uniform_initialRepairStage_weighted_sum_bound`: uniform
  weighted sums over the actual initial repair marks.
-/

open ManyBody (boundaryEndpoints fineLayerIndices)

section RepairStage

section

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The data at one stage of simultaneous repair. The identifier types may
change at the next stage; all remembered births and labels are retained under
the old-identifier inclusion. The distinguished identifier is the original
dummy and does not assert that its current region is nonempty.
Source: area-law Section 11, lines 393–417, 471–514 and 558–561. -/
structure RepairStage where
  /-- Region identifiers at this stage.
  Source: area-law Section 11, lines 398–407 and 558–561. -/
  regionIndex : Type
  /-- The retained dummy identifier.
  Source: area-law Section 11, lines 172–177 and 558–561. -/
  dummy : regionIndex
  /-- The remembered closed birth of each region.
  Source: area-law Section 11, lines 404–417 and 558–561. -/
  birth : regionIndex → Set (ℝ × ℝ)
  /-- The current region after all preceding simultaneous removals.
  Source: area-law Section 11, lines 398–399 and 558–561. -/
  current : regionIndex → Set (ℝ × ℝ)
  /-- The binary label attached to each region identifier.
  Source: area-law Section 11, lines 404–407 and 497–504. -/
  color : regionIndex → Fin 2
  /-- Current mark occurrences, retaining their parent histories.
  Source: area-law Section 11, lines 404–409 and 506–514. -/
  markIndex : Type
  /-- The location of each current mark occurrence.
  Source: area-law Section 11, lines 404–409 and 506–514. -/
  location : markIndex → ℝ × ℝ
  /-- The scale assigned to each current mark occurrence.
  Source: area-law Section 11, lines 404–409 and 506–514. -/
  scale : markIndex → ℝ

/-- The initial stage uses the same jointly selected belt residues, finite
mark set, and least incident scales furnished by the initial-mark theorem.
No second choice of residues is made for the region family. Its dummy is the
existing unit summand, and its mark carrier is the selected finite set itself.
Source: area-law Section 11, lines 212–233 and 325–363. -/
def initialRepairStage (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    RepairStage :=
  let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let a := Classical.choose h
  let hb := Classical.choose_spec h
  let b := Classical.choose hb
  let hab := Classical.choose_spec hb
  let hM := hab.2.2
  let M := Classical.choose hM
  let hS := (Classical.choose_spec hM).2.2
  { regionIndex := InitialRegionIndex o k₀ (boundaryEndpoints Λ A) C a b hC h₀
    dummy := .inl ()
    birth := initialBirthRegion o k₀ (boundaryEndpoints Λ A) C a b hC h₀
    current := initialOpenRegion o k₀ (boundaryEndpoints Λ A) C a b hC h₀
    color := initialRegionColor o k₀ (boundaryEndpoints Λ A) C a b hC h₀
    markIndex := M
    location := fun p ↦ p.val
    scale := Classical.choose hS }

/-- One actual recursive step reads its assignment from the current family
before removal. It retains every old identifier, birth and label and gives
fresh regions the generation-parent-run identifiers of the existing repair
operation. All current parent squares are removed, including terminal ones;
only nonterminal parents contribute replacement regions and nine children.
The inherited dummy supplies nonemptiness for the total assignment choice.
Source: area-law Section 11, lines 393–417 and 486–514. -/
def repairNextStage (j : ℕ) (Sstar : ℝ) (D : RepairStage) : RepairStage :=
  letI : Nonempty D.regionIndex := ⟨D.dummy⟩
  let σ := repairCurrentAssignments D.current D.location D.scale
  { regionIndex := RepairRegionIndex j D.scale Sstar D.color σ
    dummy := .inl D.dummy
    birth := repairNextBirthRegion j D.birth D.location D.scale Sstar D.color σ
    current := repairNextCurrentRegion j D.current D.location D.scale Sstar D.color σ
    color := repairNextRegionColor j D.scale Sstar D.color σ
    markIndex := RepairNextMarkIndex j D.scale Sstar
    location := repairNextMarkLocation j D.location D.scale Sstar
    scale := repairNextMarkScale j D.scale Sstar }

/-- The actual stage family starts with the jointly chosen initial regions
and marks and repeatedly reads the current family to perform the next repair.
It is defined for every natural-number generation; no termination assertion
or external sequence of sector assignments is supplied.
Source: area-law Section 11, lines 393–417 and 471–514. -/
def repairStage (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) : ℕ → RepairStage :=
  Nat.rec (initialRepairStage o Λ A C k₀ hC h₀)
    (fun j D ↦ repairNextStage j Sstar D)

/-- The accumulated terminal-interior contribution from all generations is
the union of the interiors of terminal removal squares. It does not include
unassigned interface points and is not identified with the full exceptional
remainder or a lattice partition.
Source: area-law Section 11, lines 398–409 and 558–561. -/
def repairTerminalInteriors (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) : Set (ℝ × ℝ) :=
  ⋃ j : ℕ,
    let D := repairStage o Λ A C k₀ hC h₀ Sstar j
    repairTerminalInteriorSet D.location D.scale Sstar

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

open ManyBody (edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The sparse cells and geometric properties attached to the actual initial
repair stage, with the exact residue choices used in its definition.
Source: area-law Section 11, `geometry:belt-count` and
`geometry:initial-stars`, lines 212–233 and 325–363. -/
theorem initialRepairStage_mark_spec (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset ↥Λ) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    let h := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose h
    let hb := Classical.choose_spec h
    let b := Classical.choose hb
    let F := fun k => beltCellIndices
      (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
    let D := initialRepairStage o Λ A C k₀ hC h₀
    (∀ k, ((F k).card : ℝ) ≤
      64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) ∧
    Set.Finite {k | (F k).Nonempty} ∧
    (∀ p : D.markIndex, 0 < D.scale p ∧ ∃ k z,
      k₀ ≤ k ∧ z ∈ F k ∧ D.location p ∈ beltCellMarks o (fineScaleIndex k) z ∧
        D.scale p = (2 : ℝ) ^ fineScaleIndex k) ∧
    (∀ (p : D.markIndex) (k : ℕ) (z : ℤ × ℤ),
      k₀ ≤ k → z ∈ F k → D.location p ∈ beltCellMarks o (fineScaleIndex k) z →
        D.scale p ≤ (2 : ℝ) ^ fineScaleIndex k) ∧
    (∀ p q : D.markIndex, p ≠ q →
      max (D.scale p) (D.scale q) / 4 ≤ dist (D.location p) (D.location q)) ∧
    Function.Injective D.location := by
  let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let hab := Classical.choose_spec (Classical.choose_spec hchoice)
  let hspec := Classical.choose_spec (Classical.choose_spec hab.2.2).2.2
  exact ⟨hab.1, hab.2.1, hspec.1, hspec.2.1, hspec.2.2, Subtype.val_injective⟩

end TNLean.PEPS.AreaLaw.Geometry
end

end

end RepairStage

section RepairInitialWeightedCount

/-!
## Uniform weighted sums over the actual initial repair marks

Fix a real exponent. One positive numerical budget bounds every weighted sum
over the actual initial repair marks when each root's scale gives the stated
polynomial upper bound on its weight. The budget is chosen before the
coefficient, origin, domain, cut, width, lower layer, and weights.

The selected cells and marks are those of the existing joint initial choice.
The coefficient 576 is the product of the nine-mark bound and the sparse-cell
coefficient 64. The sum is written as a finite-support sum over the actual
initial carrier; its finiteness follows from the chosen finite mark set.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, sparse belt cells and initial marks,
lines 212–233 and 325–363; `geometry:total-repairs`, lines 668–692,
especially the weighted sum in lines 683–692.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators
open ManyBody (edgeBoundary planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Weighted sums over the actual initial roots, with an explicit budget.**
The weight hypothesis uses the actual root scale and applies at every
admissible upper layer; the budget is `polynomialDyadicBudget P`.
Source: area-law Section 11, lines 212–233 and 325–363;
`geometry:total-repairs`, lines 668–692, especially 683–692. -/
theorem initialRepairStage_weighted_sum_le (P : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    let D := initialRepairStage o Λ A C k₀ hC h₀
    ∀ (w : D.markIndex → ℝ),
      (∀ (p : D.markIndex) (k : ℕ), k₀ ≤ k →
        D.scale p ≤ (2 : ℝ) ^ k → w p ≤ c * ((k : ℝ) + 1) ^ P) →
      (∑ᶠ p : D.markIndex, w p) ≤
        576 * c * polynomialDyadicBudget P * (2 * (C : ℝ) + 1) ^ 2 *
          (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  intro D w hw
  set B := polynomialDyadicBudget P
  have hbudget := sum_le_polynomialDyadicBudget P
  let : Fintype D.markIndex := by
    dsimp only [D, initialRepairStage]
    infer_instance
  rw [finsum_eq_sum_of_fintype]
  let F : ℕ → Finset (ℤ × ℤ) :=
    let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose hchoice
    let b := Classical.choose (Classical.choose_spec hchoice)
    fun k ↦ beltCellIndices
      (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
  obtain ⟨hFcard, _, hInc, _, _, hLocInj⟩ :=
    initialRepairStage_mark_spec o Λ A C k₀ hC h₀
  choose layer cell hlower hcell hloc hscale using fun p : D.markIndex ↦ (hInc p).2
  have hfiber (k : ℕ) :
      (Finset.univ.filter fun p : D.markIndex ↦ layer p = k).card ≤
        (beltMarks o (fineScaleIndex k) (F k)).card := by
    refine Finset.card_le_card_of_injOn D.location ?_ hLocInj.injOn
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with rfl
    exact Finset.mem_biUnion.mpr ⟨cell p, hcell p, hloc p⟩
  have hcount (k : ℕ) :
      (Finset.univ.filter fun p : D.markIndex ↦ layer p = k).card ≤ 9 * (F k).card :=
    (hfiber k).trans (card_beltMarks_le o (fineScaleIndex k) (F k))
  have hwlayer (p : D.markIndex) : w p ≤ c * ((layer p : ℝ) + 1) ^ P :=
    hw p (layer p) (hlower p) ((hscale p).le.trans
      (pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le (layer p))))
  let K : Finset ℕ := Finset.univ.image layer
  have hgroup : ∑ p, w p =
      ∑ k ∈ K, ∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p :=
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := K) (g := layer)
      (fun p _ ↦ Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩) w).symm
  have hsumlayer (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        ((Finset.univ.filter (fun p : D.markIndex ↦ layer p = k)).card : ℝ) *
          (c * ((k : ℝ) + 1) ^ P) := by
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul (Finset.univ.filter (fun p : D.markIndex ↦ layer p = k))
        w (c * ((k : ℝ) + 1) ^ P)
        (fun p hp ↦ (Finset.mem_filter.mp hp).2 ▸ hwlayer p)
  have hcap_nonneg (k : ℕ) : 0 ≤ c * ((k : ℝ) + 1) ^ P :=
    mul_nonneg hc (Real.rpow_nonneg (by positivity) P)
  have hcount_real (k : ℕ) :
      ((Finset.univ.filter (fun p : D.markIndex ↦ layer p = k)).card : ℝ) ≤
        9 * ((F k).card : ℝ) := by
    exact_mod_cast hcount k
  have hsumcount (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        (9 * ((F k).card : ℝ)) * (c * ((k : ℝ) + 1) ^ P) :=
    (hsumlayer k).trans (mul_le_mul_of_nonneg_right (hcount_real k) (hcap_nonneg k))
  have hsparse (k : ℕ) :
      (9 * ((F k).card : ℝ)) * (c * ((k : ℝ) + 1) ^ P) ≤
        (9 * (64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2))) *
            (c * ((k : ℝ) + 1) ^ P) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hFcard k) (by norm_num)) (hcap_nonneg k)
  have hrow (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        576 * c * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card *
          (((k : ℝ) + 1) ^ P *
            (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2)) := by
    convert (hsumcount k).trans (hsparse k) using 1
    ring
  rw [hgroup]
  refine (Finset.sum_le_sum (fun k _ ↦ hrow k)).trans ?_
  rw [← Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left (hbudget K)
    (show 0 ≤ 576 * c * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card by
      positivity) using 1
  ring

/-- A numerical budget for weighted sums over the actual initial roots,
chosen before the coefficient and all geometric data. The weight hypothesis
uses the actual root scale and applies at every admissible upper layer. The
budget is `polynomialDyadicBudget P` (`initialRepairStage_weighted_sum_le`).
Source: area-law Section 11, lines 212–233 and 325–363;
`geometry:total-repairs`, lines 668–692, especially 683–692. -/
theorem exists_uniform_initialRepairStage_weighted_sum_bound (P : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (c : ℝ), 0 ≤ c →
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ)
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀),
        let D := initialRepairStage o Λ A C k₀ hC h₀
        ∀ (w : D.markIndex → ℝ),
          (∀ (p : D.markIndex) (k : ℕ), k₀ ≤ k →
            D.scale p ≤ (2 : ℝ) ^ k → w p ≤ c * ((k : ℝ) + 1) ^ P) →
          (∑ᶠ p : D.markIndex, w p) ≤
            576 * c * B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card :=
  ⟨_, polynomialDyadicBudget_pos P, fun _ hc ↦ initialRepairStage_weighted_sum_le P hc⟩

end TNLean.PEPS.AreaLaw.Geometry

end

end RepairInitialWeightedCount
