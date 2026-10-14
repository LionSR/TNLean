/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialMarkFamily
import TNLean.PEPS.AreaLaw.Geometry.InitialRegions
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentAssignments

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
-/

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
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
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
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) : ℕ → RepairStage :=
  Nat.rec (initialRepairStage o Λ A C k₀ hC h₀)
    (fun j D ↦ repairNextStage j Sstar D)

/-- The accumulated terminal-interior contribution from all generations is
the union of the interiors of terminal removal squares. It does not include
unassigned interface points and is not identified with the full exceptional
remainder or a lattice partition.
Source: area-law Section 11, lines 398–409 and 558–561. -/
def repairTerminalInteriors (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
    (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (Sstar : ℝ) : Set (ℝ × ℝ) :=
  ⋃ j : ℕ,
    let D := repairStage o Λ A C k₀ hC h₀ Sstar j
    repairTerminalInteriorSet D.location D.scale Sstar

end TNLean.PEPS.AreaLaw.Geometry
