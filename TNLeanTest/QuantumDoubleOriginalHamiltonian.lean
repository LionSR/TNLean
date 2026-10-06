/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleOriginalPreparation

/-! Nonabelian and full-space regressions for the original-spin quantum double. -/

noncomputable section
open scoped BigOperators Matrix
open TNLean.PEPS
namespace QuantumDoubleOriginalTest

section General
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "V" => TorusVertex width height
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "E" => Edge (torusGraph width height)
local notation "C" => (F → G)

-- No transport equality or commutation premise is supplied.
example (j : (V ⊕ V) ⊕ E) :
    quantumDoubleOriginalTerm (G := G) j = quantumDoubleKLatticeUnblockedTerm j :=
  quantumDoubleOriginalTerm_eq_unblocked j

example (j k : (V ⊕ V) ⊕ E) :
    Commute (quantumDoubleOriginalTerm (G := G) j) (quantumDoubleOriginalTerm k) :=
  quantumDoubleOriginalTerm_commute j k

-- Entire kernel dimension, not just one prepared ground vector.
example : Module.finrank ℂ (Matrix.mulVecLin
    (quantumDoubleOriginalHamiltonian (width := width) (height := height) (G := G))).ker =
      Nat.card (CommutingPairConjugacyClass G) :=
  finrank_ker_quantumDoubleOriginalHamiltonian

-- The exact normalized preparation counts controls with stabilizer multiplicity.
example :
    (fun σ : C => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) =
      (Fintype.card G : ℂ) ^ (2 * (width * height)) •
        (quantumDoubleOriginalGroundProjector *ᵥ Pi.single (1 : C) 1) :=
  quantumDoubleOriginalCheckerboard_eq_groundProjector_one

-- Every face index really is one fine-lattice unit square, with a bijective indexing.
example (j : (V ⊕ V) ⊕ E) :
    (match j with | .inl k => toricCodeARegion k | .inr e => toricCodeBRegion e) =
      toricCodeFinePlaquette (toricCodePlaquetteIndexEquiv j) :=
  toricCodePlaquetteIndexEquiv_region j

end General

local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩
private abbrev S₃ := Equiv.Perm (Fin 3)
private def s : S₃ := Equiv.swap 0 1
private def t : S₃ := Equiv.swap 1 2
private def u : S₃ := s * t
local notation "V" => TorusVertex 3 3
local notation "F" => TorusVertex 6 6
local notation "tile" => kitaevPeriodicTilingEquiv (width := 3) (height := 3)

example : s * t ≠ t * s := by decide
example : u ≠ u⁻¹ := by decide

-- Right-facing B acts by R on corner 0, and by L on corner 1, even at a seam.
example (v : V) (σ : F → S₃) :
    quantumDoubleOriginalBAction (torusRightEdge v) u σ (tile (v, 0)) =
      σ (tile (v, 0)) * u⁻¹ := by
  simp [quantumDoubleOriginalBAction, (tile).injective.eq_iff]

example (v : V) (σ : F → S₃) :
    quantumDoubleOriginalBAction (torusRightEdge v) u σ (tile (v, 1)) =
      u * σ (tile (v, 1)) := by
  simp [quantumDoubleOriginalBAction, (tile).injective.eq_iff]

-- The incoming right-facing corner rejects wrong-side multiplication for
-- noncommuting s,t, on a face crossing the horizontal periodic seam.
example :
    quantumDoubleOriginalBAction (torusRightEdge ((2, 2) : V)) s (fun _ => t)
      (tile ((2, 2), 0)) ≠ s * t := by
  simp only [quantumDoubleOriginalBAction, quantumDoubleOriginalBOutgoing_right,
    quantumDoubleOriginalBIncoming_right, Finset.mem_insert, Finset.mem_singleton,
    (tile).injective.eq_iff, Prod.mk.injEq]
  simp only [Fin.isValue, and_true]
  decide

-- Up-facing B has L at corner 0, R at corner 3, and spectators off its support.
example (v : V) (σ : F → S₃) :
    quantumDoubleOriginalBAction (torusUpEdge v) u σ (tile (v, 0)) =
      u * σ (tile (v, 0)) := by
  simp [quantumDoubleOriginalBAction, (tile).injective.eq_iff]

example (v : V) (σ : F → S₃) :
    quantumDoubleOriginalBAction (torusUpEdge v) u σ (tile (v, 3)) =
      σ (tile (v, 3)) * u⁻¹ := by
  simp [quantumDoubleOriginalBAction, (tile).injective.eq_iff]

example (v : V) (σ : F → S₃) :
    quantumDoubleOriginalBAction (torusRightEdge v) u σ (tile (v, 3)) = σ (tile (v, 3)) := by
  have hv : v ≠ (v.1 + 1, v.2) := by
    intro h
    have hh := congrArg Prod.fst h
    exact one_ne_zero (add_left_cancel (hh.symm.trans (add_zero v.1).symm))
  simp [quantumDoubleOriginalBAction, (tile).injective.eq_iff, hv]

private def innerConfig (p : F) : S₃ :=
  if p = tile ((0, 0), 0) then s
  else if p = tile ((0, 0), 1) then t
  else if p = tile ((0, 0), 2) then t * s
  else 1

-- This actual fine-spin inner A configuration is flat only in its arrow order.
example : quantumDoubleOriginalAHolonomy (.inl ((0, 0) : V)) innerConfig = 1 := by
  simp only [quantumDoubleOriginalAHolonomy, innerConfig, (tile).injective.eq_iff,
    Prod.mk.injEq]
  decide

example : innerConfig (tile ((0, 0), 3)) * innerConfig (tile ((0, 0), 2)) *
    innerConfig (tile ((0, 0), 1)) * innerConfig (tile ((0, 0), 0)) ≠ 1 := by
  simp only [innerConfig, (tile).injective.eq_iff, Prod.mk.injEq]
  decide

private def holeConfig (p : F) : S₃ :=
  if p = tile ((2, 0), 1) then s
  else if p = tile ((2, 2), 0) then t
  else if p = tile ((0, 2), 3) then t * s
  else 1

-- An actual hole A face crossing both periodic seams has the opposite
-- geometric orientation; reversing its physical-site product fails.
example : quantumDoubleOriginalAHolonomy (.inr ((2, 2) : V)) holeConfig = 1 := by
  simp only [quantumDoubleOriginalAHolonomy, holeConfig, (tile).injective.eq_iff,
    Prod.mk.injEq]
  decide

example : holeConfig (tile ((0, 0), 2)) * holeConfig (tile ((0, 2), 3)) *
    holeConfig (tile ((2, 2), 0)) * holeConfig (tile ((2, 0), 1)) ≠ 1 := by
  simp only [holeConfig, (tile).injective.eq_iff, Prod.mk.injEq]
  decide

end QuantumDoubleOriginalTest
