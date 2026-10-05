/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGraphBondBlocking

/-! # General-group physical bond separation, normalization, and axiom regressions -/

open TNLean.PEPS
open scoped Matrix

noncomputable section

-- No commutativity, connectedness, or valence hypothesis is present.
example {G K V : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype K] [DecidableEq K] [Fintype V] [LinearOrder V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    regularGraphBlocking (Γ := Γ) (G := G) K
        (graphBondNetwork (graphAveragingSite (regularBundleMatrix K))) =
      fun σ => (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^ Fintype.card (Edge Γ) *
        graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
          regularGraphNormalizedBell K σ.2 :=
  regularGraphBlocking_averagingSite_normalized K

-- A genuinely nonabelian group is permitted, with two regular bonds per edge.
example :
    regularGraphBlocking (Γ := (⊤ : SimpleGraph (Fin 3)))
        (G := Equiv.Perm (Fin 3)) Unit
        (graphBondNetwork (graphAveragingSite (regularBundleMatrix Unit))) =
      fun σ => graphBondNetwork (graphAveragingSite
          (leftRegularMatrix (Equiv.Perm (Fin 3)))) σ.1 *
        regularGraphResidualBell Unit σ.2 :=
  regularGraphBlocking_averagingSite Unit

example : (Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2 ≠
    (Equiv.swap (1 : Fin 3) 2) * Equiv.swap 0 1 := by decide

-- Empty graphs and isolated vertices are both covered.
example : star (regularGraphNormalizedBell (Γ := (⊥ : SimpleGraph (Fin 0)))
      (G := Equiv.Perm (Fin 3)) (Fin 4)) ⬝ᵥ regularGraphNormalizedBell (Fin 4) = 1 :=
  regularGraphNormalizedBell_dotProduct (Fin 4)

example : star (regularGraphNormalizedBell (Γ := (⊥ : SimpleGraph (Fin 3)))
      (G := Equiv.Perm (Fin 3)) (Fin 4)) ⬝ᵥ regularGraphNormalizedBell (Fin 4) = 1 :=
  regularGraphNormalizedBell_dotProduct (Fin 4)

-- An empty surplus family discards no bond coordinates.
example : star (regularGraphNormalizedBell (Γ := (⊤ : SimpleGraph (Fin 3)))
      (G := Equiv.Perm (Fin 3)) (Fin 0)) ⬝ᵥ regularGraphNormalizedBell (Fin 0) = 1 :=
  regularGraphNormalizedBell_dotProduct (Fin 0)

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.regularGraphBlocking_averagingSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularGraphBlocking_averagingSite

/--
info: 'TNLean.PEPS.regularGraphBlocking_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularGraphBlocking_dotProduct

/--
info: 'TNLean.PEPS.regularGraphNormalizedBell_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularGraphNormalizedBell_dotProduct

/--
info: 'TNLean.PEPS.regularGraphBlocking_averagingSite_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularGraphBlocking_averagingSite_normalized
