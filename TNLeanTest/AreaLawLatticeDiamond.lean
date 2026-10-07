/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphLatticeDiamond

/-!
# Consumer regressions for the exact lattice diamond

Kernel computation checks the finite sets independently of the general cardinality theorem.
The examples include radius zero, the five-site unit diamond, a translated radius-two diamond,
and the exclusion of containing-square corners. Graph consumers check an empty finite set,
a singleton graph, and exclusion of sites in another connected component.
-/

open TNLean.PEPS.AreaLaw

namespace TNLeanTest

-- Radius zero retains the center and no other lattice site.
example : latticeDiamond (0, 0) 0 = {(0, 0)} := by decide

-- The unit diamond contains five sites, rather than the surrounding square's nine.
example : latticeDiamond (0, 0) 1 = {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} := by
  decide

-- These computations use the finite-set definition, not the cardinality formula.
example : (latticeDiamond (0, 0) 2).card = 13 := by decide
example : (latticeDiamond (4, -3) 2).card = 13 := by decide
example : ((1, 1) : ℤ × ℤ) ∉ latticeDiamond (0, 0) 1 := by decide
example : ((2, 0) : ℤ × ℤ) ∈ latticeDiamond (0, 0) 2 := by decide
example : ((-1, -1) : ℤ × ℤ) ∈ latticeDiamond (0, 0) 2 := by decide

-- Arbitrary centers use the same exact count.
example (a : ℤ × ℤ) : (latticeDiamond a 0).card = 1 := by simp
example (a : ℤ × ℤ) : (latticeDiamond a 3).card = 25 := by simp

-- The ambient result needs no graph structure or finite ambient type.
example (a : ℤ × ℤ) (R : ℕ) :
    (∅ : Finset (ℤ × ℤ)).card ≤ 1 + 2 * R * (R + 1) :=
  card_le_diamond_of_latticeL1Distance_le id ∅ Function.injective_id a R (by simp)

-- A radius-zero ball in a singleton graph has one site.
example : (Finset.univ : Finset PUnit).card ≤ 1 := by
  exact le_trans (card_le_diamond_of_edist_le (G := (⊥ : SimpleGraph PUnit))
    (fun _ : PUnit ↦ ((0, 0) : ℤ × ℤ)) Finset.univ
    (fun _ _ _ ↦ Subsingleton.elim _ _) (by intro x y h; simp at h)
    PUnit.unit 0 (by intro x hx; cases x; simp)) (by simp)

-- Distinct components cannot satisfy a finite-distance hypothesis used by the count.
example {V : Type*} {a b : V} (hab : a ≠ b) (R : ℕ) :
    ¬ (⊥ : SimpleGraph V).edist a b ≤ (R : ℕ∞) := by
  have hd : (⊥ : SimpleGraph V).edist a b = ⊤ :=
    SimpleGraph.edist_eq_top_of_not_reachable
      (fun h ↦ hab (SimpleGraph.reachable_bot.mp h))
  simp [hd]

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.mem_latticeDiamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.AreaLaw.mem_latticeDiamond

/-- info: 'TNLean.PEPS.AreaLaw.card_latticeDiamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.AreaLaw.card_latticeDiamond

/-- info: 'TNLean.PEPS.AreaLaw.card_le_diamond_of_latticeL1Distance_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.AreaLaw.card_le_diamond_of_latticeL1Distance_le

/-- info: 'TNLean.PEPS.AreaLaw.card_le_diamond_of_walks' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.AreaLaw.card_le_diamond_of_walks

/-- info: 'TNLean.PEPS.AreaLaw.card_le_diamond_of_edist_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.AreaLaw.card_le_diamond_of_edist_le

end TNLeanTest
