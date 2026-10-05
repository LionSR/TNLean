/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBondClosureSeamMovement

/-! # Dimension-independent closure seam movement regressions -/

open TNLean.PEPS
open scoped BigOperators

-- The movement is a group-valued statement, without finiteness or linear data.
example {G : Type*} [Group G] {w h : ℕ} [NeZero w] [NeZero h]
    (g k : G) (hgk : Commute g k) (c : ZMod w) (r : ZMod h) :
    torusBondGauge (torusBondClosureSeamGauge g k c r) (torusBondClosureLabels g k) =
      torusBondClosureLabelsAt g k c r :=
  torusBondGauge_closureSeamGauge g k hgk c r

-- Averaging works for every function into an additive commutative monoid,
-- including dependent-bond contractions with unrelated virtual dimensions.
example {G A : Type*} [Group G] [Fintype G] [AddCommMonoid A]
    (f : TorusBondLabels 2 2 G → A) (g h : G) (hgh : Commute g h) (c r : ZMod 2) :
    (∑ q, f (torusBondGauge q (torusBondClosureLabelsAt g h c r))) =
      ∑ q, f (torusBondGauge q (torusBondClosureLabels g h)) :=
  sum_torusBondGauge_closureAt f g h hgh c r

-- Unequal positive periods need no further geometric lower bound.
example {G : Type*} [Group G] (g h : G) (hgh : Commute g h) :
    ∃ q : TorusVertex 2 3 → G,
      torusBondGauge q (torusBondClosureLabels g h) = torusBondClosureLabelsAt g h 1 2 :=
  exists_torusBondGauge_eq_closureAt g h hgh 1 2

-- Period-one self bonds are retained, and the only seam gauge is the identity.
example {G : Type*} [Group G] (g h : G) (v : TorusVertex 1 1) :
    torusBondClosureSeamGauge g h 0 0 v = 1 := by
  simp [torusBondClosureSeamGauge, torusSeamGauge]

example {G : Type*} [Group G] (g h : G) (hgh : Commute g h) :
    torusBondGauge (torusBondClosureSeamGauge g h (0 : ZMod 1) (0 : ZMod 1))
        (torusBondClosureLabels g h) = torusBondClosureLabelsAt g h 0 0 :=
  torusBondGauge_closureSeamGauge g h hgh 0 0

-- Moving both seams on the two-by-two torus changes the actual initial vertices.
example {G : Type*} [Group G] (g h : G) :
    (torusBondClosureLabelsAt (width := 2) (height := 2) g h 1 1).1 (0, 1) = h ∧
    (torusBondClosureLabelsAt (width := 2) (height := 2) g h 1 1).1 (1, 1) = 1 ∧
    (torusBondClosureLabelsAt (width := 2) (height := 2) g h 1 1).2 (1, 0) = g ∧
    (torusBondClosureLabelsAt (width := 2) (height := 2) g h 1 1).2 (1, 1) = 1 := by
  simp [torusBondClosureLabelsAt]

-- The ambient group need not be abelian; commuting nonidentity permutation
-- seams move by the same explicit gauge.
example (k : Equiv.Perm (Fin 3)) :
    torusBondGauge (torusBondClosureSeamGauge k k (1 : ZMod 2) (1 : ZMod 2))
        (torusBondClosureLabels k k) = torusBondClosureLabelsAt k k 1 1 :=
  torusBondGauge_closureSeamGauge k k (Commute.refl k) 1 1

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.torusBondGauge_closureSeamGauge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondGauge_closureSeamGauge

/--
info: 'TNLean.PEPS.sum_torusBondGauge_closureAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.sum_torusBondGauge_closureAt
