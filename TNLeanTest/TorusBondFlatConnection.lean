/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusBondFlatConnection

/-!
# Labelled two-by-two torus flat-connection tests

The classifier is instantiated at period two for arbitrary, potentially
noncommutative groups. Its rooted gauge and two holonomies are checked against
the explicit four-vertex formulas. A noncommuting pair of permutations fails the
closure flatness condition, so the commutation constraint is not vacuous.
-/

open TNLean.PEPS

section Group

variable {G : Type*} [Group G]

example (p : TorusBondLabels 2 2 G) (hp : IsTorusBondFlat p) :
    ∃ (q : TorusVertex 2 2 → G) (g h : G),
      Commute g h ∧ torusBondGauge q p = torusBondClosureLabels g h :=
  exists_torusBondGauge_eq_closure p hp

example (p : TorusBondLabels 2 2 G) :
    torusBondTreeGauge p (0, 0) = 1 := by
  simp [torusBondTreeGauge, torusTreeGauge]

example (p : TorusBondLabels 2 2 G) :
    torusBondTreeGauge p (1, 0) = (p.1 (0, 0))⁻¹ := by
  simp [torusBondTreeGauge, torusTreeGauge,
    show (1 : ZMod 2).val = 1 from by decide, zmodTransport_succ]

example (p : TorusBondLabels 2 2 G) :
    torusBondTreeGauge p (0, 1) = p.2 (0, 0) := by
  simp [torusBondTreeGauge, torusTreeGauge,
    show (1 : ZMod 2).val = 1 from by decide, zmodTransport_succ]

example (p : TorusBondLabels 2 2 G) :
    torusBondTreeGauge p (1, 1) = (p.1 (0, 0))⁻¹ * p.2 (1, 0) := by
  simp [torusBondTreeGauge, torusTreeGauge,
    show (1 : ZMod 2).val = 1 from by decide, zmodTransport_succ]

example (p : TorusBondLabels 2 2 G) (hp : IsTorusBondFlat p) :
    torusBondGauge (torusBondTreeGauge p) p =
      torusBondClosureLabels (p.2 (0, 0) * p.2 (0, 1)) (p.1 (1, 0) * p.1 (0, 0)) := by
  simpa [zmodTransport_succ] using hp.torusBondGauge_tree

example (p : TorusBondLabels 2 2 G) (hp : IsTorusBondFlat p) :
    Commute (p.2 (0, 0) * p.2 (0, 1)) (p.1 (1, 0) * p.1 (0, 0)) := by
  have h := ((isTorusBondFlat_iff_isTorusFlat p).mp hp).commute_holonomies.symm.inv_left
  simpa [zmodTransport_succ] using h

example (q : TorusVertex 2 2 → G) :
    IsTorusBondFlat (torusBondRelativeLabels q) := isTorusBondFlat_relativeLabels q

-- The two parallel horizontal bonds need not have equal labels.
example (g h : G) :
    (torusBondClosureLabels (width := 2) (height := 2) g h).1 (0, 0) = 1 ∧
      (torusBondClosureLabels (width := 2) (height := 2) g h).1 (1, 0) = h := by
  simp [torusBondClosureLabels, show (1 : ZMod 2) + 1 = 0 from by decide]

-- The degenerate positive period one also requires no simple-graph hypothesis.
example (p : TorusBondLabels 1 1 G) (hp : IsTorusBondFlat p) :
    ∃ (q : TorusVertex 1 1 → G) (g h : G),
      Commute g h ∧ torusBondGauge q p = torusBondClosureLabels g h :=
  exists_torusBondGauge_eq_closure p hp

end Group

example : ¬IsTorusBondFlat
    (torusBondClosureLabels (width := 2) (height := 2)
      (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2)) := by
  rw [isTorusBondFlat_closure_iff]
  unfold Commute SemiconjBy
  decide

example : IsTorusBondFlat
    (torusBondClosureLabels (width := 2) (height := 2)
      (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (0 : Fin 3) 1)) := by
  rw [isTorusBondFlat_closure_iff]
  exact Commute.refl _
