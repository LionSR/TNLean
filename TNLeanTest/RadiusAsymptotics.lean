/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Regression checks for the rounded squared-logarithmic radius

The tests cover zero constants, the two smallest system sizes, and domination
by a small positive real power. Guarded dependency reports check that the
asymptotic results use only Lean's standard axioms.
-/

open Filter TNLean.PEPS.AreaLaw.Scan

example (n : ℕ) : roundedLogRadius 0 n = 0 := by
  simp [roundedLogRadius]

example : roundedLogRadius 1 0 = 0 := by
  simp [roundedLogRadius]

example : roundedLogRadius 1 1 = 0 := by
  simp [roundedLogRadius]

example : ∀ᶠ n : ℕ in atTop, (roundedLogRadius 7 n : ℝ) ≤
    (n : ℝ) ^ ((1 : ℝ) / 1000) :=
  eventually_roundedLogRadius_le_rpow (by norm_num) (by norm_num)

example : ∀ᶠ n : ℕ in atTop, 4000 * (roundedLogRadius 7 n : ℝ) ≤
    (n : ℝ) ^ ((1 : ℝ) / 1000) :=
  eventually_const_mul_roundedLogRadius_le_rpow (by norm_num) (by norm_num) 4000

example : ∀ᶠ n : ℕ in atTop, (117 * Real.exp 1) * (roundedLogRadius 7 n : ℝ) ^ 3 ≤
    (n : ℝ) ^ ((1 : ℝ) / 1000) :=
  eventually_const_mul_roundedLogRadius_cube_le_rpow (by norm_num) (by norm_num)
    (117 * Real.exp 1)

example : ∀ᶠ n : ℕ in atTop, 1 ≤ roundedLogRadius 1 n :=
  eventually_one_le_roundedLogRadius (by norm_num)

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.isLittleO_roundedLogRadius_rpow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.isLittleO_roundedLogRadius_rpow

/--
info: 'TNLean.PEPS.AreaLaw.Scan.eventually_const_mul_roundedLogRadius_cube_le_rpow'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_const_mul_roundedLogRadius_cube_le_rpow

/--
info: 'TNLean.PEPS.AreaLaw.Scan.eventually_one_le_roundedLogRadius'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.eventually_one_le_roundedLogRadius

end AxiomChecks
