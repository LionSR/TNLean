/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsingCrossingCoefficients

/-!
# Signature and axiom checks for Ising crossing structure coefficients

The tests check the base fusion table, the defining double sum, all three
`σ, σ` output formulas, and associativity for arbitrary complex weights and
natural lengths. Length zero is tested explicitly. Guarded axiom reports
exclude nonstandard axioms from the public theorems.
-/

open TNLean.Algebra.IsingCrossing
open TNLean.Algebra.IsingCrossing.Label
open scoped BigOperators

example (a c : Label) : fusionMultiplicity one a c = if a = c then 1 else 0 := rfl

example (a c : Label) : fusionMultiplicity a one c = if a = c then 1 else 0 := by
  cases a <;> cases c <;> decide

example :
    (fusionMultiplicity psi psi one, fusionMultiplicity psi psi psi,
      fusionMultiplicity psi psi sigma) = (1, 0, 0) := rfl

example :
    (fusionMultiplicity psi sigma one, fusionMultiplicity psi sigma psi,
      fusionMultiplicity psi sigma sigma) = (0, 0, 1) := rfl

example :
    (fusionMultiplicity sigma psi one, fusionMultiplicity sigma psi psi,
      fusionMultiplicity sigma psi sigma) = (0, 0, 1) := rfl

example :
    (fusionMultiplicity sigma sigma one, fusionMultiplicity sigma sigma psi,
      fusionMultiplicity sigma sigma sigma) = (1, 1, 0) := rfl

example (w : Label → ℂ) (L : ℕ) (a b c : Label) :
    coefficient w L a b c =
      ∑ r, ∑ t, w r ^ L * (fusionMultiplicity a r t : ℂ) *
        (fusionMultiplicity t b c : ℂ) := rfl

example (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma one = w one ^ L + w psi ^ L :=
  coefficient_sigma_sigma_one w L

example (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma psi = w one ^ L + w psi ^ L :=
  coefficient_sigma_sigma_psi w L

example (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma sigma = 2 * w sigma ^ L :=
  coefficient_sigma_sigma_sigma w L

example : fusionMultiplicity sigma sigma sigma = 0 :=
  fusionMultiplicity_sigma_sigma_sigma

example (w : Label → ℂ) (L : ℕ) (a b c d : Label) :
    (∑ e, coefficient w L a b e * coefficient w L e c d) =
      ∑ f, coefficient w L b c f * coefficient w L a f d :=
  coefficient_assoc w L a b c d

example (w : Label → ℂ) : coefficient w 0 sigma sigma sigma = 2 := by
  simp [coefficient_sigma_sigma_sigma]

example (a b c d : Label) :
    (∑ e, coefficient (fun _ => 0) 0 a b e * coefficient (fun _ => 0) 0 e c d) =
      ∑ f, coefficient (fun _ => 0) 0 b c f * coefficient (fun _ => 0) 0 a f d :=
  coefficient_assoc (fun _ => 0) 0 a b c d

example : coefficient (fun _ => 1) 1 sigma sigma sigma ≠
    (fusionMultiplicity sigma sigma sigma : ℂ) := by
  simp [coefficient_sigma_sigma_sigma, fusionMultiplicity_sigma_sigma_sigma]

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_one

/-- info: 'TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_psi

/-- info: 'TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.Algebra.IsingCrossing.coefficient_sigma_sigma_sigma

/-- info: 'TNLean.Algebra.IsingCrossing.fusionMultiplicity_sigma_sigma_sigma' does not depend on any axioms -/
#guard_msgs in
#print axioms TNLean.Algebra.IsingCrossing.fusionMultiplicity_sigma_sigma_sigma

/-- info: 'TNLean.Algebra.IsingCrossing.coefficient_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.Algebra.IsingCrossing.coefficient_assoc

end AxiomChecks
