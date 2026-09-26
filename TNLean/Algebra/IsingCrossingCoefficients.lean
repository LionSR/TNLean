/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

/-!
# Structure coefficients from the Ising fusion rules

For the Ising labels `1`, `ψ`, `σ`, let `N a b c` be the natural-number
multiplicity of `c` in `a × b`. For arbitrary complex weights `w` and every
natural length `L`, define the structure coefficients
`c_{a,b,c}^{(L)} = ∑ r, ∑ t, w r ^ L * N a r t * N t b c`.

These are the coefficients of `e_a W_L e_b`, where `W_L = ∑ r, w r ^ L e_r`.
The formulas and associativity below formalize the coefficient calculation in
`Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/rfp_symmetry_bridge.tex`,
“Renormalization fixed points and structure coefficients”, and its companion
`ising_comparison.tex`. They do not assert an RFP realization, comparison
matrices, or a classification of their solutions.
-/

namespace TNLean.Algebra.IsingCrossing

/-- The three Ising labels, with `one` denoting the unit label. -/
inductive Label
  | one
  | psi
  | sigma
  deriving DecidableEq

instance : Fintype Label where
  elems := {Label.one, Label.psi, Label.sigma}
  complete a := by cases a <;> simp

open Label
open scoped BigOperators

/-- The Ising fusion table: `1 a = a 1 = a`, `ψ² = 1`, `ψσ = σψ = σ`,
and `σ² = 1 + ψ`. -/
def fusionMultiplicity : Label → Label → Label → ℕ
  | one, b, c => if b = c then 1 else 0
  | psi, one, c => if c = psi then 1 else 0
  | psi, psi, c => if c = one then 1 else 0
  | psi, sigma, c => if c = sigma then 1 else 0
  | sigma, one, c => if c = sigma then 1 else 0
  | sigma, psi, c => if c = sigma then 1 else 0
  | sigma, sigma, c => if c = sigma then 0 else 1

private theorem sum_labels (f : Label → ℂ) :
    ∑ a, f a = f one + f psi + f sigma := by
  change (∑ a ∈ ({one, psi, sigma} : Finset Label), f a) = _
  simp [add_assoc]

/-- The crossing structure coefficients, with no positivity or nonzero assumption
on the weights. The definition also includes length zero. -/
noncomputable def coefficient (w : Label → ℂ) (L : ℕ) (a b c : Label) : ℂ :=
  ∑ r, ∑ t, w r ^ L * (fusionMultiplicity a r t : ℂ) *
    (fusionMultiplicity t b c : ℂ)

/-- The unit output of the `σ, σ` crossing. -/
theorem coefficient_sigma_sigma_one (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma one = w one ^ L + w psi ^ L := by
  simp [coefficient, sum_labels, fusionMultiplicity]

/-- The `ψ` output of the `σ, σ` crossing. -/
theorem coefficient_sigma_sigma_psi (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma psi = w one ^ L + w psi ^ L := by
  simp [coefficient, sum_labels, fusionMultiplicity]

/-- The `σ` output has two contributions from the inserted label `σ`. -/
theorem coefficient_sigma_sigma_sigma (w : Label → ℂ) (L : ℕ) :
    coefficient w L sigma sigma sigma = 2 * w sigma ^ L := by
  simp [coefficient, sum_labels, fusionMultiplicity, two_mul]

/-- The base fusion table has no `σ` output in `σ × σ`. -/
theorem fusionMultiplicity_sigma_sigma_sigma :
    fusionMultiplicity sigma sigma sigma = 0 := rfl

set_option maxHeartbeats 800000 in
-- Expanding the double sums in all 81 label cases exceeds the default limit.
/-- The structure coefficients are associative for every natural length,
including zero. No restriction on the complex weights is needed. -/
theorem coefficient_assoc (w : Label → ℂ) (L : ℕ) (a b c d : Label) :
    (∑ e, coefficient w L a b e * coefficient w L e c d) =
      ∑ f, coefficient w L b c f * coefficient w L a f d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [coefficient, sum_labels, fusionMultiplicity] <;> ring

end TNLean.Algebra.IsingCrossing
