/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Channel.Semigroup.Basic

/-!
# Euler-resolvent limit (Wolf, Equation (7.9))

The Euler approximation of a dynamical semigroup by powers of the resolvent:
Wolf's lecture notes, Equation (7.9),
`T_t = lim_{n → ∞} ((n/t) R(n/t))ⁿ` with `R(z) = (z𝟙 - L)⁻¹` (Eq. (7.6)).
-/

open Matrix TNLean

noncomputable section

namespace TNLean.Channel.Semigroup

open scoped TNOperatorSpace

variable {D : ℕ}

/-- Euler resolvent step `(λ R(λ,L))`. -/
def eulerResolventStep (L : MatrixCLM (Fin D)) (lam : ℂ) : MatrixCLM (Fin D) :=
  lam • resolvent L lam

/-- Finite-`n` Euler approximation term `((n/t)R(n/t,L))^n`. -/
def eulerResolventApprox (L : MatrixCLM (Fin D)) (t : ℝ) (n : ℕ) : MatrixCLM (Fin D) :=
  (eulerResolventStep L ((n : ℂ) / (t : ℂ))) ^ n

/-- Axiomatized Euler limit statement (Wolf Equation (7.9)) in the present
finite-dimensional setting. -/
def HasEulerResolventLimit (L : MatrixCLM (Fin D)) (t : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => eulerResolventApprox L t n) Filter.atTop
    (nhds (expSemigroupCLM L t))

end TNLean.Channel.Semigroup
