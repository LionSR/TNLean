/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.MatrixOperatorSpace
import TNLean.Channel.Semigroup.Basic

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Ring.Units

open Matrix TNLean

noncomputable section

namespace TNLean.Channel.Semigroup

open scoped TNOperatorSpace

variable {D : ℕ}

/-- Neumann-series specialization at `z = 1`:
if `‖L‖ < 1`, then `R(1,L) = ∑ₙ L^n`. -/
theorem resolvent_one_neumann
    (L : MatrixCLM (Fin D)) (hL : ‖L‖ < 1) :
    resolvent L (1 : ℂ) = ∑' n : ℕ, L ^ n := by
  simpa [resolvent, Algebra.algebraMap_eq_smul_one, one_smul] using
    (NormedRing.inverse_one_sub L hL)

/-- Euler resolvent step `(λ R(λ,L))`. -/
def eulerResolventStep (L : MatrixCLM (Fin D)) (lam : ℂ) : MatrixCLM (Fin D) :=
  lam • resolvent L lam

/-- Finite-`n` Euler approximation term `((n/t)R(n/t,L))^n`. -/
def eulerResolventApprox (L : MatrixCLM (Fin D)) (t : ℝ) (n : ℕ) : MatrixCLM (Fin D) :=
  (eulerResolventStep L ((n : ℂ) / (t : ℂ))) ^ n

/-- Axiomatized Euler limit statement (Wolf Equation (7.9)) in the present finite-dimensional setting. -/
def HasEulerResolventLimit (L : MatrixCLM (Fin D)) (t : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => eulerResolventApprox L t n) Filter.atTop
    (nhds (expSemigroupCLM L t))

end TNLean.Channel.Semigroup
