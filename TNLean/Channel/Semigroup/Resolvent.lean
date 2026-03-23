/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Normed.Ring.Units

open Matrix

noncomputable section

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

namespace TNLean.Channel.Semigroup

variable {D : ℕ}

private abbrev CLM (D : ℕ) :=
  Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ

/-- Resolvent of a semigroup generator (`R(z,L) = (z • 1 - L)⁻¹`). -/
abbrev generatorResolventCLM (L : CLM D) (z : ℂ) : CLM D :=
  resolvent L z

@[simp] theorem generatorResolventCLM_eq_mathlib (L : CLM D) (z : ℂ) :
    generatorResolventCLM L z = resolvent L z := rfl

/-- Neumann-series specialization at `z = 1`:
if `‖L‖ < 1`, then `R(1,L) = ∑ₙ L^n`. -/
theorem generatorResolventCLM_one_neumann
    (L : CLM D) (hL : ‖L‖ < 1) :
    generatorResolventCLM L (1 : ℂ) = ∑' n : ℕ, L ^ n := by
  simpa [generatorResolventCLM, resolvent, Algebra.algebraMap_eq_smul_one, one_smul] using
    (NormedRing.inverse_one_sub L hL)

/-- Euler resolvent step `(λ R(λ,L))`. -/
def eulerResolventStep (L : CLM D) (lam : ℂ) : CLM D :=
  lam • generatorResolventCLM L lam

/-- Finite-`n` Euler approximation term `((n/t)R(n/t,L))^n`. -/
def eulerResolventApprox (L : CLM D) (t : ℝ) (n : ℕ) : CLM D :=
  (eulerResolventStep L ((n : ℂ) / (t : ℂ))) ^ n

/-- Axiomatized Euler limit statement (Wolf Eq. (7.9)) in the present finite-dimensional setting. -/
def HasEulerResolventLimit (L : CLM D) (t : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => eulerResolventApprox L t n) Filter.atTop
    (nhds (expSemigroupCLM L t))

end TNLean.Channel.Semigroup
