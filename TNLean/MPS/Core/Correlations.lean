/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.TraceExpansion
import TNLean.QPF.Assembly

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Correlations for normal MPS in the thermodynamic limit

This file defines connected correlations for an MPS tensor in the
thermodynamic limit.  One-point and two-point observables are expressed
through the transfer map, and the connected two-point function is obtained
by subtracting the product of one-point expectations.

The spectral statements `connectedCorrelator_eq_sum` and
`connectedCorrelator_bound` take the spectral decomposition or bound
as an explicit hypothesis; the source (arXiv:2011.12127, Sec. 4.5)
derives these hypotheses from the transfer-map eigendecomposition.
The definitions here are used by the zero-correlation-length results.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

private abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- One-site expectation value in terms of a chosen right fixed point `ρR`.

In the thermodynamic limit for a normal MPS, one takes `ρR` to be the positive
right fixed point of the transfer map. -/
noncomputable def onePointExpectation
    (ρR X : Mat D) : ℂ :=
  Matrix.trace (X * ρR)

/-- Two-point function at distance `n`, written by sandwiching `E^n` between
single-site insertions and evaluating against `ρR`. -/
noncomputable def twoPointExpectation (A : MPSTensor d D)
    (ρR X Y : Mat D) (n : ℕ) : ℂ :=
  Matrix.trace (Y * ((transferMap (d := d) (D := D) A) ^ n) (X * ρR))

/-- Connected correlator `C(X,Y;n) = ⟨X₀Yₙ⟩ - ⟨X₀⟩⟨Y₀⟩`. -/
noncomputable def connectedCorrelator (A : MPSTensor d D)
    (ρR X Y : Mat D) (n : ℕ) : ℂ :=
  twoPointExpectation (d := d) (D := D) A ρR X Y n -
    onePointExpectation (D := D) ρR X *
      onePointExpectation (D := D) ρR Y

@[simp] theorem connectedCorrelator_def (A : MPSTensor d D)
    (ρR X Y : Mat D) (n : ℕ) :
    connectedCorrelator (d := d) (D := D) A ρR X Y n =
      twoPointExpectation (d := d) (D := D) A ρR X Y n -
        onePointExpectation (D := D) ρR X *
          onePointExpectation (D := D) ρR Y := rfl

/-- Transfer-map expression for the two-point function. -/
@[simp] theorem twoPointExpectation_transfer (A : MPSTensor d D)
    (ρR X Y : Mat D) (n : ℕ) :
    twoPointExpectation (d := d) (D := D) A ρR X Y n =
      Matrix.trace (Y * ((transferMap (d := d) (D := D) A) ^ n) (X * ρR)) := rfl

/--
Spectral expansion of connected correlators (conditional on supplied
coefficients and eigenvalues).

If coefficients `cⱼ` and eigenvalues `λⱼ` satisfying the spectral expansion
identity are supplied, then the connected correlator equals the sum of
exponentials `∑ⱼ cⱼ λⱼⁿ`.

The source (arXiv:2011.12127, Sec. 4.5) asserts that such `cⱼ, λⱼ`
always exist for a normal MPS via the transfer-map eigendecomposition.
-/
theorem connectedCorrelator_eq_sum
    (A : MPSTensor d D)
    (ρR X Y : Mat D)
    (c lam : Fin (D * D - 1) → ℂ)
    (hdecomp : ∀ n : ℕ,
      connectedCorrelator (d := d) (D := D) A ρR X Y n =
        ∑ j : Fin (D * D - 1), c j * (lam j) ^ n) :
    ∀ n : ℕ,
      connectedCorrelator (d := d) (D := D) A ρR X Y n =
        ∑ j : Fin (D * D - 1), c j * (lam j) ^ n :=
  hdecomp

/--
Exponential decay bound for connected correlations (conditional on
supplied constant and subleading eigenvalue).

If a constant `C_X_Y` and a subleading eigenvalue `λ₂` with the
exponential-decay bound are supplied, then the connected correlator
satisfies `|C(X,Y;n)| ≤ C_X_Y · |λ₂|ⁿ`.

The source (arXiv:2011.12127, Sec. 4.5) derives this from the
sum-of-exponentials expansion and the spectral gap condition.
-/
theorem connectedCorrelator_bound
    (A : MPSTensor d D)
    (ρR X Y : Mat D) (CXY : ℝ) (lam₂ : ℂ)
    (hbound : ∀ n : ℕ,
      ‖connectedCorrelator (d := d) (D := D) A ρR X Y n‖ ≤ CXY * ‖lam₂‖ ^ n) :
    ∀ n : ℕ,
      ‖connectedCorrelator (d := d) (D := D) A ρR X Y n‖ ≤ CXY * ‖lam₂‖ ^ n :=
  hbound

/-- Correlation length associated with a chosen subleading eigenvalue `λ₂`. -/
noncomputable def correlationLength (lam₂ : ℂ) : ℝ :=
  -1 / Real.log ‖lam₂‖

/-- The correlation length is positive when `0 < ‖λ₂‖ < 1`. -/
theorem correlationLength_pos {lam₂ : ℂ} (h0 : 0 < ‖lam₂‖) (h1 : ‖lam₂‖ < 1) :
    0 < correlationLength lam₂ := by
  unfold correlationLength
  rw [neg_div, neg_pos]
  exact div_neg_of_pos_of_neg one_pos (Real.log_neg h0 h1)

end MPSTensor
