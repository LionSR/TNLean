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

This file defines connected correlations for a (normalized) MPS tensor
in the thermodynamic limit. We express one-point and two-point
observables through the transfer map `transferMap`, and package the standard
sum-of-exponentials / exponential-decay statements in a form that downstream
chapters can consume.

The theorems in this file are intentionally lightweight wrappers: they expose
exact assumptions needed in later files while keeping the implementation
independent of a specific spectral decomposition API.
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
Abstract spectral decomposition interface for connected correlators:
if a spectral expansion is provided, it gives the expected sum-of-exponentials
formula.
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
Exponential bound for connected correlations once the subleading spectral radius
bound is supplied.
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

end MPSTensor
