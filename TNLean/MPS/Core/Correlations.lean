/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Transfer
import TNLean.Spectral.TransferOperatorGapInjective
import QICLean.QPF.Assembly

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Correlations for normal MPS in the thermodynamic limit

This file defines connected correlations for an MPS tensor in the
thermodynamic limit.  One-point and two-point observables are expressed
through the transfer map, and the connected two-point function is obtained
by subtracting the product of one-point expectations.

The spectral expansion and decay results remain separate proof obligations
tracked in issue #1447. The source (arXiv:2011.12127 [CPGSV21]) discusses
connected correlations in Section II.B.3. A pure exponential expansion
requires diagonalizability; in general Jordan blocks contribute polynomial
factors, and a geometric bound uses a rate above the complementary spectral
radius.
The definitions here are used by the zero-correlation-length results.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- One-site expectation value in terms of a chosen right fixed point `ρR`.

In the thermodynamic limit for a normal MPS, one takes `ρR` to be the positive
right fixed point of the transfer map.  Cf. CPGSV21, Sec. 2.3:
`⟨X⟩ := tr(Xρ^R)`. -/
noncomputable def onePointExpectation
    (ρR X : Mat D) : ℂ :=
  Matrix.trace (X * ρR)

/-- Two-point function at distance `n`, written by sandwiching `E^n` between
single-site insertions and evaluating against `ρR`.

Cf. CPGSV21, Sec. 2.3: `⟨X₀ Yₙ⟩ := tr(Y E_A^n (X ρ^R))`. -/
noncomputable def twoPointExpectation (A : MPSTensor d D)
    (ρR X Y : Mat D) (n : ℕ) : ℂ :=
  Matrix.trace (Y * ((Kraus.transferMap (d := d) (D := D) A) ^ n) (X * ρR))

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
      Matrix.trace (Y * ((Kraus.transferMap (d := d) (D := D) A) ^ n) (X * ρR)) := rfl

/-- Correlation length associated with a chosen subleading eigenvalue `λ₂`.

Formula from CPGSV21, Sec. 2.3: `ξ := −1/log|λ₂|`. -/
noncomputable def correlationLength (lam₂ : ℂ) : ℝ :=
  -1 / Real.log ‖lam₂‖

/-- The correlation length is positive when `0 < ‖λ₂‖ < 1`. -/
theorem correlationLength_pos {lam₂ : ℂ} (h0 : 0 < ‖lam₂‖) (h1 : ‖lam₂‖ < 1) :
    0 < correlationLength lam₂ := by
  unfold correlationLength
  rw [neg_div, neg_pos]
  exact div_neg_of_pos_of_neg one_pos (Real.log_neg h0 h1)

/-- A positive correlation length forces `0 < ‖λ₂‖ < 1`; converse of `correlationLength_pos`. -/
theorem norm_pos_and_lt_one_of_correlationLength_pos {lam₂ : ℂ}
    (hξ : 0 < correlationLength lam₂) : 0 < ‖lam₂‖ ∧ ‖lam₂‖ < 1 := by
  have hlog : Real.log ‖lam₂‖ < 0 := by
    by_contra h
    push Not at h
    have : correlationLength lam₂ ≤ 0 := by
      unfold correlationLength
      exact div_nonpos_iff.mpr (Or.inr ⟨by norm_num, h⟩)
    linarith
  have hpos : 0 < ‖lam₂‖ := by
    rcases (norm_nonneg lam₂).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hlog
      exact absurd hlog (lt_irrefl 0)
  exact ⟨hpos, (Real.log_neg_iff hpos).mp hlog⟩

end MPSTensor
