/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Correlations

/-!
# Traceless reduction of connected correlations

For a normalized right fixed point `ρ` of the transfer map, this file defines
the traceless matrix
`X * ρ - (Matrix.trace (X * ρ)) • ρ`
and rewrites the connected correlator as the trace pairing of `Y` with the
iterated transfer map applied to that matrix.

The identity is the algebraic reduction in
[Cirac et al., arXiv:2011.12127, Section II.B.3][Cirac2021Matrix].
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

private abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- The traceless part of `X` relative to a fixed point `ρ` with `tr ρ = 1`:
`Z = X * ρ − (tr(X * ρ)) • ρ`.  This satisfies `tr Z = 0`. -/
noncomputable def tracelessPart (ρ X : Mat D) : Mat D :=
  X * ρ - (Matrix.trace (X * ρ)) • ρ

/-- The traceless part indeed has trace zero. -/
theorem trace_tracelessPart (ρ X : Mat D) (hTr : Matrix.trace ρ = 1) :
    Matrix.trace (tracelessPart ρ X) = 0 := by
  dsimp [tracelessPart]
  simp [hTr]

/-- Reduction identity for the connected correlator.

Let `ρ` satisfy `E_A(ρ) = ρ` and set
`Z = X * ρ − (tr(X * ρ)) • ρ`.  When `tr(ρ) = 1`, the preceding lemma shows
that `Z` is traceless.
Then `C(X,Y;n) = tr(Y · E_A^n (Z))`.

Reference: arXiv:2011.12127, Sec. II.B.3. -/
theorem connectedCorrelator_eq_trace_transfer_tracelessPart
    (A : MPSTensor d D) (ρ X Y : Mat D) (n : ℕ)
    (hFix : transferMap (d := d) (D := D) A ρ = ρ) :
    connectedCorrelator (d := d) (D := D) A ρ X Y n =
      Matrix.trace (Y * (((transferMap (d := d) (D := D) A)) ^ n) (tracelessPart ρ X)) := by
  set E := transferMap (d := d) (D := D) A
  have hE_ρ_n : ∀ k : ℕ, (E ^ k) ρ = ρ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [pow_succ, hFix, ih]
  unfold connectedCorrelator twoPointExpectation onePointExpectation tracelessPart
  calc
    Matrix.trace (Y * ((E ^ n) (X * ρ))) -
        (Matrix.trace (X * ρ)) * Matrix.trace (Y * ρ) =
      Matrix.trace (Y * ((E ^ n) (X * ρ))) -
        Matrix.trace ((Matrix.trace (X * ρ)) • (Y * ρ)) := by
      simp [Matrix.trace_smul]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ)) - (Matrix.trace (X * ρ)) • (Y * ρ)) := by
      rw [Matrix.trace_sub]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ)) - Y * ((Matrix.trace (X * ρ)) • ρ)) := by
      simp
    _ = Matrix.trace (Y * (((E ^ n) (X * ρ)) - ((Matrix.trace (X * ρ)) • ρ))) := by
      rw [mul_sub]
    _ = Matrix.trace (Y * ((E ^ n) (X * ρ - (Matrix.trace (X * ρ)) • ρ))) := by
      simp [map_sub, map_smul, hE_ρ_n n]

end MPSTensor
