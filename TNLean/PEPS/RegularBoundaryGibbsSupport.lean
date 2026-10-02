/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryState
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Gibbs operators and the invariant regular boundary support

For a nontrivial finite group, the regular boundary density is singular on
the full virtual space. It therefore cannot be a matrix exponential there.
On its invariant support it is a positive scalar multiple of the identity,
and is the Gibbs operator of a constant Hamiltonian.

The density is the regular virtual boundary state of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Theorem 6.9, lines 2027–2076. These finite
dimensional statements clarify the support needed when considering the
Gibbs representation in the bulk–boundary conjecture of
arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`, local source lines
980–1024. They do not establish locality of a boundary Hamiltonian or a
uniform bulk spectral gap.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The regular boundary density has a proper support for a nontrivial group.
Source: SCP10, Theorem 6.9, lines 2027–2076. -/
theorem rank_regularBoundaryDensity_lt_card (n : ℕ) (hG : 1 < Fintype.card G) :
    (regularBoundaryDensity (G := G) n).rank < Fintype.card (Fin (n + 1) → G) := by
  rw [rank_regularBoundaryDensity, Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_lt_pow_right hG (Nat.lt_succ_self n)

/-- The regular virtual boundary density is not invertible on the full
boundary space for a nontrivial group. Source: SCP10, Theorem 6.9,
lines 2027–2076. -/
theorem not_isUnit_regularBoundaryDensity (n : ℕ) (hG : 1 < Fintype.card G) :
    ¬ IsUnit (regularBoundaryDensity (G := G) n) := by
  intro h
  exact (rank_regularBoundaryDensity_lt_card n hG).ne
    (Matrix.rank_of_isUnit _ h)

/-- No finite matrix Hamiltonian has the full-space regular boundary density
as its exponential when the group is nontrivial. This is a support
obstruction, rather than a spectral-gap assertion, relevant to the Gibbs
representation in arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem regularBoundaryDensity_ne_exp (n : ℕ) (hG : 1 < Fintype.card G)
    (H : Matrix (Fin (n + 1) → G) (Fin (n + 1) → G) ℂ) :
    regularBoundaryDensity (G := G) n ≠ NormedSpace.exp H := by
  intro h
  apply not_isUnit_regularBoundaryDensity n hG
  rw [h]
  exact Matrix.isUnit_exp H

/-- The density in the relative-coordinate basis of its invariant support.
Source: SCP10, Theorem 6.9, lines 2027–2076. -/
noncomputable def regularBoundarySupportedDensity (n : ℕ) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  ((Fintype.card G : ℂ) ^ n)⁻¹ • 1

/-- A constant Hamiltonian on the invariant support, with inverse
temperature absorbed into its definition. Source: the flat support density
in SCP10, Theorem 6.9, lines 2027–2076. -/
noncomputable def regularBoundarySupportedHamiltonian (n : ℕ) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  (Real.log (Fintype.card G ^ n : ℝ) : ℂ) • 1

/-- Relative coordinates identify the action of the full density on an
invariant vector with its supported density. Source: SCP10, Theorem 6.9,
lines 2027–2076. -/
theorem regularBoundarySupportedDensity_mulVec (n : ℕ)
    (x : (regularBoundaryRepresentation (G := G) (n + 1)).invariants) :
    regularBoundarySupportedDensity n *ᵥ regularBoundaryInvariantsEquiv n x =
      regularBoundaryInvariantsEquiv n
        ⟨regularBoundaryDensity n *ᵥ x.1, by
          rw [regularBoundaryDensity_mulVec_of_mem_invariants n x.1 x.2]
          exact Submodule.smul_mem _ _ x.2⟩ := by
  rw [regularBoundarySupportedDensity, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hx := regularBoundaryDensity_mulVec_of_mem_invariants n x.1 x.2
  apply congrArg (regularBoundaryInvariantsEquiv n)
    (show ((Fintype.card G : ℂ) ^ n)⁻¹ • x =
        ⟨regularBoundaryDensity n *ᵥ x.1, _⟩ from Subtype.ext hx.symm)

/-- On its invariant support the flat regular boundary density is a Gibbs
operator of a constant Hamiltonian. This makes no locality assertion for
the original virtual legs. Source: SCP10, Theorem 6.9, lines 2027–2076;
compare arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem regularBoundarySupportedDensity_eq_exp (n : ℕ) :
    regularBoundarySupportedDensity (G := G) n =
      NormedSpace.exp (-regularBoundarySupportedHamiltonian (G := G) n) := by
  have hpos : 0 < (Fintype.card G ^ n : ℝ) :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) n
  rw [regularBoundarySupportedHamiltonian, regularBoundarySupportedDensity]
  rw [show -((Real.log (Fintype.card G ^ n : ℝ) : ℂ) •
      (1 : Matrix (Fin n → G) (Fin n → G) ℂ)) =
      Matrix.diagonal (fun _ => -(Real.log (Fintype.card G ^ n : ℝ) : ℂ)) by
        ext i j
        simp [Matrix.diagonal_apply, Matrix.one_apply]]
  rw [Matrix.exp_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, Complex.exp_neg,
    ← Complex.ofReal_exp, Real.exp_log hpos]

end TNLean.PEPS
