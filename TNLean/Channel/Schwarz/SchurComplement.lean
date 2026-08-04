/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.Douglas
import TNLean.Analysis.MatrixSqrt
import Mathlib.Data.Matrix.Block

/-!
# Block Schur complements (Wolf §5.1, Theorem 5.2)

For a self-adjoint 2×2 block matrix `M = [[P, Q], [Q†, R]]`
with `P, R` PSD, the following are equivalent:

1. `M` is PSD
2. `ker(R) ⊆ ker(Q)` and the pseudoinverse Schur complement `P − Q·R⁺·Q†` is PSD
3. `ker(R) ⊆ ker(Q)` and `‖P^{-1/2}·Q·R^{-1/2}‖ ≤ 1` (contraction form)

## References

* [M. Wolf, *Quantum Channels & Operations*, Theorem 5.2][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace SchurComplement

variable {D₁ D₂ : ℕ}

/-- A 2×2 block matrix: [[P, Q], [Q†, R]]. -/
def blockMatrix (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) : Matrix ((Fin D₁) ⊕ (Fin D₂)) ((Fin D₁) ⊕ (Fin D₂)) ℂ :=
  Matrix.fromBlocks P Q (Qᴴ) R

theorem blockMatrix_isHermitian (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.IsHermitian) (hR : R.IsHermitian) : (blockMatrix P Q R).IsHermitian := by
  rw [Matrix.IsHermitian, blockMatrix]
  simp [Matrix.fromBlocks_conjTranspose, hP.eq, hR.eq]

/-- Pseudoinverse Schur complement: `P − Q·R⁺·Q†`. -/
noncomputable def schurComplement (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin D₁) (Fin D₁) ℂ :=
  P - Q * (Douglas.pinv R) * (Qᴴ)

/-- **Schur complement theorem** (Wolf Theorem 5.2).
For PSD blocks P and R, the following are equivalent:
1. The block matrix [[P, Q], [Q†, R]] is PSD
2. ker(R) ⊆ ker(Q) and the pseudoinverse Schur complement P − Q·R⁺·Q† is PSD
3. ker(R) ⊆ ker(Q) and ‖P^{-1/2}·Q·R^{-1/2}‖ ≤ 1 (contraction)

Proof follows Wolf: (1)→(2) via quadratic-form minimization,
(2)→(3) via algebraic manipulation with P^{1/2} and R^{1/2},
(3)→(1) via the representation with contraction K. -/
theorem schur_tfae (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef) :
    List.TFAE [
      (blockMatrix P Q R).PosSemidef,
      (∀ (y : Fin D₂ → ℂ), mulVec R y = 0 → mulVec Q y = 0) ∧
        (schurComplement P Q R).PosSemidef,
      (∀ (y : Fin D₂ → ℂ), mulVec R y = 0 → mulVec Q y = 0) ∧
        (‖(CFC.sqrt P)⁻¹ * Q * (CFC.sqrt R)⁻¹‖ ≤ 1)
    ] := by
  sorry

end SchurComplement
