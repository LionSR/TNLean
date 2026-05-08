/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.Basic
import TNLean.MPS.Core.Transfer

/-!
# Shared trace-adjoint auxiliary lemma for irreducible-channel developments

This file factors out a common trace-pairing identity used in multiple
irreducibility proofs:

`tr(σ · E(X)) = tr(E*(σ) · X)`

where `E*(Y) = ∑ K_i* Y K_i` is the adjoint (Heisenberg-picture) map.

This identity corresponds to **Wolf's Eq. (6.33)** in the proof of
**Theorem 6.3(3)** (uniqueness of the positive eigenvalue): taking traces
against a positive-definite left eigenvector `X' > 0` of `T*` gives
`r tr(X' Y) = tr(X' T(Y)) = λ tr(X' Y)`, forcing `r = λ`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2,
  proof of Theorem 6.3(3), Eq. (6.33)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

variable {D : ℕ}

/-- The adjoint trace-pairing identity
`tr(ρ * E(X)) = tr(E†(ρ) * X)`, expressed via the conjugate-transposed Kraus
family for an `MPSTensor` transfer map. -/
lemma trace_mul_transferMap_adjoint
    {n : ℕ}
    (K : MPSTensor n D)
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE_eq : E = MPSTensor.transferMap (d := n) (D := D) K)
    (ρ X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ρ * E X) =
      Matrix.trace (MPSTensor.transferMap (d := n) (D := D) (fun i => (K i)ᴴ) ρ * X) := by
  calc
    Matrix.trace (ρ * E X)
        = Matrix.trace (ρ * MPSTensor.transferMap (d := n) (D := D) K X) := by rw [hE_eq]
    _ = Matrix.trace (Kraus.adjointMap K ρ * X) := by
          simpa only [Kraus.map, MPSTensor.transferMap_apply] using
            (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := K) ρ X)
    _ = Matrix.trace
          (MPSTensor.transferMap (d := n) (D := D) (fun i => (K i)ᴴ) ρ * X) := by
          simp [Kraus.adjointMap, MPSTensor.transferMap_apply,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
