/-  
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.Basic
import TNLean.MPS.Core.Transfer

/-!
# Shared trace-adjoint helper for irreducible-channel developments

This file factors out a common trace-pairing identity used in multiple
irreducibility proofs.
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
          simpa [Kraus.map, MPSTensor.transferMap_apply] using
            (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := K) ρ X)
    _ = Matrix.trace
          (MPSTensor.transferMap (d := n) (D := D) (fun i => (K i)ᴴ) ρ * X) := by
          simp [Kraus.adjointMap, MPSTensor.transferMap_apply,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
