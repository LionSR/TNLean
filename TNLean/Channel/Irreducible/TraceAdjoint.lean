/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.KrausSetup

/-!
# Trace-adjoint identity for transfer maps

For a transfer map $E(X)=\sum_i K_iXK_i^*$, the adjoint trace pairing reads
$$
\operatorname{tr}(\rho E(X))
  = \operatorname{tr}\!\left(\sum_i K_i^*\rho K_i\,X\right).
$$

## Main declaration

* `trace_mul_transferMap_adjoint`: the adjoint trace-pairing identity in MPS transfer-map
  notation.
-/

open scoped Matrix ComplexOrder BigOperators

variable {D : ℕ}

/-- The adjoint trace-pairing identity in MPS transfer-map notation. -/
lemma trace_mul_transferMap_adjoint
    {n : ℕ}
    (K : MPSTensor n D)
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE_eq : E = MPSTensor.transferMap (d := n) (D := D) K)
    (ρ X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ρ * E X) =
      Matrix.trace (MPSTensor.transferMap (d := n) (D := D) (fun i => (K i)ᴴ) ρ * X) :=
  Kraus.trace_mul_transferMap_adjoint K hE_eq ρ X
