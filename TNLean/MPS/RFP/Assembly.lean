/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.RFP.StructuralForm

/-!
# Assembly: RFP ⟺ ZCL equivalence

This file assembles the forward and backward directions of the main
equivalence from arXiv:1606.00608, Theorem 3.10 (partial):

> For a canonical-form MPS tensor, being a renormalization fixed point (RFP)
> is equivalent to having zero correlation length (ZCL).

The NNCPH (nearest-neighbour commuting parent Hamiltonian) direction of
Theorem 3.10 is deferred to a later module.

This reduces directly to `zcl_iff_idempotent_transfer` (Theorem 3.8).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Theorem 3.10** (arXiv:1606.00608, partial): For a canonical-form MPS
tensor, RFP is equivalent to ZCL.

The full theorem also includes equivalence with the NNCPH condition; that
direction is deferred.

Proved by `zcl_iff_idempotent_transfer.symm`. -/
theorem rfp_iff_zcl {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) (k : Fin r) :
    IsRFP (A k) ↔ IsZCL (A k) :=
  (zcl_iff_idempotent_transfer μ A hCF k).symm

end MPSTensor
