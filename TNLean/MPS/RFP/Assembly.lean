/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.RFP.StructuralForm

/-!
# Per-block equivalence of RFP and ZCL

This file proves the single-block consequence used in the RFP-ZCL comparison
from arXiv:1606.00608, Theorem 3.10:

> for each block of a canonical-form MPS tensor, the block is a
> renormalization fixed point (RFP) if and only if that block has the local
> zero-correlation-length (ZCL) property.

**Scope restriction:** The source theorem uses the BNT-family ZCL condition:
CID together with local orthogonality between distinct BNT elements. The theorem
in this file applies the single-block predicate to one chosen block and does not
by itself formalize the full BNT-family statement. This restriction is recorded
in `docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`.

This reduces directly to `zcl_iff_idempotent_transfer` (Theorem 3.8).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Per-block RFP-ZCL equivalence inside a canonical form
(arXiv:1606.00608, Theorem 3.10, single-block consequence).

For a canonical-form MPS tensor, each chosen block is a renormalization fixed
point if and only if that same block has the local zero-correlation-length
property.

**Scope restriction:** The source theorem uses a BNT-family ZCL condition,
namely CID together with local orthogonality between distinct BNT elements. This
declaration only applies the single-block predicate to `A k`. See
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex`.

Proved by `zcl_iff_idempotent_transfer.symm`. -/
theorem rfp_iff_zcl {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (_hCF : IsCanonicalForm μ A) (k : Fin r) :
    IsRFP (A k) ↔ IsZCL (A k) :=
  (zcl_iff_idempotent_transfer (A k)).symm

end MPSTensor
