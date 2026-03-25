/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Core.Transfer
import TNLean.MPS.BNT.Construction
import TNLean.Spectral.SpectralGap
import TNLean.Algebra.ScalarPowerSumIdentity

/-!
# Zero correlation length (ZCL) for MPS tensors

This file defines zero-correlation-length (ZCL) conditions for MPS tensors,
following arXiv:1606.00608 §3.2 (Cirac–Pérez-García–Schuch–Verstraete).

Three predicates are introduced:

* `IsCID A` — correlations are independent of distance.
* `IsLocallyOrthogonal A` — the BNT components have vanishing mixed transfer
  operators.
* `IsZCL A` — the conjunction of local orthogonality and CID.

The main result (Theorem 3.8) asserts that for a canonical-form tensor,
`IsZCL` is equivalent to having an idempotent transfer map (`IsRFP`).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Correlations independent of distance: the two-point correlation function
of any pair of local observables is independent of the separation between
them. See arXiv:1606.00608, Definition 3.3.

TODO: formalize in terms of `twoPointExpectation` from `Core/Correlations`. -/
def IsCID (_A : MPSTensor d D) : Prop :=
  sorry

/-- Local orthogonality: the BNT elements of `A` have vanishing mixed
transfer operators, i.e. `Σ_i A^i_j ⊗ Ā^i_{j'} = 0` for `j ≠ j'`.
See arXiv:1606.00608, Definition 3.5.

TODO: formalize in terms of `mixedTransferMap` from `Spectral/`. -/
def IsLocallyOrthogonal (_A : MPSTensor d D) : Prop :=
  sorry

/-- Zero correlation length: a tensor has ZCL when it is both locally
orthogonal and has correlations independent of distance.
See arXiv:1606.00608, Definition 3.6. -/
def IsZCL (A : MPSTensor d D) : Prop :=
  IsLocallyOrthogonal A ∧ IsCID A

/-- **Theorem 3.8** (arXiv:1606.00608): For a canonical-form MPS tensor,
ZCL is equivalent to the transfer map being idempotent (i.e. `IsRFP`).

Forward: `E² = E` implies CID (from the correlation formula) and LO
(from spectral gap of mixed transfer).
Reverse: if `E² ≠ E`, block-injectivity constructs observables detecting
a subleading eigenvalue; Newton–Girard handles the μ-coefficient phases.

TODO: add `IsCanonicalForm` hypothesis and prove both directions. -/
theorem zcl_iff_idempotent_transfer (A : MPSTensor d D)
    /- (hCF : IsCanonicalForm μ A) -/ :
    IsZCL A ↔ IsRFP A := by
  sorry

end MPSTensor
