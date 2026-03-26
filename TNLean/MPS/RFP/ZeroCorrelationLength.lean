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

/-- Correlations independent of distance (arXiv:1606.00608, Definition 3.3):
the connected two-point correlation function through the transfer map is
constant in the separation for all local observables.

**Status**: `sorry` placeholder. A naive formalization quantifying
`tr(Y · E^n(X · ρR)) = tr(Y · E^m(X · ρR))` over all matrices `ρR`, `X`, `Y`
collapses to `IsRFP` by non-degeneracy of the trace pairing (see PR #271
discussion). The correct definition requires either:
(a) restricting to a specific fixed-point state and using the *connected*
    correlator `C(X,Y,n) = tr(Y · Eⁿ(X · ρ)) − tr(X·ρ)·tr(Y·ρ)`, or
(b) formulating CID at the multi-block BNT level where cross-block transfer
    operators provide non-trivial content.

TODO: formalize using `twoPointCorrelation` infrastructure once available. -/
def IsCID (_A : MPSTensor d D) : Prop :=
  sorry

/-- Local orthogonality for a single BNT block: the self-transfer map is
idempotent. For a single tensor `A`, this is equivalent to `IsRFP A`
(see `isLocallyOrthogonal_iff_isRFP`). See arXiv:1606.00608, Definition 3.5.

In the full BNT setting, local orthogonality additionally requires that
the *mixed* transfer operators `F_{jk}` vanish for `j ≠ k`. That
off-diagonal condition is captured at the canonical-form level in
`zcl_iff_idempotent_transfer`. -/
def IsLocallyOrthogonal (A : MPSTensor d D) : Prop :=
  IsRFP A

/-- `IsLocallyOrthogonal` is definitionally equal to `IsRFP` for a single
BNT block. This lemma bridges the two views. -/
lemma isLocallyOrthogonal_iff_isRFP (A : MPSTensor d D) :
    IsLocallyOrthogonal A ↔ IsRFP A :=
  Iff.rfl

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

TODO: prove both directions. -/
theorem zcl_iff_idempotent_transfer {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) (k : Fin r) :
    IsZCL (A k) ↔ IsRFP (A k) := by
  sorry

end MPSTensor
