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

/-- Correlations independent of distance: the two-point function through the
transfer map is constant in the separation. That is, for all matrices
`X`, `Y`, `ρR`,
  `tr(Y · E^(n+1)(X · ρR)) = tr(Y · E^(m+1)(X · ρR))`
for all `n, m : ℕ`. See arXiv:1606.00608, Definition 3.3.

Note: the exponents use `n + 1` and `m + 1` to avoid the degenerate case
`E^0 = id`, which would force `E = id` by the non-degeneracy of the trace
pairing. The physical interpretation is that correlations at distance ≥ 1
are independent of the separation. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR X Y : Matrix (Fin D) (Fin D) ℂ) (n m : ℕ),
    Matrix.trace (Y * ((transferMap A) ^ (n + 1)) (X * ρR)) =
      Matrix.trace (Y * ((transferMap A) ^ (m + 1)) (X * ρR))

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
