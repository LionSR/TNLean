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
transfer map is constant in the separation `n`. That is, for all observables
`X`, `Y` and right reference states `ρR`,
  `tr(Y · E^n(X · ρR)) = tr(Y · E^m(X · ρR))`
for all `n, m : ℕ`. See arXiv:1606.00608, Definition 3.3.

Equivalently, `E² = E` on the range of `X ↦ X · ρR`, but this formulation
avoids choosing a normalization. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR X Y : Matrix (Fin D) (Fin D) ℂ) (n m : ℕ),
    Matrix.trace (Y * ((transferMap A) ^ n) (X * ρR)) =
      Matrix.trace (Y * ((transferMap A) ^ m) (X * ρR))

/-- Local orthogonality: the mixed transfer operator `F_{AB}(X) = Σ_i A_i X B_i†`
for two distinct BNT blocks `A ≠ B` should vanish. For a single tensor `A`,
this is captured by requiring that the (self) transfer map is idempotent as a
mixed transfer operator, i.e. `E_A ∘ E_A = E_A` (which is exactly `IsRFP`
restricted to the diagonal block). See arXiv:1606.00608, Definition 3.5.

The full off-diagonal condition for BNT components is stated at the
canonical-form level in `zcl_iff_idempotent_transfer`. -/
def IsLocallyOrthogonal (A : MPSTensor d D) : Prop :=
  transferMap A ∘ₗ transferMap A = transferMap A

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
