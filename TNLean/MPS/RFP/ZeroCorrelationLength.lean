/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Core.Transfer
import TNLean.MPS.Core.Correlations
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

Concretely, for every right density `ρR` and observables `X`, `Y`, the
connected correlator `⟨X₀ Yₙ⟩ − ⟨X⟩⟨Y⟩` is the same for all distances `n`. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR X Y : Matrix (Fin D) (Fin D) ℂ) (m n : ℕ),
    twoPointExpectation A ρR X Y m = twoPointExpectation A ρR X Y n

/-- Local orthogonality: the Kraus operators of `A` satisfy trace-orthogonality,
i.e. `∑ k, (A k i)ᴴ * (A k j) = 0` for `i ≠ j`.
Equivalently, the mixed transfer map `E_{A_i, A_j}` vanishes for distinct
block indices. See arXiv:1606.00608, Definition 3.5. -/
def IsLocallyOrthogonal (A : MPSTensor d D) : Prop :=
  ∀ i j : Fin d, i ≠ j →
    (A i)ᴴ * (A j) = 0

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
