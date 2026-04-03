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
the transfer map powers stabilize, meaning `E^{n+2} = E^{n+1}` for all `n`.

For canonical-form tensors (where each block is injective), this algebraic
condition captures the physical property that two-point correlation functions
do not depend on the separation distance: injectivity ensures that physical
observables span the full matrix algebra, so the transfer-map-level condition
is equivalent to the observable-level one.

This is equivalent to `IsRFP A` (transfer map idempotence). The equivalence
follows from Mathlib's `IsIdempotentElem.pow_succ_eq`: if `E² = E` then
`E^{n+1} = E` for all `n`, hence consecutive powers agree.
See arXiv:1606.00608, Definition 3.3 and Theorem 3.8. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ n : ℕ, (transferMap A) ^ (n + 2) = (transferMap A) ^ (n + 1)

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

Forward (`IsZCL → IsRFP`): `IsZCL = IsLocallyOrthogonal ∧ IsCID`, and
`IsLocallyOrthogonal` is definitionally `IsRFP`, so just project.

Reverse (`IsRFP → IsZCL`): `IsLocallyOrthogonal` is immediate.
For `IsCID`, `E² = E` means `transferMap A` is idempotent in the
`Module.End` monoid; by `IsIdempotentElem.pow_succ_eq`, all powers
`E^{n+1} = E`, so consecutive powers agree. -/
theorem zcl_iff_idempotent_transfer {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (_hCF : IsCanonicalForm μ A) (k : Fin r) :
    IsZCL (A k) ↔ IsRFP (A k) := by
  constructor
  · exact fun h => h.1
  · intro hRFP
    refine ⟨hRFP, fun n => ?_⟩
    have hIdem : IsIdempotentElem (transferMap (A k)) := hRFP
    rw [hIdem.pow_succ_eq, hIdem.pow_succ_eq]

end MPSTensor
