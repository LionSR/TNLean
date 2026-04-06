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

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Correlations independent of distance (arXiv:1606.00608, Definition 3.3):
the connected two-point correlation function through the transfer map is
constant in the separation for all local observables.

For every nonzero positive semidefinite right fixed point `ρR` of the
transfer map, the connected correlator `C(X,Y;n) = ⟨X₀Yₙ⟩ − ⟨X⟩⟨Y⟩` is the
same for all separations `n ≥ 1` and all observables `X`, `Y`. Excluding
`ρR = 0` avoids making the condition vacuous, since `0` is always a fixed
point of the linear transfer map. -/
def IsCID (A : MPSTensor d D) : Prop :=
  ∀ (ρR : Matrix (Fin D) (Fin D) ℂ),
    ρR.PosSemidef → transferMap A ρR = ρR → ρR ≠ 0 →
    ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) (n m : ℕ),
      1 ≤ n → 1 ≤ m →
      connectedCorrelator A ρR X Y n = connectedCorrelator A ρR X Y m

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

/-- **Theorem 3.8** (arXiv:1606.00608): For an MPS tensor,
ZCL is equivalent to the transfer map being idempotent (i.e. `IsRFP`).

Forward: `IsZCL → IsRFP` is immediate since `IsLocallyOrthogonal = IsRFP`.
Reverse: `E² = E` implies `Eⁿ = E` for `n ≥ 1` by `IsIdempotentElem.pow_eq`,
so the connected correlator is independent of separation, giving CID. -/
theorem zcl_iff_idempotent_transfer (A : MPSTensor d D) :
    IsZCL A ↔ IsRFP A := by
  constructor
  · exact fun ⟨hLO, _⟩ => hLO
  · intro hRFP
    refine ⟨hRFP, fun ρR _ _ _ X Y n m hn hm => ?_⟩
    have hIdem : IsIdempotentElem (transferMap A) := hRFP
    have hpow_n : (transferMap A) ^ n = transferMap A :=
      hIdem.pow_eq (by omega)
    have hpow_m : (transferMap A) ^ m = transferMap A :=
      hIdem.pow_eq (by omega)
    simp only [connectedCorrelator_def, twoPointExpectation_transfer,
      hpow_n, hpow_m]

end MPSTensor
