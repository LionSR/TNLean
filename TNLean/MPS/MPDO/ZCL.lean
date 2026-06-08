/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.RFP.Defs

/-!
# Zero correlation length for MPO tensors

Definitions of zero-correlation-length conditions for mixed-state tensor
networks, following arXiv:1606.00608, lines 736–741.

## Main definitions

* `MPOTensor.IsZCL`: the MPO transfer map is idempotent.
* `MPOTensor.isZCL_iff_toMPSTensor_isRFP`: this condition is equivalent to the
  pure-state RFP condition for the doubled-index MPS tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.3
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- An MPO tensor has **zero correlation length** when its transfer map is
*literally* idempotent: `E_M ∘ E_M = E_M`.

**Scope restriction (canonical form):** the source ZCL (arXiv:1606.00608,
Definition 4.2, lines 735–739, the figure `MPDO_ZCL.png`) is the natural
extension of the pure-state ZCL. The proof of the pure-state equivalence pins
that down as `𝔼² = 𝔼` **for a tensor in canonical form** (line 1248): idempotence
after the transfer operator is normalized so that its leading eigenvalue is `1`.
The literal condition here is faithful only for such normalized representatives.
For a general representative it is strictly stronger, since it forces the leading
eigenvalue to equal `1`, whereas the source ZCL is invariant under the rescaling
`E_M ↦ λ E_M`. The deviation is witnessed by `exists_isPRFP_not_isZCL`, where the
purification's trace contraction drops the leading eigenvalue. The faithful
(normalized) ZCL and the source's equivalence between PRFP and ZCL remain open. Recorded
in `docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

See arXiv:1606.00608, lines 735–739 (and the canonical-form characterization at
line 1248), and arXiv:2011.12127, Section II.E.2, lines 937–939. -/
def IsZCL (M : MPOTensor d D) : Prop :=
  transferMap M ∘ₗ transferMap M = transferMap M

/-- ZCL for an MPO tensor is equivalent to the pure-state RFP condition for
the doubled-index MPS tensor `M.toMPSTensor`. Both statements assert
idempotence of the same transfer map. -/
theorem isZCL_iff_toMPSTensor_isRFP (M : MPOTensor d D) :
    IsZCL M ↔ MPSTensor.IsRFP (M.toMPSTensor) := by
  simp [IsZCL, MPSTensor.IsRFP]

end MPOTensor
