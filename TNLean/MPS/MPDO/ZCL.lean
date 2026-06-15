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

* `MPOTensor.physTraceTransfer`: the physical-trace transfer
  `∑ i, M i i` obtained by closing the ket and bra physical legs of one tensor.
* `MPOTensor.IsSourceZCL`: the source-faithful zero-correlation-length
  condition for the physical-trace transfer.
* `MPOTensor.isSourceZCL_of_physTraceTransfer_sq`: literal idempotence of the
  physical-trace transfer gives source ZCL.
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
`E_M ↦ λ E_M`. The deviation is witnessed by
`MPOTensor.exists_isLocalPurificationRFP_not_isZCL`: the rescaled purification
`d = dK = 2`, `D = 1`, `A = [1/√2, 0, 0, 1/√2]` satisfies the local
purification-RFP condition, yet its transfer map is `½ • id`, so
`E_M ∘ E_M = ¼ • id ≠ E_M`; the trace contraction in the purification has dropped
the leading eigenvalue from `1` to `½`. The faithful (normalized) ZCL and the
source's equivalence between PRFP and ZCL remain open. Recorded in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

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

/-- The **physical-trace transfer** `𝒯_M = ∑_i M^{ii}` of an MPO tensor: the
single bond matrix obtained by closing the ket and bra physical legs of one
tensor. This is the transfer object of the source zero-correlation-length
condition (arXiv:1606.00608, Definition 4.2, lines 735–739), as identified in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`. It is distinct
from the doubled-index completely positive map `transferMap`, which sums
`∑_{i,j} M^{ij} X (M^{ij})ᴴ` over both physical legs; the physical-trace transfer
instead contracts the two legs of a single tensor. -/
noncomputable def physTraceTransfer (M : MPOTensor d D) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d, M i i

/-- **Source-faithful zero correlation length** (arXiv:1606.00608, Definition 4.2).
An MPO tensor has zero correlation length when its physical-trace transfer
`𝒯_M = ∑_i M^{ii}` is nonzero and idempotent up to a positive scalar:
`𝒯_M * 𝒯_M = λ • 𝒯_M` for some `λ > 0`. The condition is invariant under the
rescaling `M ↦ c M`, and literal idempotence `𝒯_M * 𝒯_M = 𝒯_M` is the `λ = 1`
canonical-form representative. The nonzero clause excludes the degenerate zero
transfer, which satisfies `𝒯_M * 𝒯_M = λ • 𝒯_M` vacuously for every `λ`.

This is the Option 1 formalization of
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`: it uses the source
transfer object `𝒯_M`, unlike `MPOTensor.IsZCL`, which records idempotence of the
doubled-index map `transferMap`. -/
def IsSourceZCL (M : MPOTensor d D) : Prop :=
  physTraceTransfer M ≠ 0 ∧
    ∃ lam : ℝ, 0 < lam ∧
      physTraceTransfer M * physTraceTransfer M = (lam : ℂ) • physTraceTransfer M

/-- Literal idempotence of the physical-trace transfer (the `λ = 1`
canonical-form case) gives source zero correlation length, provided the transfer
is nonzero. -/
theorem isSourceZCL_of_physTraceTransfer_sq
    (M : MPOTensor d D) (h0 : physTraceTransfer M ≠ 0)
    (hidem : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M) :
    IsSourceZCL M :=
  ⟨h0, 1, one_pos, by rw [hidem, Complex.ofReal_one, one_smul]⟩

/-- **Normalized transfer is idempotent under source zero correlation length.**
If the physical-trace transfer satisfies
$\mathcal{T}_M^2 = \lambda\,\mathcal{T}_M$ with $\lambda > 0$, then
$\lambda^{-1}\mathcal{T}_M$ is idempotent. Hence the eigenvalues of
$\mathcal{T}_M$ lie in $\{0,\lambda\}$, and $\lambda$ is its leading
eigenvalue. -/
theorem IsSourceZCL.normalized_idempotent {M : MPOTensor d D} (h : IsSourceZCL M) :
    ∃ lam : ℝ, 0 < lam ∧ IsIdempotentElem ((lam : ℂ)⁻¹ • physTraceTransfer M) := by
  obtain ⟨_, lam, hlam, hidem⟩ := h
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlam
  refine ⟨lam, hlam, ?_⟩
  change ((lam : ℂ)⁻¹ • physTraceTransfer M) * ((lam : ℂ)⁻¹ • physTraceTransfer M)
    = (lam : ℂ)⁻¹ • physTraceTransfer M
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hidem, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ hlamC, mul_one]

end MPOTensor
