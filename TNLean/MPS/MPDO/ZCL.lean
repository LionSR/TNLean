/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
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
* `MPOTensor.IsSourceZCL`: the scale-invariant nonzero physical-trace relation.
* `MPOTensor.IsSourceZCL.bondDim_ne_zero`: this relation forces a nonzero bond
  space.
* `MPOTensor.isSourceZCL_of_physTraceTransfer_sq`: literal idempotence of the
  physical-trace transfer gives the up-to-scalar relation.
* `MPOTensor.IsZCL`: the MPO transfer map is idempotent.
* `MPOTensor.isZCL_iff_toMPSTensor_isTransferIdempotent`: this condition is equivalent to the
  pure-state RFP condition for the doubled-index MPS tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Section 4.3
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- An MPO tensor has **zero correlation length** when its transfer map is
*literally* idempotent: `E_M ∘ E_M = E_M`.

**Scope restriction (different transfer object):** The source's mixed-state ZCL
diagram (arXiv:1606.00608, Definition 4.2, lines 735--739) is literal
idempotence of the physical-trace transfer `physTraceTransfer M`. The condition
here is instead literal idempotence of the doubled-index completely positive
map `transferMap M`. These are different transfer objects. The deviation is
witnessed by
`MPOTensor.exists_isLocalPurificationRFP_not_isZCL`: the rescaled purification
`d = dK = 2`, `D = 1`, `A = [1/√2, 0, 0, 1/√2]` satisfies the local
purification-RFP condition, yet its transfer map is `½ • id`, so
`E_M ∘ E_M = ¼ • id ≠ E_M`; the trace contraction in the purification has dropped
the leading eigenvalue from `1` to `½`. The separate predicate `IsSourceZCL`
uses the physical-trace object but allows a positive scalar; it is a broader
scale-invariant repair, not the paper's literal fixed-tensor diagram. Recorded in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

See arXiv:1606.00608, lines 735–739 (and the canonical-form characterization at
line 1248), and arXiv:2011.12127, Section II.E.2, lines 937–939. -/
def IsZCL (M : MPOTensor d D) : Prop :=
  transferMap M ∘ₗ transferMap M = transferMap M

/-- ZCL for an MPO tensor is equivalent to the pure-state RFP condition for
the doubled-index MPS tensor `M.toMPSTensor`. Both statements assert
idempotence of the same transfer map. -/
theorem isZCL_iff_toMPSTensor_isTransferIdempotent (M : MPOTensor d D) :
    IsZCL M ↔ MPSTensor.IsTransferIdempotent (M.toMPSTensor) := by
  rw [IsZCL, MPSTensor.IsTransferIdempotent, transferMap_eq_toMPSTensor]

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

/-- **Scale-invariant nonzero physical-trace relation.** An MPO tensor satisfies
this relation when its physical-trace transfer `𝒯_M = ∑_i M^{ii}` is nonzero and
idempotent up to a positive scalar:
`𝒯_M * 𝒯_M = λ • 𝒯_M` for some `λ > 0`. The condition is invariant under
positive real rescaling `M ↦ c M`, and literal idempotence
`𝒯_M * 𝒯_M = 𝒯_M` is the `λ = 1` physical-trace-normalized representative. The
nonzero clause excludes the degenerate zero transfer, which satisfies the
relation vacuously for every `λ`.

**Scope restriction (up-to-scalar interpretation):** The paper's diagram in
arXiv:1606.00608, Definition 4.2, lines 735--739, is the literal `λ = 1`
identity for a fixed tensor. This development's predicate is a broader,
scale-invariant repair at the level of the generated state family; it must not
be substituted unchanged into fixed-tensor implications such as Theorem 4.9.
Documented in `docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

The relation uses the paper's physical-trace transfer object `𝒯_M`, unlike
`MPOTensor.IsZCL`, which records idempotence of the doubled-index map
`transferMap`. -/
def IsSourceZCL (M : MPOTensor d D) : Prop :=
  physTraceTransfer M ≠ 0 ∧
    ∃ lam : ℝ, 0 < lam ∧
      physTraceTransfer M * physTraceTransfer M = (lam : ℂ) • physTraceTransfer M

/-- A tensor satisfying the nonzero physical-trace relation has nonzero bond
dimension.

The required nonzero physical-trace transfer cannot be represented on an empty
bond space.

Scope: the up-to-scalar interpretation documented in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`. -/
theorem IsSourceZCL.bondDim_ne_zero {M : MPOTensor d D} (h : IsSourceZCL M) :
    D ≠ 0 := by
  intro hD
  subst D
  exact h.1 (Subsingleton.elim _ _)

/-- Literal idempotence of the physical-trace transfer (the
physical-trace-normalized `λ = 1` case) gives the scale-invariant relation,
provided the transfer is nonzero. -/
theorem isSourceZCL_of_physTraceTransfer_sq
    (M : MPOTensor d D) (h0 : physTraceTransfer M ≠ 0)
    (hidem : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M) :
    IsSourceZCL M :=
  ⟨h0, 1, one_pos, by rw [hidem, Complex.ofReal_one, one_smul]⟩

/-- **The normalized transfer is idempotent under the up-to-scalar relation.**
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
  rw [smul_mul_smul_comm, hidem, smul_smul, mul_assoc, inv_mul_cancel₀ hlamC, mul_one]

end MPOTensor
