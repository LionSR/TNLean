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
* `MPOTensor.IsPhysicalTraceIdempotent`: literal Definition 4.2 physical-trace
  idempotence.
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
`MPOTensor.exists_isPRFP_not_isZCL`: the rescaled purification
`d = dK = 2`, `D = 1`, `A = [1/√2, 0, 0, 1/√2]` is a purification
renormalization fixed point, yet its transfer map is `½ • id`, so
`E_M ∘ E_M = ¼ • id ≠ E_M`; the trace contraction in the purification has dropped
the leading eigenvalue from `1` to `½`. The predicate
`IsPhysicalTraceIdempotent` records the paper's literal fixed-tensor diagram.
The separate predicate `IsSourceZCL` uses the same physical-trace object but
allows a positive scalar, giving a broader scale-invariant relation. Recorded
in <https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>.

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
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>.
It is distinct
from the doubled-index completely positive map `transferMap`, which sums
`∑_{i,j} M^{ij} X (M^{ij})ᴴ` over both physical legs; the physical-trace transfer
instead contracts the two legs of a single tensor. -/
noncomputable def physTraceTransfer (M : MPOTensor d D) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d, M i i

/-- **Literal physical-trace idempotence.** An MPO tensor satisfies the
zero-correlation-length diagram of arXiv:1606.00608, Definition 4.2,
lines 735--739, when its physical-trace transfer is idempotent. This predicate
records the fixed-tensor equation from the source and is distinct from both the
scale-invariant relation `IsSourceZCL` and doubled-index transfer idempotence
`IsZCL`. -/
def IsPhysicalTraceIdempotent (M : MPOTensor d D) : Prop :=
  IsIdempotentElem (physTraceTransfer M)

/-- Literal physical-trace idempotence is the matrix equation
`𝒯_M * 𝒯_M = 𝒯_M` from arXiv:1606.00608, Definition 4.2, lines 735--739. -/
theorem isPhysicalTraceIdempotent_iff (M : MPOTensor d D) :
    IsPhysicalTraceIdempotent M ↔
      physTraceTransfer M * physTraceTransfer M = physTraceTransfer M :=
  isIdempotentElem_iff

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
Documented in <https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>.

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
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>. -/
theorem IsSourceZCL.bondDim_ne_zero {M : MPOTensor d D} (h : IsSourceZCL M) :
    D ≠ 0 := by
  intro hD
  subst D
  exact h.1 (Subsingleton.elim _ _)

/-- Literal Definition 4.2 physical-trace idempotence, together with a nonzero
physical-trace transfer, implies the broader scale-invariant relation. The
nonzero hypothesis is not part of the literal source diagram and only excludes
the zero transfer from `IsSourceZCL`. -/
theorem IsPhysicalTraceIdempotent.isSourceZCL {M : MPOTensor d D}
    (h : IsPhysicalTraceIdempotent M) (h0 : physTraceTransfer M ≠ 0) :
    IsSourceZCL M :=
  ⟨h0, 1, one_pos, by
    rw [(isPhysicalTraceIdempotent_iff M).mp h, Complex.ofReal_one, one_smul]⟩

/-- The equation form of literal physical-trace idempotence gives the
scale-invariant relation, provided the transfer is nonzero. -/
theorem isSourceZCL_of_physTraceTransfer_sq
    (M : MPOTensor d D) (h0 : physTraceTransfer M ≠ 0)
    (hidem : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M) :
    IsSourceZCL M :=
  (isPhysicalTraceIdempotent_iff M).2 hidem |>.isSourceZCL h0

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
