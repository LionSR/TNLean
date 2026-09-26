/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLawScaling
import TNLean.MPS.MPDO.CPSVExample412NormalizedGSNNCH
import TNLean.MPS.MPDO.RFPViaTS

/-!
# CPSV16 Example 4.12: all four properties of the normalized tensor

**Source.** Cirac--Perez-Garcia--Schuch--Verstraete 2017 (arXiv:1606.00608),
Example 4.12, `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 932--939: the tensor
generating `𝟙^{⊗ N} + σ_z^{⊗ N}` is SAL, has ZCL, is not of the commuting form
`(rhoNComm)`, and satisfies the renormalization fixed-point property.

**Formalized here.** For the density-normalized representative
`Mhat = (1 / 2) • M`: saturation of the area law (Definition 4.6), literal
physical-trace idempotence (Definition 4.2), failure of the commuting form
(Definition 4.8), and the two channel equations of Definition 4.1, collected in
one statement.

**Local fix (normalization):** the source prints the unscaled tensor `M`, whose
physical-trace transfer squares to twice itself, so the literal Definition 4.2
diagram and the channel equations fail for it. For `(1 / 2) • M`, which
generates the same normalized states, saturation of the area law, zero
correlation length, failure of the commuting form, and the two channel
equations of Definition 4.1 hold. Documented in
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_example_4_12_normalization.pdf>.

**Scope restriction (canonical weight):** the fixed-point conjunct of
`Mhat_isSAL_isPhysicalTraceIdempotent_not_isGSNNCH_isRFPViaTS` is the bare
channel predicate `IsRFPViaTS`. It does not assert the line-246 global
unit-weight canonical convention under which the source reads Definition 4.1,
so the conclusion is the channel content of the source's fixed-point claim,
not the full claim. Documented in
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>.

## Main results

* `Mhat_isSAL`: the normalized tensor verifies saturation of the area law.
* `Mhat_isPhysicalTraceIdempotent`: its physical-trace transfer is idempotent.
* `Mhat_isSAL_isPhysicalTraceIdempotent_not_isGSNNCH_isRFPViaTS`: the four
  claims of Example 4.12 for the normalized tensor, with the fixed-point claim
  read as the channel equations.

## References

- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- Cirac, Perez-Garcia,
  Schuch, Verstraete, *Matrix product density operators: Renormalization fixed
  points and boundary theories*
-/

open scoped Matrix ComplexOrder

namespace MPOTensor.CPSVExample412NormalizedRFP

/-- The density-normalized representative of Example 4.12 verifies saturation of
the area law.

Source: arXiv:1606.00608, Example 4.12, lines 937--938 ("this tensor is SAL"),
with Definition 4.6, lines 811--815, transported from the printed tensor along
the positive rescaling by `1 / 2`. -/
theorem Mhat_isSAL : IsSAL Mhat :=
  (isSAL_smul_ofReal_iff _ (by norm_num)).2 CPSVExample412Literal.M_isSAL

/-- The density-normalized representative of Example 4.12 has zero correlation
length in the literal sense of Definition 4.2: its physical-trace transfer is
idempotent.

Source: arXiv:1606.00608, Example 4.12, lines 937--938 ("has ZCL"), with
Definition 4.2, lines 735--739. -/
theorem Mhat_isPhysicalTraceIdempotent : IsPhysicalTraceIdempotent Mhat :=
  isPhysicalTraceIdempotent_of_isRFPViaTS Mhat Mhat_isRFPViaTS

/-- **CPSV16 Example 4.12.** The density-normalized representative of the printed
tensor verifies saturation of the area law, has zero correlation length in the
literal sense of Definition 4.2, is not of the commuting form of
Definition 4.8, and satisfies the two channel equations of Definition 4.1.

Source: arXiv:1606.00608, Example 4.12, lines 937--939.

The statement concerns `Mhat = (1 / 2) • M` rather than the printed tensor
`M`, and its last conjunct is the bare channel predicate `IsRFPViaTS`; see the
module's normalization fix and canonical-weight scope restriction. -/
theorem Mhat_isSAL_isPhysicalTraceIdempotent_not_isGSNNCH_isRFPViaTS :
    IsSAL Mhat ∧ IsPhysicalTraceIdempotent Mhat ∧ ¬ IsGSNNCH Mhat ∧
      IsRFPViaTS Mhat :=
  ⟨Mhat_isSAL, Mhat_isPhysicalTraceIdempotent, Mhat_not_isGSNNCH, Mhat_isRFPViaTS⟩

end MPOTensor.CPSVExample412NormalizedRFP
