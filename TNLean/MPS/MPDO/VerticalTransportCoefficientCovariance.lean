/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAssociativity
import TNLean.MPS.MPDO.BNTAlgebraTensorClause

/-!
# Covariance of BNT coefficients under vertical transport

This file records the change-of-normalization law for the structure
coefficients of two explicitly identified vertical BNT operator families.  An
algebra isomorphism identifies the ambient operator algebras at each length,
while a nonzero scalar attached to each label records the normalization of its
representative.  Linear independence then determines the transformed
coefficients uniquely.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 1997--2008
-/

open scoped BigOperators

noncomputable section

namespace MPOTensor

namespace BNTLabelOperatorFamily

variable {Λ Λ' : Type*} {O O' : ℕ → Type*}

/-- Explicit transport between two vertical BNT operator families.

The label equivalence identifies sectors, the nonzero scalars record the
normalization of their representatives, and the algebra isomorphism identifies
the ambient operator algebras at each positive length.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equations
`eq:vertical-coefficient-explicit-transport` and
`eq:vertical-coefficient-covariance`. -/
structure ExplicitVerticalTransport
    [∀ L, Semiring (O L)] [∀ L, Algebra ℂ (O L)]
    [∀ L, Semiring (O' L)] [∀ L, Algebra ℂ (O' L)]
    (op : BNTLabelOperatorFamily Λ O) (op' : BNTLabelOperatorFamily Λ' O') where
  /-- Identification of target labels with source labels. -/
  labelEquiv : Λ' ≃ Λ
  /-- Relative normalization of each target representative. -/
  scale : Λ' → ℂ
  /-- Every relative normalization is nonzero. -/
  scale_ne_zero : ∀ α, scale α ≠ 0
  /-- Identification of the ambient operator algebras at each positive length. -/
  algebraEquiv : ∀ L, 0 < L → O L ≃ₐ[ℂ] O' L
  /-- The target representative is the transported source representative,
  multiplied by the corresponding length power of its normalization. -/
  operator_eq : ∀ L (hL : 0 < L) α,
    op'.operator L α =
      scale α ^ L • algebraEquiv L hL (op.operator L (labelEquiv α))

/-- The coefficient family obtained by explicit vertical transport.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equation
`eq:vertical-coefficient-covariance`. -/
def verticalTransportCoefficients
    (c : BNTLabelCoefficientFamily Λ) (e : Λ' ≃ Λ) (s : Λ' → ℂ) :
    BNTLabelCoefficientFamily Λ' where
  coeff L α β γ := ((s α * s β) / s γ) ^ L * c.coeff L (e α) (e β) (e γ)

variable [Fintype Λ] [Fintype Λ']
  [∀ L, Ring (O L)] [∀ L, Algebra ℂ (O L)]
  [∀ L, Ring (O' L)] [∀ L, Algebra ℂ (O' L)]

/-- Explicit vertical transport carries a same-length product law to the
scale-covariant coefficient family.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equations
`eq:vertical-coefficient-explicit-transport` and
`eq:vertical-coefficient-covariance`. -/
theorem ExplicitVerticalTransport.hasSameLengthProductForm_verticalTransport
    {op : BNTLabelOperatorFamily Λ O} {op' : BNTLabelOperatorFamily Λ' O'}
    {c : BNTLabelCoefficientFamily Λ}
    (T : ExplicitVerticalTransport op op') (h : op.HasSameLengthProductForm c) :
    op'.HasSameLengthProductForm (verticalTransportCoefficients c T.labelEquiv T.scale) := by
  intro L hL α β
  rw [T.operator_eq L hL α, T.operator_eq L hL β]
  rw [smul_mul_smul, ← map_mul]
  rw [h L hL]
  simp only [map_sum, map_smul]
  rw [Finset.smul_sum]
  rw [← T.labelEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro γ _
  rw [T.operator_eq L hL γ]
  simp only [verticalTransportCoefficients, smul_smul]
  congr 1
  have hscalePow :
      ((T.scale α * T.scale β) / T.scale γ) ^ L * T.scale γ ^ L =
        (T.scale α * T.scale β) ^ L := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero L (T.scale_ne_zero γ))]
  rw [← mul_pow (T.scale α) (T.scale β)]
  calc
    (T.scale α * T.scale β) ^ L *
        c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) =
      c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) *
        (T.scale α * T.scale β) ^ L := mul_comm _ _
    _ = c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) *
        (((T.scale α * T.scale β) / T.scale γ) ^ L * T.scale γ ^ L) := by
      rw [hscalePow]
    _ = ((T.scale α * T.scale β) / T.scale γ) ^ L *
        c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) *
          T.scale γ ^ L := by ring

/-- At a linearly independent positive length, explicit vertical transport
forces the scale-covariant comparison law for the structure coefficients.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equation
`eq:vertical-coefficient-covariance`. -/
theorem ExplicitVerticalTransport.coeff_eq_verticalTransport_of_linearIndependentAt
    {op : BNTLabelOperatorFamily Λ O} {op' : BNTLabelOperatorFamily Λ' O'}
    {c : BNTLabelCoefficientFamily Λ} {c' : BNTLabelCoefficientFamily Λ'}
    (T : ExplicitVerticalTransport op op') (h : op.HasSameLengthProductForm c)
    (h' : op'.HasSameLengthProductForm c') {L : ℕ} (hL : 0 < L)
    (hli : op'.LinearIndependentAt L) (α β γ : Λ') :
    c'.coeff L α β γ =
      ((T.scale α * T.scale β) / T.scale γ) ^ L *
        c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) := by
  symm
  exact (T.hasSameLengthProductForm_verticalTransport h).coeff_eq_of_linearIndependentAt
    h' hL hli α β γ

/-- If the normalizations multiply compatibly on a product triple, explicit
vertical transport preserves its structure coefficient exactly.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equation
`eq:vertical-coefficient-covariance`. -/
theorem ExplicitVerticalTransport.coeff_eq_of_scale_mul_eq_of_linearIndependentAt
    {op : BNTLabelOperatorFamily Λ O} {op' : BNTLabelOperatorFamily Λ' O'}
    {c : BNTLabelCoefficientFamily Λ} {c' : BNTLabelCoefficientFamily Λ'}
    (T : ExplicitVerticalTransport op op') (h : op.HasSameLengthProductForm c)
    (h' : op'.HasSameLengthProductForm c') {L : ℕ} (hL : 0 < L)
    (hli : op'.LinearIndependentAt L) {α β γ : Λ'}
    (hscale : T.scale α * T.scale β = T.scale γ) :
    c'.coeff L α β γ =
      c.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) := by
  rw [T.coeff_eq_verticalTransport_of_linearIndependentAt h h' hL hli]
  rw [hscale, div_self (T.scale_ne_zero γ), one_pow, one_mul]

end BNTLabelOperatorFamily

namespace BNTAlgebraTensorClause

variable {d D d' D' : ℕ} {M : MPOTensor d D} {M' : MPOTensor d' D'}

/-- Explicit vertical transport between two tensor-attached BNT clauses gives
the scale-covariant comparison law for their structure coefficients.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equation
`eq:vertical-coefficient-covariance`. -/
theorem coeff_eq_of_explicitVerticalTransport
    (H : BNTAlgebraTensorClause M) (H' : BNTAlgebraTensorClause M')
    (T : BNTLabelOperatorFamily.ExplicitVerticalTransport H.operators H'.operators)
    {L : ℕ} (hL : 0 < L) (hli : H'.operators.LinearIndependentAt L)
    (α β γ : Fin H'.labelCount) :
    H'.coeffs.coeff L α β γ =
      ((T.scale α * T.scale β) / T.scale γ) ^ L *
        H.coeffs.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) :=
  T.coeff_eq_verticalTransport_of_linearIndependentAt
    H.algebraClause.sameLengthProduct H'.algebraClause.sameLengthProduct hL hli α β γ

/-- Under multiplicative compatibility of the representative normalizations,
explicit vertical transport preserves a tensor-attached structure coefficient
exactly.

Source: arXiv:1606.00608, Appendix C.4, lines 1997--2008; see also
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>, equation
`eq:vertical-coefficient-covariance`. -/
theorem coeff_eq_of_explicitVerticalTransport_of_scale_mul_eq
    (H : BNTAlgebraTensorClause M) (H' : BNTAlgebraTensorClause M')
    (T : BNTLabelOperatorFamily.ExplicitVerticalTransport H.operators H'.operators)
    {L : ℕ} (hL : 0 < L) (hli : H'.operators.LinearIndependentAt L)
    {α β γ : Fin H'.labelCount} (hscale : T.scale α * T.scale β = T.scale γ) :
    H'.coeffs.coeff L α β γ =
      H.coeffs.coeff L (T.labelEquiv α) (T.labelEquiv β) (T.labelEquiv γ) :=
  T.coeff_eq_of_scale_mul_eq_of_linearIndependentAt
    H.algebraClause.sameLengthProduct H'.algebraClause.sameLengthProduct hL hli hscale

end BNTAlgebraTensorClause

end MPOTensor
