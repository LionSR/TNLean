/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Dimer.TwistedDimerProductLaw
import TNLean.MPS.Examples.Dimer.TwistedDimerVerticalCF

/-!
# The tensor-attached algebra clause of the $\mathbb Z_2$-twisted quantum dimer

**Scope: the algebra clause of Theorem 4.14(ii) attached to the vertical
canonical form of `T`.**  The vertical canonical form of the twisted quantum
dimer (`TNLean.MPS.MPDO.TwistedDimerVerticalCF`) has the two normalized flag
sectors as basis of normal tensors, and the same-length product law of their
closed operators (`TNLean.MPS.MPDO.TwistedDimerProductLaw`) carries the
two-label coefficient family with $\alpha = 7/10$, $\beta = 1/10$.  This file
combines the two into the tensor-attached algebra clause
`MPOTensor.BNTAlgebraTensorClause` of arXiv:1606.00608, Theorem 4.14(ii),
lines 972--993: the flag sectors are normal tensors in the sense of the source
(injective at one site and left-canonical), the coefficient family is the
trace-power family of the positive diagonal $\chi$-family `twoLabelChi`, and
the trace scalars $m_0 = m_1 = \mu = 5/8$ satisfy the length-one idempotent law
$$
  m_g = \sum_{f, f'} c^{(1)}_{f f' g}\, m_f\, m_{f'}
      = 2 (\alpha + \beta)\, \mu^2 = \tfrac{8}{5} \cdot \tfrac{25}{64} = \tfrac58 .
$$
The tensor is a project example motivated by the length-dependence question
after Theorem 4.14 (lines 995--1010); it is not a tensor stated in that source.
No comparison with a blocked basis, fusion isometry, or renormalization map is
asserted here.

## Main results

* `sectorWeight_hasIdempotentCoefficientForm` — the length-one idempotent law
  of the trace scalars;
* `T_bntAlgebraTensorClause` — the tensor-attached algebra clause of `T`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 945--959; Theorem 4.14(ii), lines 972--993; and
  lines 995--1010 (the length-dependence question motivating this project
  example)
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### The algebra clause -/

/-- The two-label coefficient family is the trace-power family of the positive
diagonal $\chi$-family `twoLabelChi` (arXiv:1606.00608, Theorem 4.14(ii),
lines 972--985). -/
def twoLabelChiTracePowerForm : PositiveBNTLabelChiTracePowerForm twoLabelCoeffs :=
  PositiveBNTLabelChiTracePowerForm.ofChi twoLabelChi twoLabelChi_posEntries

/-- **The length-one idempotent law.**  With $m_0 = m_1 = \mu = 5/8$ and the
length-one coefficients $\alpha = 7/10$, $\beta = 1/10$, each label $g$
satisfies $m_g = \sum_{f, f'} c^{(1)}_{f f' g} m_f m_{f'} = 2(\alpha + \beta)\mu^2$
(arXiv:1606.00608, Theorem 4.14(ii), lines 981--985).

Project example; not from CPSV16. -/
theorem sectorWeight_hasIdempotentCoefficientForm :
    (verticalBNTTraceScalarFamily sectorWeight).HasIdempotentCoefficientForm twoLabelCoeffs := by
  intro g
  simp only [verticalBNTTraceScalarFamily_traceScalar, sectorWeight, twoLabelCoeffs_coeff,
    Fin.sum_univ_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  fin_cases g <;> simp [IsSameChannel] <;> norm_num [mu, alpha, beta]

/-- The algebra clause for the flag-sector operators and trace scalars. -/
def flagAlgebraClause :
    BNTAlgebraClause twoLabelCoeffs (verticalBNTOperatorFamily (D := 8) flagFamily)
      (verticalBNTTraceScalarFamily sectorWeight) where
  positiveChi := twoLabelChiTracePowerForm
  sameLengthProduct := flagOperatorFamily_hasSameLengthProductForm
  idempotent := sectorWeight_hasIdempotentCoefficientForm

/-- **The tensor-attached algebra clause of the twisted quantum dimer.**  The
vertical canonical form with the two flag sectors, multiplicity one each and
weight $\mu = 5/8$, together with the two-label coefficient family
$c^{(L)}_{f f' g} = \alpha^L$ on the channel $g = f + f'$ and $\beta^L$ on the
channel $g = f + f' + 1$, is the algebra clause of arXiv:1606.00608, Theorem
4.14(ii), lines 972--993, for the displayed tensor.  Together with
`twoLabelCoeffs_rescaling_stable_not_lengthIndependent`, the attached
coefficient family is one that no positive rescaling of the two labels makes
length independent.  The tensor is a project example motivated by the
length-dependence question after Theorem 4.14 (lines 995--1010); it is not a
tensor stated in that source. -/
def T_bntAlgebraTensorClause : BNTAlgebraTensorClause T where
  labelCount := 2
  bondDim := sectorDim
  multiplicity := sectorMult
  weight := sectorWeight
  tensor := flagFamily
  verticalCoisometry := verticalCoisometry
  multiplicity_pos _ := Nat.one_pos
  weight_pos _ _ := Complex.zero_lt_real.mpr (by norm_num [mu])
  coisometry := verticalCoisometry_mul_conjTranspose
  isCPSVBNT := flagFamily_isCPSVBasisOfNormalTensors
  forward := verticalCoisometry_conj_verticalTensor
  reconstruction := verticalTensor_T_eq_conjTranspose_mul
  coeffs := twoLabelCoeffs
  algebraClause := flagAlgebraClause

/-- The twisted quantum dimer has a tensor-attached algebra clause. -/
theorem T_hasBNTAlgebraTensorClause : HasBNTAlgebraTensorClause T :=
  ⟨T_bntAlgebraTensorClause⟩

end MPOTensor.TwistedDimer
