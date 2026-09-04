/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.TwistedDimerProductLaw
import TNLean.MPS.MPDO.TwistedDimerVerticalCF

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

* `flagFamily_isLeftCanonical` — each flag sector is left-canonical;
* `flagFamily_isNormalTensor` — each flag sector is a normal tensor in the
  sense of arXiv:1606.00608, lines 231--235;
* `flagFamily_isCPSVBasisOfNormalTensors` — the flag sectors form the basis of
  normal tensors of the vertically viewed tensor in the source's sense;
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

/-! ### Left-canonical normalization of the flag sectors -/

/-- The letter of a flag sector, multiplied on the left by its adjoint, is a
diagonal matrix unit at the right bits with the squared modulus of the
coefficient. -/
lemma conjTranspose_flagMPO_mul_self (f : Fin 2) (a b : Fin 8) :
    (flagMPO f a b)ᴴ * flagMPO f a b =
      Matrix.single (finProdFinEquiv (bitR a, bitR b)) (finProdFinEquiv (bitR a, bitR b))
        (star (flagCoef f a b) * flagCoef f a b) := by
  simp [flagMPO, unitTensor, Matrix.conjTranspose_single, Matrix.single_mul_single_same]

/-- The squared modulus of the sector coefficient: the flag sign squares to
one, leaving the squared bond-matrix entry over $(2\mu)^2$ when the block
labels agree. -/
lemma star_flagCoef_mul_self (f p p' k q q' k' : Fin 2) :
    star (flagCoef f (physIdx p p' k) (physIdx q q' k')) *
        flagCoef f (physIdx p p' k) (physIdx q q' k') =
      if k = k' then (((Cmat k p p' / (2 * mu)) ^ 2 : ℝ) : ℂ) else 0 := by
  simp only [flagCoef, bitF_physIdx, flagWeight_physIdx]
  split_ifs
  · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    have ht : tau k f * tau k f = 1 := by fin_cases k <;> fin_cases f <;> norm_num [tau]
    calc Cmat k p p' * tau k f / (2 * mu) * (Cmat k p p' * tau k f / (2 * mu))
        = (Cmat k p p' / (2 * mu)) ^ 2 * (tau k f * tau k f) := by ring
      _ = _ := by rw [ht, mul_one]
  · simp

/-- Expanding a double sum over the bond indices along their bit encodings. -/
private lemma sum_bits (F : Fin 8 → Fin 8 → ℂ) :
    (∑ a, ∑ b, F a b) =
      ∑ p, ∑ p', ∑ k, ∑ q, ∑ q', ∑ k', F (physIdx p p' k) (physIdx q q' k') := by
  rw [← physEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [← physEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **The flag sectors are left-canonical.**  The sum over the bond pairs of
the adjoint of a sector letter times the letter is the identity: at each
right-bit pair, the sum of the squared coefficients is
$2 \sum_{k, p} C_k[p, p']^2 / (2\mu)^2 = 4 \cdot \tfrac{25}{64} / \tfrac{100}{64} = 1$.

Project example; not from CPSV16. -/
theorem flagFamily_isLeftCanonical (f : Fin 2) : (flagFamily f).IsLeftCanonical := by
  unfold MPSTensor.IsLeftCanonical Kraus.IsTP
  rw [← (finProdFinEquiv (m := 8) (n := 8)).sum_comp, Fintype.sum_prod_type]
  simp only [flagFamily_finProdFinEquiv, conjTranspose_flagMPO_mul_self]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [and_self, ite_true]
    obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective i
    rw [sum_bits fun a b =>
      if finProdFinEquiv (bitR a, bitR b) = finProdFinEquiv (i₁, i₂) then
        star (flagCoef f a b) * flagCoef f a b else 0]
    simp only [bitR_physIdx, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq,
      star_flagCoef_mul_self]
    fin_cases i₁ <;> fin_cases i₂ <;>
      simp [Fin.sum_univ_two, Cmat, cDiag_eq, cOff_eq, mu] <;> norm_num
  · rw [ite_eq_right hij]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]
    rintro ⟨h₁, h₂⟩
    exact hij (h₁.symm.trans h₂)

/-- **The flag sectors are normal tensors** in the sense of arXiv:1606.00608,
lines 231--235: injective at one site and left-canonical.

Project example; not from CPSV16. -/
theorem flagFamily_isNormalTensor (f : Fin 2) : (flagFamily f).IsNormalTensor :=
  MPSTensor.isNormalTensor_of_isNormal_leftCanonical (flagFamily f) (flagFamily_isNormal f)
    (flagFamily_isLeftCanonical f)

/-- **The flag sectors form the source's basis of normal tensors of the
vertically viewed tensor** (arXiv:1606.00608, Proposition 4.13, lines
945--959).

Project example; not from CPSV16. -/
theorem flagFamily_isCPSVBasisOfNormalTensors :
    MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor T)
      (fun f : Fin 2 => ⟨sectorDim f, flagFamily f⟩) where
  blocks_normal := flagFamily_isNormalTensor
  spans_mpv N hN := ⟨fun _ => ((mu : ℝ) : ℂ) ^ N, mpv_verticalTensor_T hN⟩
  eventually_li := ⟨0, fun N hN => linearIndependent_mpvState_flagFamily N hN⟩

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
