/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTCoefficients

/-!
# Associativity constraints on BNT-label structure coefficients

The discussion following Theorem IV.13 of arXiv:1606.00608 (lines 997--999)
notes that the associativity of the multiplication in the same-length product
law imposes restrictions on the family of diagonal matrices
$\chi_{\alpha,\beta,\gamma}$: expanding the two associations of a triple
product and comparing coefficients yields
\[
  \sum_\delta c^{(L)}_{\alpha,\beta,\delta}\, c^{(L)}_{\delta,\gamma,\epsilon}
    = \sum_\delta c^{(L)}_{\beta,\gamma,\delta}\,
        c^{(L)}_{\alpha,\delta,\epsilon}.
\]
The comparison of coefficients requires the linear independence of the
labelled operators, which the source provides through the defining property
of a basis of normal tensors (lines 271--275: the generated family is
linearly independent for all lengths beyond some threshold) and invokes at
the operator level in Appendix C.4 (line 2058).

This file records the linear-independence predicates for a BNT-label
operator family, the uniqueness of the structure coefficients at a linearly
independent length, and the associativity constraint, together with its
trace-power form. In the source these restrictions, combined with the
isometry statement of Theorem IV.13(iii), lead to a pentagon-like equation
for the fusion isometries whose solutions come from unitary fusion
categories; that development belongs to the boundary-theory program and is
not formalized here.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 271--275, 976--999, and Appendix C.4, lines 2046--2065
-/

open scoped BigOperators

namespace MPOTensor

namespace BNTLabelOperatorFamily

variable {Λ : Type*} {O : ℕ → Type*}

/-- Linear independence of the length-`L` operators of a BNT-label operator
family.

Source: arXiv:1606.00608, Appendix C.4, line 2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex` (the operators of a basis of normal
tensors are linearly independent for sufficiently large lengths). -/
def LinearIndependentAt (op : BNTLabelOperatorFamily Λ O) (L : ℕ)
    [AddCommMonoid (O L)] [Module ℂ (O L)] : Prop :=
  LinearIndependent ℂ (op.operator L)

/-- Eventual linear independence of the operators of a BNT-label operator
family: beyond some threshold length, the operators are linearly
independent. This is the operator-level form of the third defining property
of a basis of normal tensors.

Source: arXiv:1606.00608, lines 271--275 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def EventuallyLinearIndependent (op : BNTLabelOperatorFamily Λ O)
    [∀ L, AddCommMonoid (O L)] [∀ L, Module ℂ (O L)] : Prop :=
  ∃ N₀ : ℕ, ∀ L : ℕ, N₀ < L → op.LinearIndependentAt L

variable [Fintype Λ]

/-- **Uniqueness of the structure coefficients** at a linearly independent
length: two coefficient systems satisfying the same-length product law for
the same operator family agree wherever the operators are linearly
independent.

Source: arXiv:1606.00608, Appendix C.4, lines 2046--2065 of
`Papers/1606.00608/MPDO-22-12-17-2.tex` (coefficient comparison under the
linear independence of the operators). -/
theorem HasSameLengthProductForm.coeff_eq_of_linearIndependentAt
    [∀ L, AddCommGroup (O L)] [∀ L, Module ℂ (O L)] [∀ L, Mul (O L)]
    {op : BNTLabelOperatorFamily Λ O} {c c' : BNTLabelCoefficientFamily Λ}
    (h : op.HasSameLengthProductForm c) (h' : op.HasSameLengthProductForm c')
    {L : ℕ} (hL : 0 < L) (hli : op.LinearIndependentAt L) (α β γ : Λ) :
    c.coeff L α β γ = c'.coeff L α β γ := by
  have hsum : ∑ δ, c.coeff L α β δ • op.operator L δ
      = ∑ δ, c'.coeff L α β δ • op.operator L δ := by
    rw [← h L hL α β, ← h' L hL α β]
  have hzero : ∑ δ, (c.coeff L α β δ - c'.coeff L α β δ) • op.operator L δ
      = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hdiff := Fintype.linearIndependent_iff.mp hli
    (fun δ => c.coeff L α β δ - c'.coeff L α β δ) hzero γ
  exact sub_eq_zero.mp hdiff

/-- **Associativity constraint on the structure coefficients**: expanding
the two associations of a triple product through the same-length product law
and comparing coefficients at a linearly independent length gives
\[
  \sum_\delta c^{(L)}_{\alpha,\beta,\delta}\, c^{(L)}_{\delta,\gamma,\epsilon}
    = \sum_\delta c^{(L)}_{\beta,\gamma,\delta}\,
        c^{(L)}_{\alpha,\delta,\epsilon}.
\]

Source: arXiv:1606.00608, lines 997--999 of
`Papers/1606.00608/MPDO-22-12-17-2.tex` (the associativity of the
multiplication imposes restrictions on the structure coefficients). -/
theorem HasSameLengthProductForm.coeff_assoc_of_linearIndependentAt
    [∀ L, NonUnitalRing (O L)] [∀ L, Module ℂ (O L)]
    [∀ L, SMulCommClass ℂ (O L) (O L)] [∀ L, IsScalarTower ℂ (O L) (O L)]
    {op : BNTLabelOperatorFamily Λ O} {c : BNTLabelCoefficientFamily Λ}
    (h : op.HasSameLengthProductForm c)
    {L : ℕ} (hL : 0 < L) (hli : op.LinearIndependentAt L) (α β γ ε : Λ) :
    ∑ δ, c.coeff L α β δ * c.coeff L δ γ ε
      = ∑ δ, c.coeff L β γ δ * c.coeff L α δ ε := by
  have hexp1 : (op.operator L α * op.operator L β) * op.operator L γ
      = ∑ ε', (∑ δ, c.coeff L α β δ * c.coeff L δ γ ε') •
          op.operator L ε' := by
    rw [h L hL α β, Finset.sum_mul]
    simp_rw [smul_mul_assoc, h L hL, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have hexp2 : op.operator L α * (op.operator L β * op.operator L γ)
      = ∑ ε', (∑ δ, c.coeff L β γ δ * c.coeff L α δ ε') •
          op.operator L ε' := by
    rw [h L hL β γ, Finset.mul_sum]
    simp_rw [mul_smul_comm, h L hL, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have hsum :
      ∑ ε', (∑ δ, c.coeff L α β δ * c.coeff L δ γ ε') • op.operator L ε'
        = ∑ ε', (∑ δ, c.coeff L β γ δ * c.coeff L α δ ε') •
            op.operator L ε' := by
    rw [← hexp1, ← hexp2, mul_assoc]
  have hzero : ∑ ε', ((∑ δ, c.coeff L α β δ * c.coeff L δ γ ε')
      - (∑ δ, c.coeff L β γ δ * c.coeff L α δ ε')) • op.operator L ε' = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hdiff := Fintype.linearIndependent_iff.mp hli
    (fun ε' => (∑ δ, c.coeff L α β δ * c.coeff L δ γ ε')
      - (∑ δ, c.coeff L β γ δ * c.coeff L α δ ε')) hzero ε
  exact sub_eq_zero.mp hdiff

/-- Trace-power form of the associativity constraint: for a coefficient
system in trace-power form, the restriction of the preceding theorem is a
constraint on the diagonal matrices $\chi_{\alpha,\beta,\gamma}$,
\[
  \sum_\delta
    \operatorname{tr}(\chi_{\alpha,\beta,\delta}^{L})
    \operatorname{tr}(\chi_{\delta,\gamma,\epsilon}^{L})
  = \sum_\delta
    \operatorname{tr}(\chi_{\beta,\gamma,\delta}^{L})
    \operatorname{tr}(\chi_{\alpha,\delta,\epsilon}^{L}).
\]

Source: arXiv:1606.00608, lines 997--999 of
`Papers/1606.00608/MPDO-22-12-17-2.tex` (the restrictions imposed on the
family of diagonal matrices by associativity). -/
theorem HasSameLengthProductForm.tracePowerCoeff_assoc_of_linearIndependentAt
    [∀ L, NonUnitalRing (O L)] [∀ L, Module ℂ (O L)]
    [∀ L, SMulCommClass ℂ (O L) (O L)] [∀ L, IsScalarTower ℂ (O L) (O L)]
    {op : BNTLabelOperatorFamily Λ O} {c : BNTLabelCoefficientFamily Λ}
    {χ : DiagonalChiFamily Λ}
    (h : op.HasSameLengthProductForm c)
    (htp : c.HasPositiveLengthChiTracePowerForm χ)
    {L : ℕ} (hL : 0 < L) (hli : op.LinearIndependentAt L) (α β γ ε : Λ) :
    ∑ δ, χ.tracePowerCoeff α β δ L * χ.tracePowerCoeff δ γ ε L
      = ∑ δ, χ.tracePowerCoeff β γ δ L * χ.tracePowerCoeff α δ ε L := by
  have hassoc := h.coeff_assoc_of_linearIndependentAt hL hli α β γ ε
  simp_rw [htp L hL] at hassoc
  exact hassoc

end BNTLabelOperatorFamily

end MPOTensor
