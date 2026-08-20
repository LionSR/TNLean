/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.BNTAssociativity

/-!
# Scale-covariant comparison of vertical BNT coefficients under transport

Bare horizontal periodic equality between two MPO tensors does not determine
the structure coefficients of their tensor-attached vertical BNT algebra
clauses; the explicit counterexample is in
`TNLean/MPS/MPDO/VerticalCoefficientPresentationCounterexample.lean`.  This
file proves the positive replacement statement: once an explicit vertical
transport is assumed between the two per-length operator families, consisting
of a label equivalence \(e\), nonzero scalars \(s_\alpha\), and per-length
algebra isomorphisms \(\Phi_L\) with
\[
  O'_L(\alpha) = s_\alpha^L\,\Phi_L\bigl(O_L(e\alpha)\bigr),
\]
then at every positive length at which the target operators are linearly
independent, uniqueness of the product expansion forces the scale-covariant
comparison law
\[
  {c'}^{(L)}_{\alpha,\beta,\gamma}
    = \Bigl(\frac{s_\alpha s_\beta}{s_\gamma}\Bigr)^{L}
      c^{(L)}_{e\alpha,e\beta,e\gamma}.
\]
Exact coefficient equality after relabelling follows under the additional
normalization condition \(s_\alpha s_\beta = s_\gamma\) on every product
triple with nonvanishing coefficient.  The transport keeps the normalization
scale explicit, exactly as the source comparison retains the positive ratio
\(m_\alpha/n_{\sigma(\alpha)}\) instead of discarding it.

Deriving the transport itself from two literal horizontal canonical
presentations, and extending the comparison to every positive length from
bare horizontal periodic equality, are separate statements not proved here;
the counterexample shows they require more than periodic equality.

## Main results

* `BNTVerticalTransport`: the explicit transport between two BNT-label
  operator families.
* `BNTVerticalTransport.hasSameLengthProductForm_transported`: the target
  family satisfies the same-length product law with the scale-transported
  coefficients.
* `BNTVerticalTransport.coeff_covariance_of_linearIndependentAt`: the
  scale-covariant comparison law at a linearly independent length.
* `BNTVerticalTransport.coeff_eq_of_linearIndependentAt_of_scale_compatible`:
  exact coefficient equality after relabelling under the normalization
  condition.
* `BNTAlgebraTensorClause.coeff_covariance_of_verticalTransport` and
  `BNTAlgebraTensorClause.coeff_eq_of_verticalTransport_of_scale_compatible`:
  the same two conclusions for the coefficient families of two
  tensor-attached vertical BNT algebra clauses.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii), lines 972--985, and the retained scale ratio in
  Appendix C.4, lines 1997--2008
* `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`, equations
  eq:vertical-coefficient-explicit-transport and
  eq:vertical-coefficient-covariance
-/

open scoped BigOperators

namespace MPOTensor

variable {Λ Λ' : Type*} {O O' : ℕ → Type*}

/-- Explicit vertical transport between two BNT-label operator families.

The transport consists of a label equivalence \(e\), nonzero scalars
\(s_\alpha\), and, at each length, a linear equivalence \(\Phi_L\) of the
ambient algebras respecting products, such that for every label \(\alpha\)
and every positive length \(L\),
\[
  O'_L(\alpha) = s_\alpha^L\,\Phi_L\bigl(O_L(e\alpha)\bigr).
\]
This is the hypothesis under which the vertical BNT structure coefficients of
two presentations can be compared; without it the comparison fails, as the
counterexample in
`TNLean/MPS/MPDO/VerticalCoefficientPresentationCounterexample.lean` shows.

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
eq:vertical-coefficient-explicit-transport, following the retained ratio
\(m_\alpha/n_{\sigma(\alpha)}\) in CPSV16, Appendix C.4, arXiv:1606.00608,
lines 1997--2008 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTVerticalTransport
    [∀ L, AddCommMonoid (O L)] [∀ L, Module ℂ (O L)] [∀ L, Mul (O L)]
    [∀ L, AddCommMonoid (O' L)] [∀ L, Module ℂ (O' L)] [∀ L, Mul (O' L)]
    (op : BNTLabelOperatorFamily Λ O) (op' : BNTLabelOperatorFamily Λ' O') where
  /-- The label equivalence \(e\) matching target labels to source labels.

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport. -/
  relabel : Λ' ≃ Λ
  /-- The per-label normalization scale \(s_\alpha\).

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport; the retained ratio in CPSV16,
  Appendix C.4, arXiv:1606.00608, lines 1997--2008. -/
  scale : Λ' → ℂ
  /-- Every normalization scale is nonzero.

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport. -/
  scale_ne_zero : ∀ α : Λ', scale α ≠ 0
  /-- The length-\(L\) algebra isomorphism \(\Phi_L\), as a linear
  equivalence of the ambient algebras.

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport. -/
  map : ∀ L : ℕ, O L ≃ₗ[ℂ] O' L
  /-- Each \(\Phi_L\) respects products, so it is an isomorphism of
  algebras.

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport. -/
  map_mul : ∀ (L : ℕ) (x y : O L), map L (x * y) = map L x * map L y
  /-- The transport relation
  \(O'_L(\alpha) = s_\alpha^L\,\Phi_L(O_L(e\alpha))\) at every positive
  length.

  Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
  eq:vertical-coefficient-explicit-transport. -/
  transport : ∀ L : ℕ, 0 < L → ∀ α : Λ',
    op'.operator L α = scale α ^ L • map L (op.operator L (relabel α))

namespace BNTVerticalTransport

variable [∀ L, AddCommMonoid (O L)] [∀ L, Module ℂ (O L)] [∀ L, Mul (O L)]
  {op : BNTLabelOperatorFamily Λ O}

section Transported

variable [∀ L, AddCommMonoid (O' L)] [∀ L, Module ℂ (O' L)] [∀ L, Mul (O' L)]
  {op' : BNTLabelOperatorFamily Λ' O'}

/-- The coefficient family obtained by transporting
\(c^{(L)}_{\alpha,\beta,\gamma}\) along a vertical transport: relabel the
three indices and multiply by the scale ratio,
\[
  \Bigl(\frac{s_\alpha s_\beta}{s_\gamma}\Bigr)^{L}
    c^{(L)}_{e\alpha,e\beta,e\gamma}.
\]
Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
eq:vertical-coefficient-covariance. -/
noncomputable def transportedCoefficients (T : BNTVerticalTransport op op')
    (c : BNTLabelCoefficientFamily Λ) : BNTLabelCoefficientFamily Λ' where
  coeff L α β γ := (T.scale α * T.scale β / T.scale γ) ^ L *
    c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ)

@[simp]
theorem transportedCoefficients_coeff (T : BNTVerticalTransport op op')
    (c : BNTLabelCoefficientFamily Λ) (L : ℕ) (α β γ : Λ') :
    (T.transportedCoefficients c).coeff L α β γ =
      (T.scale α * T.scale β / T.scale γ) ^ L *
        c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) :=
  rfl

end Transported

variable [Fintype Λ] [Fintype Λ']
  [∀ L, NonUnitalRing (O' L)] [∀ L, Module ℂ (O' L)]
  [∀ L, SMulCommClass ℂ (O' L) (O' L)] [∀ L, IsScalarTower ℂ (O' L) (O' L)]
  {op' : BNTLabelOperatorFamily Λ' O'}

/-- Transporting the same-length product law: if the source family expands
products with coefficients \(c^{(L)}_{\alpha,\beta,\gamma}\), the target
family of a vertical transport expands products with the transported
coefficients
\(\bigl(s_\alpha s_\beta/s_\gamma\bigr)^{L}
c^{(L)}_{e\alpha,e\beta,e\gamma}\).

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
eq:vertical-coefficient-covariance, applying \(\Phi_L\) to the product law of
arXiv:1606.00608, Theorem 4.14(ii), eq:algebra, lines 972--985. -/
theorem hasSameLengthProductForm_transported
    (T : BNTVerticalTransport op op') {c : BNTLabelCoefficientFamily Λ}
    (h : op.HasSameLengthProductForm c) :
    op'.HasSameLengthProductForm (T.transportedCoefficients c) := by
  intro L hL α β
  calc op'.operator L α * op'.operator L β
      = (T.scale α ^ L • T.map L (op.operator L (T.relabel α))) *
          (T.scale β ^ L • T.map L (op.operator L (T.relabel β))) := by
        rw [T.transport L hL α, T.transport L hL β]
    _ = (T.scale α * T.scale β) ^ L •
          T.map L (op.operator L (T.relabel α) * op.operator L (T.relabel β)) := by
        rw [smul_mul_smul_comm, ← T.map_mul, mul_pow]
    _ = ∑ δ : Λ,
          ((T.scale α * T.scale β) ^ L *
            c.coeff L (T.relabel α) (T.relabel β) δ) •
            T.map L (op.operator L δ) := by
        rw [h L hL, map_sum, Finset.smul_sum]
        simp_rw [map_smul, smul_smul]
    _ = ∑ γ : Λ',
          ((T.scale α * T.scale β) ^ L *
            c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ)) •
            T.map L (op.operator L (T.relabel γ)) :=
        (Equiv.sum_comp T.relabel fun δ ↦
          ((T.scale α * T.scale β) ^ L *
            c.coeff L (T.relabel α) (T.relabel β) δ) •
            T.map L (op.operator L δ)).symm
    _ = ∑ γ : Λ',
          (T.transportedCoefficients c).coeff L α β γ • op'.operator L γ := by
        refine Finset.sum_congr rfl fun γ _ ↦ ?_
        have hΦ : T.map L (op.operator L (T.relabel γ)) =
            (T.scale γ ^ L)⁻¹ • op'.operator L γ := by
          rw [T.transport L hL γ,
            inv_smul_smul₀ (pow_ne_zero L (T.scale_ne_zero γ))]
        rw [hΦ, smul_smul, transportedCoefficients_coeff, div_pow,
          div_eq_mul_inv]
        ring_nf

/-- **Scale covariance of the vertical BNT structure coefficients.**  Under
an explicit vertical transport, at every positive length at which the target
operators are linearly independent, uniqueness of the product expansion
forces
\[
  {c'}^{(L)}_{\alpha,\beta,\gamma}
    = \Bigl(\frac{s_\alpha s_\beta}{s_\gamma}\Bigr)^{L}
      c^{(L)}_{e\alpha,e\beta,e\gamma}.
\]
This is the positive counterpart of the counterexample in
`TNLean/MPS/MPDO/VerticalCoefficientPresentationCounterexample.lean`: the
comparison holds with the normalization scale kept explicit, not with the
scale discarded.

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
eq:vertical-coefficient-covariance, following the retained ratio
\(m_\alpha/n_{\sigma(\alpha)}\) in CPSV16, Appendix C.4, arXiv:1606.00608,
lines 1997--2008 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_covariance_of_linearIndependentAt
    (T : BNTVerticalTransport op op')
    {c : BNTLabelCoefficientFamily Λ} {c' : BNTLabelCoefficientFamily Λ'}
    (h : op.HasSameLengthProductForm c)
    (h' : op'.HasSameLengthProductForm c')
    {L : ℕ} (hL : 0 < L) (hli : op'.LinearIndependentAt L) (α β γ : Λ') :
    c'.coeff L α β γ =
      (T.scale α * T.scale β / T.scale γ) ^ L *
        c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) :=
  BNTLabelOperatorFamily.HasSameLengthProductForm.coeff_eq_of_linearIndependentAt
    h' (T.hasSameLengthProductForm_transported h) hL hli α β γ

/-- **Exact coefficient equality after relabelling.**  Under an explicit
vertical transport whose scales satisfy the normalization condition
\(s_\alpha s_\beta = s_\gamma\) on every product triple with nonvanishing
source coefficient, the scale ratio in the covariance law is one, and the
structure coefficients agree after relabelling at every positive linearly
independent length.

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`, the
normalization condition following eq:vertical-coefficient-covariance. -/
theorem coeff_eq_of_linearIndependentAt_of_scale_compatible
    (T : BNTVerticalTransport op op')
    {c : BNTLabelCoefficientFamily Λ} {c' : BNTLabelCoefficientFamily Λ'}
    (h : op.HasSameLengthProductForm c)
    (h' : op'.HasSameLengthProductForm c')
    {L : ℕ} (hL : 0 < L) (hli : op'.LinearIndependentAt L)
    (hs : ∀ α β γ : Λ',
      c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) ≠ 0 →
        T.scale α * T.scale β = T.scale γ)
    (α β γ : Λ') :
    c'.coeff L α β γ =
      c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) := by
  rw [T.coeff_covariance_of_linearIndependentAt h h' hL hli α β γ]
  by_cases hc : c.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) = 0
  · rw [hc, mul_zero]
  · rw [hs α β γ hc, div_self (T.scale_ne_zero γ), one_pow, one_mul]

end BNTVerticalTransport

namespace BNTAlgebraTensorClause

variable {d D d' D' : ℕ} {M : MPOTensor d D} {M' : MPOTensor d' D'}

/-- Scale covariance for the coefficient families of two tensor-attached
vertical BNT algebra clauses: an explicit vertical transport between their
operator families forces
\[
  {c'}^{(L)}_{\alpha,\beta,\gamma}
    = \Bigl(\frac{s_\alpha s_\beta}{s_\gamma}\Bigr)^{L}
      c^{(L)}_{e\alpha,e\beta,e\gamma}
\]
at every positive length at which the target operators are linearly
independent.

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`,
eq:vertical-coefficient-covariance, for the algebra clauses of
arXiv:1606.00608, Theorem 4.14(ii), lines 972--985. -/
theorem coeff_covariance_of_verticalTransport
    (H : BNTAlgebraTensorClause M) (H' : BNTAlgebraTensorClause M')
    (T : BNTVerticalTransport H.operators H'.operators)
    {L : ℕ} (hL : 0 < L) (hli : H'.operators.LinearIndependentAt L)
    (α β γ : Fin H'.labelCount) :
    H'.coeffs.coeff L α β γ =
      (T.scale α * T.scale β / T.scale γ) ^ L *
        H.coeffs.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) :=
  T.coeff_covariance_of_linearIndependentAt
    H.algebraClause.sameLengthProduct H'.algebraClause.sameLengthProduct
    hL hli α β γ

/-- Exact equality after relabelling for the coefficient families of two
tensor-attached vertical BNT algebra clauses, under an explicit vertical
transport whose scales satisfy \(s_\alpha s_\beta = s_\gamma\) on every
product triple with nonvanishing source coefficient.

Source: `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`, the
normalization condition following eq:vertical-coefficient-covariance. -/
theorem coeff_eq_of_verticalTransport_of_scale_compatible
    (H : BNTAlgebraTensorClause M) (H' : BNTAlgebraTensorClause M')
    (T : BNTVerticalTransport H.operators H'.operators)
    {L : ℕ} (hL : 0 < L) (hli : H'.operators.LinearIndependentAt L)
    (hs : ∀ α β γ : Fin H'.labelCount,
      H.coeffs.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) ≠ 0 →
        T.scale α * T.scale β = T.scale γ)
    (α β γ : Fin H'.labelCount) :
    H'.coeffs.coeff L α β γ =
      H.coeffs.coeff L (T.relabel α) (T.relabel β) (T.relabel γ) :=
  T.coeff_eq_of_linearIndependentAt_of_scale_compatible
    H.algebraClause.sameLengthProduct H'.algebraClause.sameLengthProduct
    hL hli hs α β γ

end BNTAlgebraTensorClause

end MPOTensor
