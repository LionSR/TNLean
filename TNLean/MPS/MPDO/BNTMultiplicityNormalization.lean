/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTheoremData

/-!
# Multiplicity normalization in the BNT algebra-to-RFP implication

This file isolates the scalar normalization step in the implication from the
BNT algebra clause to the renormalization fixed-point channels.  After the
one-site and two-site vertical canonical decompositions have been compared,
the two-site multiplicity entries in sector γ are, with multiplicity, the
products of two one-site entries and the corresponding diagonal chi entry.
The length-one idempotent law then identifies the trace of the two-site
multiplicity matrix with the one-site trace scalar for γ.

The comparison of the two vertical canonical decompositions and the
construction of the trace-preserving completely positive maps remain separate
obligations.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.4, lines 2048--2085
-/

open scoped BigOperators

namespace MPOTensor

/-- Indices of the products of one-site multiplicity entries and a chi entry
which contribute to a fixed two-site sector γ.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2063 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
abbrev BNTProductMultiplicityIndex {Λ : Type*} [Fintype Λ]
    (χ : DiagonalChiFamily Λ) (oneDim : Λ → ℕ) (γ : Λ) :=
  Σ α : Λ, Σ β : Λ,
    Fin (oneDim α) × Fin (oneDim β) × Fin (χ.dim α β γ)

/-- The multiplicity-spectrum comparison used in the algebra-to-RFP direction
of Theorem IV.13.

The one-site entries are the diagonal entries of the multiplicity matrix for
α; the two-site entries are those of the multiplicity matrix for γ.  The final
field records the multiset identity obtained in the source from the comparison
of the two vertical BNT decompositions and the positive power-sum lemma.

This structure does not assert that an arbitrary algebra structure supplies
the comparison.  Constructing it from the canonical-form MPDO tensor is the
preceding obligation in Appendix C.4.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTMultiplicitySpectrumComparison {Λ : Type*} [Fintype Λ]
    (χ : DiagonalChiFamily Λ) (m : BNTLabelTraceScalarFamily Λ) where
  /-- Size of the one-site multiplicity matrix for α. -/
  oneDim : Λ → ℕ
  /-- Diagonal entries of the one-site multiplicity matrix for α. -/
  oneEntry : ∀ α : Λ, Fin (oneDim α) → ℂ
  /-- The trace of the one-site multiplicity matrix for α is its trace scalar. -/
  oneTrace : ∀ α : Λ, ∑ i, oneEntry α i = m.traceScalar α
  /-- Size of the two-site multiplicity matrix for γ. -/
  twoDim : Λ → ℕ
  /-- Diagonal entries of the two-site multiplicity matrix for γ. -/
  twoEntry : ∀ γ : Λ, Fin (twoDim γ) → ℂ
  /-- Sectorwise equality, with multiplicity, of the two-site spectrum and
  the products of the one-site and chi entries. -/
  spectrum_eq : ∀ γ : Λ,
    Finset.univ.val.map (twoEntry γ) =
      Finset.univ.val.map fun x : BNTProductMultiplicityIndex χ oneDim γ =>
        oneEntry x.1 x.2.2.1 * oneEntry x.2.1 x.2.2.2.1 *
          χ.entry x.1 x.2.1 γ x.2.2.2.2

namespace BNTMultiplicitySpectrumComparison

variable {Λ : Type*} [Fintype Λ] {χ : DiagonalChiFamily Λ}
  {m : BNTLabelTraceScalarFamily Λ}
  (C : BNTMultiplicitySpectrumComparison χ m)

/-- Summing the sectorwise multiplicity-spectrum comparison gives the
corresponding equality of traces.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2063 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem sum_twoEntry_eq_sum_products (γ : Λ) :
    ∑ r, C.twoEntry γ r =
      ∑ x : BNTProductMultiplicityIndex χ C.oneDim γ,
        C.oneEntry x.1 x.2.2.1 * C.oneEntry x.2.1 x.2.2.2.1 *
          χ.entry x.1 x.2.1 γ x.2.2.2.2 :=
  congrArg Multiset.sum (C.spectrum_eq γ)

/-- The product multiplicity sum factors into the one-site traces and the
length-one chi coefficient.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2063 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem sum_products_eq (γ : Λ) :
    (∑ x : BNTProductMultiplicityIndex χ C.oneDim γ,
        C.oneEntry x.1 x.2.2.1 * C.oneEntry x.2.1 x.2.2.2.1 *
          χ.entry x.1 x.2.1 γ x.2.2.2.2) =
      ∑ α : Λ, ∑ β : Λ,
        χ.tracePowerCoeff α β γ 1 *
          (m.traceScalar α * m.traceScalar β) := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type,
    DiagonalChiFamily.tracePowerCoeff, pow_one]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  calc
    (∑ i, ∑ j, ∑ k,
        C.oneEntry α i * C.oneEntry β j * χ.entry α β γ k) =
        ∑ i, ∑ j, (C.oneEntry α i * C.oneEntry β j) *
          ∑ k, χ.entry α β γ k := by
      simp only [Finset.mul_sum, mul_assoc]
    _ =
        (∑ i, C.oneEntry α i) *
          ((∑ j, C.oneEntry β j) * ∑ k, χ.entry α β γ k) := by
      rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
      simp only [Finset.mul_sum, mul_assoc]
    _ = (∑ i, C.oneEntry α i) * (∑ j, C.oneEntry β j) *
          ∑ k, χ.entry α β γ k := by
      ring
    _ = (∑ k, χ.entry α β γ k) *
          (m.traceScalar α * m.traceScalar β) := by
      rw [C.oneTrace, C.oneTrace]
      ring

/-- The idempotent algebra law identifies the trace of every two-site
multiplicity matrix with the corresponding one-site trace scalar.

This is the scalar conclusion required before the source defines the
preparation map by dividing the two-site multiplicity matrix by this scalar.
No channel or renormalization fixed-point conclusion is asserted here.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 1933--1942, and
Appendix C.4, lines 2058--2064 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem twoTrace_eq_traceScalar
    (hIdempotent :
      m.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi χ))
    (γ : Λ) :
    ∑ r, C.twoEntry γ r = m.traceScalar γ := by
  rw [C.sum_twoEntry_eq_sum_products, C.sum_products_eq]
  symm
  exact hIdempotent γ

end BNTMultiplicitySpectrumComparison

namespace BNTAlgebraClause

variable {Λ : Type*} [Fintype Λ] {O : ℕ → Type*}
  [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
  [∀ L : ℕ, Mul (O L)]
  {c : BNTLabelCoefficientFamily Λ} {operators : BNTLabelOperatorFamily Λ O}
  {m : BNTLabelTraceScalarFamily Λ}
  (H : BNTAlgebraClause c operators m)

/-- A BNT algebra clause, together with the multiplicity-spectrum comparison
of the one-site and two-site vertical canonical decompositions, identifies the
two-site multiplicity trace with the corresponding one-site trace scalar.

This is the first load-bearing conclusion in the algebra-to-RFP implication:
it makes the quotient of the two-site multiplicity matrix by that scalar a
trace-one matrix once positivity and nonzero sector weights have been supplied
by the canonical decomposition.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 1933--1942, and
Appendix C.4, lines 2048--2064 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem twoMultiplicityTrace_eq_traceScalar
    (C : BNTMultiplicitySpectrumComparison H.positiveChi.chi m) (γ : Λ) :
    ∑ r, C.twoEntry γ r = m.traceScalar γ :=
  C.twoTrace_eq_traceScalar H.idempotent_coefficient_form_ofChi γ

end BNTAlgebraClause

end MPOTensor
