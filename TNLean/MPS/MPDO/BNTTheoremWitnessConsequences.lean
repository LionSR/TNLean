/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTheoremWitness

/-!
# Proposition-level consequences of BNT-label theorem witnesses

This file records consequences of the existential BNT-label witness for
arXiv:1606.00608, Theorem IV.13(ii).  These declarations unpack a witness into
the source equations, the positive \(\chi\)-coefficient form, and the
blocked-basis comparison consequences.

The declarations here do not construct the witness from an MPDO tensor; that
remains the Appendix C.3--C.4 obligation.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.3--C.4
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

namespace HasBNTLabelTheoremWitness

/-- Existence of the source BNT-label witness gives a concrete witness carrying
the source predicates of Theorem IV.13(ii): the same-length product law, the
idempotent scalar law, the positive-length trace-power law, and positivity of
the diagonal \(\chi_{\alpha,\beta,\gamma}\)-entries.

This only unpacks the existential witness; it does not construct that witness
from an MPDO tensor.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_source_predicates {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      W.operators.HasSameLengthProductForm W.coeffs ∧
        W.traceScalars.HasIdempotentCoefficientForm W.coeffs ∧
        W.coeffs.HasPositiveLengthChiTracePowerForm W.positiveChi.chi ∧
        W.positiveChi.chi.PosEntries := by
  rcases h with ⟨W⟩
  exact ⟨W, W.same_length_product_form, W.idempotent_coefficient_form,
    W.positive_chi_trace_power, W.positive_chi_pos_entries⟩

/-- Existence of the source BNT-label witness gives a concrete witness whose
positive-length coefficients agree with the canonical coefficient family
determined by its \(\chi_{\alpha,\beta,\gamma}\)-matrices.

This statement deliberately keeps the positive-length hypothesis.  Theorem
IV.13(ii) does not constrain the artificial length-zero value of the formal
coefficient family.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_positive_length_coeff_eq_ofChi {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      ∀ L : ℕ, 0 < L → ∀ α β γ : W.Label,
        W.coeffs.coeff L α β γ =
          (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi).coeff L α β γ := by
  rcases h with ⟨W⟩
  refine ⟨W, ?_⟩
  intro L hL α β γ
  exact W.coeff_eq_ofChi_coeff L hL α β γ

/-- Existence of the source BNT-label witness gives a concrete witness whose
source product and idempotent laws are written with the canonical coefficient
family determined by its \(\chi_{\alpha,\beta,\gamma}\)-matrices.

This only rephrases the positive-length coefficient identity carried by the
witness; it does not construct the witness from an MPDO tensor.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_source_ofChi_predicates {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      W.operators.HasSameLengthProductForm
        (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi) ∧
      W.traceScalars.HasIdempotentCoefficientForm
        (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi) := by
  rcases h with ⟨W⟩
  exact ⟨W, W.same_length_product_form_ofChi, W.idempotent_coefficient_form_ofChi⟩

/-- Existence of the source BNT-label witness gives a concrete witness whose
blocked-basis \(\chi\)-family is the pullback of the BNT-label
\(\chi_{\alpha,\beta,\gamma}\)-family along the blocked-basis comparison maps.

This only unpacks the existential witness; constructing such a witness from an
MPDO tensor remains the Appendix C.3--C.4 obligation.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_blocked_chi_pullback {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      ∀ (n : ℕ) (hn : 0 < n),
        W.positiveBlockedChi.toDiagonal n =
          W.positiveChi.chi.comap (W.blockedComparison.blockedLabel n hn) := by
  rcases h with ⟨W⟩
  refine ⟨W, ?_⟩
  intro n hn
  exact W.positiveBlockedChi_toDiagonal_of_pos n hn

/-- Existence of the source BNT-label witness gives the blocked-basis
comparison equation before the \(\chi\)-trace formula is substituted.

This is the proposition-level form of the comparison between the chosen
blocked-basis multiplication coefficients and the BNT-label coefficients:
\[
  c^{(n)}_{i,j,k}
    =
  c^{(n)}_{\sigma_n(i),\sigma_n(j),\tau_n(k)}.
\]
It only unpacks the existential witness; constructing such a witness from an
MPDO tensor remains the Appendix C.3--C.4 obligation.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_blocked_coefficient_comparison {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      ∀ (n : ℕ) (hn : 0 < n)
        (i j : AlgebraStructureData.BlockedIndex data n)
        (k : AlgebraStructureData.BlockedIndex data (2 * n)),
        data.blockedStructureCoefficients n i j k =
          W.coeffs.coeff n
            (W.sourceLabel n hn i)
            (W.sourceLabel n hn j)
            (W.targetLabel n hn k) := by
  rcases h with ⟨W⟩
  refine ⟨W, ?_⟩
  intro n hn i j k
  exact W.blocked_coeff_eq n hn i j k

/-- Existence of the source BNT-label witness gives the two source equations
written with the BNT-label coefficients \(c^{(L)}_{\alpha,\beta,\gamma}\).

This is the proposition-level form of the product equation
\[
  O_L(M_\alpha)O_L(M_\beta)
    = \sum_\gamma c^{(L)}_{\alpha,\beta,\gamma}O_L(M_\gamma)
\]
for positive \(L\), together with the idempotent equation
\[
  m_\gamma =
    \sum_{\alpha,\beta} c^{(1)}_{\alpha,\beta,\gamma}m_\alpha m_\beta.
\]
It only unpacks the existential witness; constructing such a witness from an
MPDO tensor remains the Appendix C.3--C.4 obligation.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_source_coefficient_equations {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      (∀ L : ℕ, 0 < L → ∀ α β : W.Label,
        W.operators.operator L α * W.operators.operator L β =
          ∑ γ : W.Label, W.coeffs.coeff L α β γ • W.operators.operator L γ) ∧
      (∀ γ : W.Label,
        W.traceScalars.traceScalar γ =
          ∑ α : W.Label, ∑ β : W.Label,
            W.coeffs.coeff 1 α β γ *
              (W.traceScalars.traceScalar α * W.traceScalars.traceScalar β)) := by
  rcases h with ⟨W⟩
  refine ⟨W, ?_, ?_⟩
  · intro L hL α β
    exact W.same_length_product_eq_sum L hL α β
  · intro γ
    exact W.idempotent_eq_sum γ

/-- Existence of the source BNT-label witness gives the two source equations
with the coefficients written as traces of the corresponding
\(\chi_{\alpha,\beta,\gamma}\)-powers.

This is the proposition-level form of Theorem IV.13(ii)'s equation
\[
  O_L(M_\alpha)O_L(M_\beta)
    = \sum_\gamma
      \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L})O_L(M_\gamma)
\]
for positive \(L\), together with the length-one idempotent equation
\[
  m_\gamma =
    \sum_{\alpha,\beta}
      \operatorname{tr}(\chi_{\alpha,\beta,\gamma})m_\alpha m_\beta.
\]
It only unpacks the existential witness; constructing such a witness from an
MPDO tensor remains the Appendix C.3--C.4 obligation.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_source_chi_trace_equations {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ W : BNTLabelTheoremWitness data,
      (∀ L : ℕ, 0 < L → ∀ α β : W.Label,
        W.operators.operator L α * W.operators.operator L β =
          ∑ γ : W.Label, (W.positiveChi.chi.matrix α β γ ^ L).trace •
            W.operators.operator L γ) ∧
      (∀ γ : W.Label,
        W.traceScalars.traceScalar γ =
          ∑ α : W.Label, ∑ β : W.Label,
            (W.positiveChi.chi.matrix α β γ).trace *
              (W.traceScalars.traceScalar α * W.traceScalars.traceScalar β)) := by
  rcases h with ⟨W⟩
  refine ⟨W, ?_, ?_⟩
  · intro L hL α β
    exact W.same_length_product_eq_sum_chi_trace_pow L hL α β
  · intro γ
    exact W.idempotent_eq_sum_chi_trace γ

end HasBNTLabelTheoremWitness

end MPOTensor
