/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTCoefficients

/-!
# BNT-label theorem data for MPDO algebra structures

This file records the theorem-data layer for the BNT-label form of
arXiv:1606.00608, Theorem IV.13(ii).  The coefficient,
operator, trace-scalar, chi, and blocked-basis comparison primitives are kept in
the coefficient file; the existential witness is recorded separately.

The declarations here do not yet construct the source objects from an MPDO
tensor.  They collect the objects and consequences that the Appendix C.3--C.4
argument must provide.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.3--C.4
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

/-- The BNT-label data asserted by the source theorem, together with its
blocked-basis comparison.

This record gathers the objects that the remaining Appendix C.3--C.4
construction must produce from an MPDO tensor: the fixed BNT-label coefficient
system, the same-length BNT operator family and product law, the trace scalars
and idempotent condition, the positive length-independent chi witness, and the
comparison with the chosen blocked bases.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelTheoremData (data : AlgebraStructureData d D)
    (Λ : Type*) (O : ℕ → Type*) [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)] where
  /-- The BNT-label coefficient system \(c^{(L)}_{\alpha,\beta,\gamma}\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  coeffs : BNTLabelCoefficientFamily Λ
  /-- The BNT-label operator family \(O_L(M_\alpha)\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  operators : BNTLabelOperatorFamily Λ O
  /-- The trace scalars \(m_\alpha=\operatorname{tr}(\mu_\alpha)\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 981--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  traceScalars : BNTLabelTraceScalarFamily Λ
  /-- The same-length BNT product law.

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  sameLengthProduct : operators.HasSameLengthProductForm coeffs
  /-- The idempotent scalar condition.

  Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  idempotent : traceScalars.HasIdempotentCoefficientForm coeffs
  /-- The positive length-independent BNT-label chi witness.

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
  Appendix C.4, lines 1925--1942 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  positiveChi : PositiveBNTLabelChiTracePowerForm coeffs
  /-- Comparison of the chosen blocked-basis coefficients with the BNT labels.

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
  Appendix C.3, lines 1830--1922 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  blockedComparison : BNTBlockedBasisCoefficientComparison data coeffs

namespace BNTLabelTheoremData

variable {data : AlgebraStructureData d D} {Λ : Type*} {O : ℕ → Type*}
  [Fintype Λ] [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
  [∀ L : ℕ, Mul (O L)] (H : BNTLabelTheoremData data Λ O)

/-- Build BNT-label theorem data in the source-side case where the coefficient
family is canonically determined by the same diagonal
\(\chi_{\alpha,\beta,\gamma}\)-family.

This is the form closest to the Appendix C.4 construction: after the positive
diagonal matrices \(\chi_{\alpha,\beta,\gamma}\) have been produced, the
coefficient system is fixed to
\[
  c^{(L)}_{\alpha,\beta,\gamma}
    = \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L}).
\]
The remaining inputs are precisely the product law, idempotent law, and
blocked-basis comparison for that canonical coefficient family.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def ofChi (χ : DiagonalChiFamily Λ) (hχ : χ.PosEntries)
    (operators : BNTLabelOperatorFamily Λ O)
    (traceScalars : BNTLabelTraceScalarFamily Λ)
    (sameLengthProduct :
      operators.HasSameLengthProductForm (BNTLabelCoefficientFamily.ofChi χ))
    (idempotent :
      traceScalars.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi χ))
    (blockedComparison :
      BNTBlockedBasisCoefficientComparison data (BNTLabelCoefficientFamily.ofChi χ)) :
    BNTLabelTheoremData data Λ O where
  coeffs := BNTLabelCoefficientFamily.ofChi χ
  operators := operators
  traceScalars := traceScalars
  sameLengthProduct := sameLengthProduct
  idempotent := idempotent
  positiveChi := PositiveBNTLabelChiTracePowerForm.ofChi χ hχ
  blockedComparison := blockedComparison

/-- The same-length product predicate carried by BNT-label theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_form :
    H.operators.HasSameLengthProductForm H.coeffs :=
  H.sameLengthProduct

/-- The idempotent coefficient predicate carried by BNT-label theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_coefficient_form :
    H.traceScalars.HasIdempotentCoefficientForm H.coeffs :=
  H.idempotent

/-- Positivity of the BNT-label chi matrices carried by theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positive_chi_pos_entries :
    H.positiveChi.chi.PosEntries :=
  H.positiveChi.posEntries

/-- The positive-length trace-power predicate carried by the BNT-label chi
witness in theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positive_chi_trace_power :
    H.coeffs.HasPositiveLengthChiTracePowerForm H.positiveChi.chi :=
  H.positiveChi.tracePower

/-- The source BNT label attached by theorem data to a chosen basis element of
\(\mathcal A_n\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def sourceLabel (n : ℕ) (hn : 0 < n)
    (i : AlgebraStructureData.BlockedIndex data n) : Λ :=
  H.blockedComparison.sourceLabel n hn i

/-- The target BNT label attached by theorem data to a chosen basis element of
\(\mathcal A_{2n}\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def targetLabel (n : ℕ) (hn : 0 < n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) : Λ :=
  H.blockedComparison.targetLabel n hn k

/-- The BNT-label coefficients in theorem data are traces of powers of the
length-independent chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_trace_pow (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    H.coeffs.coeff L α β γ =
      (H.positiveChi.chi.matrix α β γ ^ L).trace :=
  H.positiveChi.eq_trace_pow L hL α β γ

/-- At every positive length, the coefficient family in theorem data agrees
with the canonical coefficient family determined by its
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

The restriction \(0<L\) is essential: the source theorem only states the
physical positive-length coefficients, and the formal coefficient family is
not constrained at length zero by Theorem IV.13(ii).

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_ofChi_coeff (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    H.coeffs.coeff L α β γ =
      (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi).coeff L α β γ :=
  H.positive_chi_trace_power L hL α β γ

/-- The same-length product law carried by theorem data may be written using
the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_form_ofChi :
    H.operators.HasSameLengthProductForm
      (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi) := by
  intro L hL α β
  rw [BNTLabelOperatorFamily.HasSameLengthProductForm.eq_sum
    (op := H.operators) H.sameLengthProduct L hL α β]
  refine Finset.sum_congr rfl ?_
  intro γ _hγ
  rw [H.coeff_eq_ofChi_coeff L hL α β γ]

/-- The same-length product equation carried by theorem data, written with the
canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum_ofChi
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    H.operators.operator L α * H.operators.operator L β =
      ∑ γ : Λ,
        (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi).coeff L α β γ •
          H.operators.operator L γ :=
  BNTLabelOperatorFamily.HasSameLengthProductForm.eq_sum
    (op := H.operators) H.same_length_product_form_ofChi L hL α β

/-- The idempotent scalar law carried by theorem data may be written using the
canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_coefficient_form_ofChi :
    H.traceScalars.HasIdempotentCoefficientForm
      (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi) := by
  intro γ
  rw [BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm.eq_sum
    (m := H.traceScalars) H.idempotent γ]
  refine Finset.sum_congr rfl ?_
  intro α _hα
  refine Finset.sum_congr rfl ?_
  intro β _hβ
  rw [H.coeff_eq_ofChi_coeff 1 Nat.zero_lt_one α β γ]

/-- The idempotent scalar equation carried by theorem data, written with the
canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum_ofChi (γ : Λ) :
    H.traceScalars.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi).coeff 1 α β γ *
          (H.traceScalars.traceScalar α * H.traceScalars.traceScalar β) :=
  BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm.eq_sum
    (m := H.traceScalars) H.idempotent_coefficient_form_ofChi γ

/-- The diagonal entries of the chi matrices in theorem data are positive.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem chi_entry_pos (α β γ : Λ)
    (k : Fin (H.positiveChi.chi.dim α β γ)) :
    0 < H.positiveChi.chi.entry α β γ k :=
  H.positiveChi.posEntries α β γ k

/-- The same-length BNT product equation carried by theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    H.operators.operator L α * H.operators.operator L β =
      ∑ γ : Λ, H.coeffs.coeff L α β γ • H.operators.operator L γ :=
  BNTLabelOperatorFamily.HasSameLengthProductForm.eq_sum
    (op := H.operators) H.sameLengthProduct L hL α β

/-- The idempotent scalar equation carried by theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum (γ : Λ) :
    H.traceScalars.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        H.coeffs.coeff 1 α β γ *
          (H.traceScalars.traceScalar α * H.traceScalars.traceScalar β) :=
  BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm.eq_sum
    (m := H.traceScalars) H.idempotent γ

/-- The blocked-basis/BNT-label coefficient comparison carried by theorem data.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      H.coeffs.coeff n
        (H.sourceLabel n hn i)
        (H.sourceLabel n hn j)
        (H.targetLabel n hn k) :=
  H.blockedComparison.blocked_coeff_eq n hn i j k

/-- The blocked-basis comparison carried by theorem data may be written using
the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def blockedComparison_ofChi :
    BNTBlockedBasisCoefficientComparison data
      (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi) where
  sourceLabel := H.sourceLabel
  targetLabel := H.targetLabel
  coeff_eq := by
    intro n hn i j k
    rw [H.blocked_coeff_eq n hn i j k]
    exact H.coeff_eq_ofChi_coeff n hn
      (H.sourceLabel n hn i) (H.sourceLabel n hn j) (H.targetLabel n hn k)

/-- The blocked-basis coefficient comparison carried by theorem data, written
with the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_ofChi
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (BNTLabelCoefficientFamily.ofChi H.positiveChi.chi).coeff n
        (H.sourceLabel n hn i)
        (H.sourceLabel n hn j)
        (H.targetLabel n hn k) :=
  H.blockedComparison_ofChi.blocked_coeff_eq n hn i j k

/-- The BNT product expansion with the coefficients written as traces of the
length-independent chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum_chi_trace_pow
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    H.operators.operator L α * H.operators.operator L β =
      ∑ γ : Λ, (H.positiveChi.chi.matrix α β γ ^ L).trace •
        H.operators.operator L γ :=
  H.same_length_product_form_ofChi.eq_sum_ofChi_trace_pow L hL α β

/-- The idempotent scalar identity with length-one coefficients written as
traces of the chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum_chi_trace (γ : Λ) :
    H.traceScalars.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        (H.positiveChi.chi.matrix α β γ).trace *
          (H.traceScalars.traceScalar α * H.traceScalars.traceScalar β) :=
  H.idempotent_coefficient_form_ofChi.eq_sum_ofChi_trace γ

/-- The blocked-basis coefficients obtained from BNT-label theorem data are
traces of powers of the pulled-back BNT-label chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_trace_pow
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (H.positiveChi.chi.matrix
        (H.sourceLabel n hn i)
        (H.sourceLabel n hn j)
        (H.targetLabel n hn k) ^ n).trace :=
  H.blockedComparison_ofChi.blocked_coeff_eq_ofChi_trace_pow n hn i j k

/-- The positive blocked chi witness obtained from the BNT-label theorem data
and the blocked-basis comparison.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def toPositiveBlockedStructureChiTracePowerForm :
    AlgebraStructureData.PositiveBlockedStructureChiTracePowerForm data :=
  H.blockedComparison.toPositiveBlockedStructureChiTracePowerForm H.positiveChi

/-- The blocked-basis chi family obtained by pulling back the uniform
BNT-label chi family in theorem data along the blocked-basis comparison maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def positiveBlockedChi : AlgebraStructureData.BlockedStructureChiFamily data :=
  H.toPositiveBlockedStructureChiTracePowerForm.chi

/-- At positive blocked length, the blocked-basis chi family obtained from
BNT-label theorem data is exactly the BNT-label chi family composed with the
source and target comparison maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_toDiagonal_of_pos
    (n : ℕ) (hn : 0 < n) :
    H.positiveBlockedChi.toDiagonal n =
      H.positiveChi.chi.comap (H.blockedComparison.blockedLabel n hn) :=
  H.blockedComparison.pulledBlockedChiFamily_toDiagonal_of_pos H.positiveChi n hn

/-- At positive blocked length, the finite-sum trace-power coefficient of the
blocked-basis chi family obtained from BNT-label theorem data is the
corresponding BNT-label trace-power coefficient.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_tracePowerCoeff_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    H.positiveBlockedChi.tracePowerCoeff n i j k L =
      H.positiveChi.chi.tracePowerCoeff
        (H.sourceLabel n hn i) (H.sourceLabel n hn j) (H.targetLabel n hn k) L :=
  H.blockedComparison.pulledBlockedChi_tracePowerCoeff_of_pos
    H.positiveChi n hn i j k L

/-- At positive blocked length, the size of the blocked-basis chi matrix obtained
from BNT-label theorem data is the corresponding BNT-label chi-matrix size.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_dim_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    H.positiveBlockedChi.dim n i j k =
      H.positiveChi.chi.dim
        (H.sourceLabel n hn i) (H.sourceLabel n hn j) (H.targetLabel n hn k) :=
  H.blockedComparison.pulledBlockedChi_dim_of_pos H.positiveChi n hn i j k

/-- At positive blocked length, the trace of the `L`-th power of the
blocked-basis chi matrix obtained from BNT-label theorem data is the trace of
the `L`-th power of the corresponding BNT-label chi matrix.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_trace_matrix_pow_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    (H.positiveBlockedChi.matrix n i j k ^ L).trace =
      (H.positiveChi.chi.matrix
        (H.sourceLabel n hn i) (H.sourceLabel n hn j) (H.targetLabel n hn k) ^
          L).trace :=
  H.blockedComparison.pulledBlockedChi_trace_matrix_pow_of_pos
    H.positiveChi n hn i j k L

/-- The pulled-back blocked-basis chi family obtained from BNT-label theorem
data satisfies the blocked trace-power predicate.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_tracePower :
    data.HasBlockedStructureChiTracePowerForm H.positiveBlockedChi :=
  H.toPositiveBlockedStructureChiTracePowerForm.tracePower

/-- The pulled-back blocked-basis chi family obtained from BNT-label theorem
data has positive diagonal entries.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_posEntries :
    H.positiveBlockedChi.PosEntries :=
  H.toPositiveBlockedStructureChiTracePowerForm.posEntries

/-- The pulled-back blocked-basis chi entries obtained from BNT-label theorem
data are positive.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_entry_pos
    (n : ℕ) (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (r : Fin (H.positiveBlockedChi.dim n i j k)) :
    0 < H.positiveBlockedChi.entry n i j k r :=
  H.toPositiveBlockedStructureChiTracePowerForm.posEntries n i j k r

/-- The blocked-basis coefficients obtained from BNT-label theorem data are
traces of powers of the pulled-back blocked-basis chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_positiveBlockedChi_trace_pow
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (H.positiveBlockedChi.matrix n i j k ^ n).trace :=
  H.toPositiveBlockedStructureChiTracePowerForm.eq_trace_pow n hn i j k

end BNTLabelTheoremData

end MPOTensor
