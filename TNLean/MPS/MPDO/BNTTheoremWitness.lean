/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTTheoremData

/-!
# BNT-label theorem witnesses for MPDO algebra structures

This file records the existential-witness layer for the BNT-label form of
arXiv:1606.00608, Theorem IV.13(ii).  The theorem-data record is kept separate
from the coefficient, operator, trace-scalar, chi, and blocked-basis comparison
primitives.

The declarations here do not yet construct the source objects from an MPDO
tensor.  They record the existence statement and witness consequences that the
Appendix C.3--C.4 argument must provide.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.3--C.4
-/

open scoped BigOperators ComplexOrder

namespace MPOTensor

/-- Existential BNT-label theorem witness for the source statement.

The BNT-label theorem data depend on a choice of BNT-label type and
same-length operator spaces.  This structure collects those choices together
with the corresponding theorem data.  The construction of such a witness from
an MPDO tensor is the outstanding step toward Theorem IV.13(ii).
This proposition-level witness uses universe-zero labels and operator spaces;
the intended MPDO-derived finite-dimensional objects live in that universe.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelTheoremWitness (data : AlgebraStructureData d D) where
  /-- The finite type of BNT labels.

  Source: arXiv:1606.00608, Proposition IV.12 and Theorem IV.13(ii),
  lines 948--985 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  Label : Type
  /-- The ambient type of length-`L` BNT operators.

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  OperatorSpace : ℕ → Type
  /-- The BNT-label type is finite.

  This records the finiteness of the BNT decomposition; it is not an
  additional hypothesis beyond the finite labelled family in the source theorem.
  Source: arXiv:1606.00608, Proposition IV.12 and Theorem IV.13(ii),
  lines 948--985 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  labelFintype : Fintype Label
  /-- Each length-`L` operator space is an additive commutative monoid.

  This is formal ambient linear-space structure for the operator algebra in
  eq:algebra, not an extra source-side mathematical hypothesis.
  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  operatorAddCommMonoid : ∀ L : ℕ, AddCommMonoid (OperatorSpace L)
  /-- Each length-`L` operator space is a complex module.

  This is formal ambient linear-space structure for the complex span in
  eq:algebra, not an extra source-side mathematical hypothesis.
  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  operatorModule : ∀ L : ℕ, Module ℂ (OperatorSpace L)
  /-- Each length-`L` operator space has the product used in the source algebra.

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  operatorMul : ∀ L : ℕ, Mul (OperatorSpace L)
  /-- The BNT-label theorem data for these choices.

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
  Appendix C.3--C.4, lines 1830--1942 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  theoremData : @BNTLabelTheoremData d D data Label OperatorSpace
    labelFintype operatorAddCommMonoid operatorModule operatorMul

/-- Existence of the BNT-label data asserted by Theorem IV.13(ii).

This is the proposition-level form of the source statement that there exist
BNT labels, same-length operators, trace scalars, length-independent positive
\(\chi_{\alpha,\beta,\gamma}\)-matrices, and the corresponding product,
idempotent, and blocked-basis comparison data.  It is only the target
existence predicate; constructing such a witness from an MPDO tensor remains
the Appendix C.3--C.4 obligation.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def HasBNTLabelTheoremWitness (data : AlgebraStructureData d D) : Prop :=
  Nonempty (BNTLabelTheoremWitness data)

namespace HasBNTLabelTheoremWitness

/-- Existence of the source BNT-label witness gives existence of a positive
blocked-basis \(\chi\)-witness by pulling back the BNT-label
\(\chi_{\alpha,\beta,\gamma}\)-matrices along the blocked-basis comparison
maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positive_blocked_chi_witness {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    Nonempty (AlgebraStructureData.PositiveBlockedStructureChiTracePowerForm data) := by
  rcases h with ⟨W⟩
  letI : Fintype W.Label := W.labelFintype
  letI : ∀ L : ℕ, AddCommMonoid (W.OperatorSpace L) := W.operatorAddCommMonoid
  letI : ∀ L : ℕ, Module ℂ (W.OperatorSpace L) := W.operatorModule
  letI : ∀ L : ℕ, Mul (W.OperatorSpace L) := W.operatorMul
  exact ⟨W.theoremData.toPositiveBlockedStructureChiTracePowerForm⟩

/-- Existence of the source BNT-label witness gives a blocked-basis
trace-power family with positive entries.

This is the proposition-level corollary for the blocked-basis statement: the
blocked \(\chi\)-family is obtained from the uniform BNT-label
\(\chi\)-family by comparison, rather than postulated as an independent
length-dependent family.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_blocked_chi_trace_power_form {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ χ : AlgebraStructureData.BlockedStructureChiFamily data,
      χ.PosEntries ∧ data.HasBlockedStructureChiTracePowerForm χ := by
  rcases h.positive_blocked_chi_witness with ⟨hχ⟩
  exact ⟨hχ.chi, hχ.posEntries, hχ.tracePower⟩

/-- Existence of the source BNT-label witness gives a positive blocked-basis
\(\chi\)-family whose matrix traces compute the blocked coefficients.

This is the trace-form version of the preceding blocked-basis trace-power
existence statement.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem exists_blocked_coeff_eq_trace_pow {data : AlgebraStructureData d D}
    (h : HasBNTLabelTheoremWitness data) :
    ∃ χ : AlgebraStructureData.BlockedStructureChiFamily data,
      χ.PosEntries ∧
        ∀ (n : ℕ), 0 < n →
          ∀ (i j : AlgebraStructureData.BlockedIndex data n)
            (k : AlgebraStructureData.BlockedIndex data (2 * n)),
          data.blockedStructureCoefficients n i j k =
            (χ.matrix n i j k ^ n).trace := by
  rcases h.exists_blocked_chi_trace_power_form with ⟨χ, hpos, htrace⟩
  refine ⟨χ, hpos, ?_⟩
  intro n hn i j k
  exact htrace.eq_trace_matrix_pow n hn i j k

end HasBNTLabelTheoremWitness

namespace BNTLabelTheoremWitness

/-- Build an existential BNT-label theorem witness in the source-side case
where the coefficient family is canonically determined by the same diagonal
\(\chi_{\alpha,\beta,\gamma}\)-family.

This is the existential form of the source-side \(\chi\)-construction: the
BNT-label type, same-length operator spaces, and their algebraic structure are
supplied as the witness, while the coefficient family is fixed to
\[
  c^{(L)}_{\alpha,\beta,\gamma}
    = \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L}).
\]
Constructing the inputs from an MPDO tensor remains the Appendix C.3--C.4
obligation; this definition only makes the source-side coefficient choice
single-source once those inputs have been produced.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def ofChi (data : AlgebraStructureData d D)
    (Λ : Type) (O : ℕ → Type) [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    (χ : DiagonalChiFamily Λ) (hχ : χ.PosEntries)
    (operators : BNTLabelOperatorFamily Λ O)
    (traceScalars : BNTLabelTraceScalarFamily Λ)
    (sameLengthProduct :
      operators.HasSameLengthProductForm (BNTLabelCoefficientFamily.ofChi χ))
    (idempotent :
      traceScalars.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi χ))
    (blockedComparison :
      BNTBlockedBasisCoefficientComparison data (BNTLabelCoefficientFamily.ofChi χ)) :
    BNTLabelTheoremWitness data where
  Label := Λ
  OperatorSpace := O
  labelFintype := inferInstance
  operatorAddCommMonoid := fun _ => inferInstance
  operatorModule := fun _ => inferInstance
  operatorMul := fun _ => inferInstance
  theoremData :=
    BNTLabelTheoremData.ofChi (data := data) χ hχ operators traceScalars
      sameLengthProduct idempotent blockedComparison

/-- A concrete BNT-label theorem witness gives the proposition-level existence
statement for Theorem IV.13(ii).

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem hasBNTLabelTheoremWitness {data : AlgebraStructureData d D}
    (W : BNTLabelTheoremWitness data) : HasBNTLabelTheoremWitness data :=
  ⟨W⟩

/-- The canonical \(\chi\)-based construction gives the proposition-level
existence statement for Theorem IV.13(ii), once the product law, idempotent
law, and blocked-basis comparison have been supplied for the canonical
coefficient family.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem ofChi_hasBNTLabelTheoremWitness (data : AlgebraStructureData d D)
    (Λ : Type) (O : ℕ → Type) [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    (χ : DiagonalChiFamily Λ) (hχ : χ.PosEntries)
    (operators : BNTLabelOperatorFamily Λ O)
    (traceScalars : BNTLabelTraceScalarFamily Λ)
    (sameLengthProduct :
      operators.HasSameLengthProductForm (BNTLabelCoefficientFamily.ofChi χ))
    (idempotent :
      traceScalars.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi χ))
    (blockedComparison :
      BNTBlockedBasisCoefficientComparison data (BNTLabelCoefficientFamily.ofChi χ)) :
    HasBNTLabelTheoremWitness data :=
  ⟨ofChi data Λ O χ hχ operators traceScalars sameLengthProduct idempotent
    blockedComparison⟩

variable {data : AlgebraStructureData d D} (W : BNTLabelTheoremWitness data)

private instance instLabelFintype : Fintype W.Label :=
  W.labelFintype

private instance instOperatorAddCommMonoid (L : ℕ) :
    AddCommMonoid (W.OperatorSpace L) :=
  W.operatorAddCommMonoid L

private instance instOperatorModule (L : ℕ) : Module ℂ (W.OperatorSpace L) :=
  W.operatorModule L

private instance instOperatorMul (L : ℕ) : Mul (W.OperatorSpace L) :=
  W.operatorMul L

/-- The BNT-label theorem data carried by an existential witness, with the
algebraic structures on the label type and operator spaces supplied by the
witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def toTheoremData :
    @BNTLabelTheoremData d D data W.Label W.OperatorSpace
      W.labelFintype W.operatorAddCommMonoid W.operatorModule W.operatorMul :=
  W.theoremData

/-- The BNT-label coefficient system carried by an existential witness. -/
def coeffs : BNTLabelCoefficientFamily W.Label :=
  W.toTheoremData.coeffs

/-- The same-length BNT operator family carried by an existential witness. -/
def operators : BNTLabelOperatorFamily W.Label W.OperatorSpace :=
  W.toTheoremData.operators

/-- The BNT-label trace scalars carried by an existential witness. -/
def traceScalars : BNTLabelTraceScalarFamily W.Label :=
  W.toTheoremData.traceScalars

/-- The positive BNT-label chi witness carried by an existential witness. -/
def positiveChi : PositiveBNTLabelChiTracePowerForm W.coeffs :=
  W.toTheoremData.positiveChi

/-- The blocked-basis comparison carried by an existential witness. -/
def blockedComparison : BNTBlockedBasisCoefficientComparison data W.coeffs :=
  W.toTheoremData.blockedComparison

/-- The same-length product predicate carried by an existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_form :
    W.operators.HasSameLengthProductForm W.coeffs :=
  W.toTheoremData.same_length_product_form

/-- The idempotent coefficient predicate carried by an existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_coefficient_form :
    W.traceScalars.HasIdempotentCoefficientForm W.coeffs :=
  W.toTheoremData.idempotent_coefficient_form

/-- Positivity of the BNT-label chi matrices carried by an existential
witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positive_chi_pos_entries :
    W.positiveChi.chi.PosEntries :=
  W.toTheoremData.positive_chi_pos_entries

/-- The positive-length trace-power predicate carried by the BNT-label chi
witness in an existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positive_chi_trace_power :
    W.coeffs.HasPositiveLengthChiTracePowerForm W.positiveChi.chi :=
  W.toTheoremData.positive_chi_trace_power

/-- The source BNT label attached by an existential witness to a chosen basis
element of \(\mathcal A_n\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def sourceLabel (n : ℕ) (hn : 0 < n)
    (i : AlgebraStructureData.BlockedIndex data n) : W.Label :=
  W.toTheoremData.sourceLabel n hn i

/-- The target BNT label attached by an existential witness to a chosen basis
element of \(\mathcal A_{2n}\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def targetLabel (n : ℕ) (hn : 0 < n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) : W.Label :=
  W.toTheoremData.targetLabel n hn k

/-- The BNT-label coefficients carried by an existential witness are traces of
powers of the length-independent chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_trace_pow (L : ℕ) (hL : 0 < L) (α β γ : W.Label) :
    W.coeffs.coeff L α β γ =
      (W.positiveChi.chi.matrix α β γ ^ L).trace :=
  W.toTheoremData.coeff_eq_trace_pow L hL α β γ

/-- At every positive length, the coefficient family in an existential witness
agrees with the canonical coefficient family determined by its
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

The restriction \(0<L\) is essential: the source theorem only states the
physical positive-length coefficients, and the formal coefficient family is
not constrained at length zero by Theorem IV.13(ii).

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_ofChi_coeff (L : ℕ) (hL : 0 < L) (α β γ : W.Label) :
    W.coeffs.coeff L α β γ =
      (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi).coeff L α β γ :=
  W.toTheoremData.coeff_eq_ofChi_coeff L hL α β γ

/-- The same-length product law carried by an existential witness may be
written using the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_form_ofChi :
    W.operators.HasSameLengthProductForm
      (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi) :=
  W.toTheoremData.same_length_product_form_ofChi

/-- The same-length product equation carried by an existential witness, written
with the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum_ofChi
    (L : ℕ) (hL : 0 < L) (α β : W.Label) :
    W.operators.operator L α * W.operators.operator L β =
      ∑ γ : W.Label,
        (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi).coeff L α β γ •
          W.operators.operator L γ :=
  W.toTheoremData.same_length_product_eq_sum_ofChi L hL α β

/-- The idempotent scalar law carried by an existential witness may be written
using the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_coefficient_form_ofChi :
    W.traceScalars.HasIdempotentCoefficientForm
      (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi) :=
  W.toTheoremData.idempotent_coefficient_form_ofChi

/-- The idempotent scalar equation carried by an existential witness, written
with the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum_ofChi (γ : W.Label) :
    W.traceScalars.traceScalar γ =
      ∑ α : W.Label, ∑ β : W.Label,
        (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi).coeff 1 α β γ *
          (W.traceScalars.traceScalar α * W.traceScalars.traceScalar β) :=
  W.toTheoremData.idempotent_eq_sum_ofChi γ

/-- The diagonal entries of the chi matrices in an existential witness are
positive.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem chi_entry_pos (α β γ : W.Label)
    (k : Fin (W.positiveChi.chi.dim α β γ)) :
    0 < W.positiveChi.chi.entry α β γ k :=
  W.positiveChi.posEntries α β γ k

/-- The same-length BNT product equation carried by an existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum (L : ℕ) (hL : 0 < L) (α β : W.Label) :
    W.operators.operator L α * W.operators.operator L β =
      ∑ γ : W.Label, W.coeffs.coeff L α β γ • W.operators.operator L γ :=
  W.toTheoremData.same_length_product_eq_sum L hL α β

/-- The idempotent scalar equation carried by an existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), idempotent, lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum (γ : W.Label) :
    W.traceScalars.traceScalar γ =
      ∑ α : W.Label, ∑ β : W.Label,
        W.coeffs.coeff 1 α β γ *
          (W.traceScalars.traceScalar α * W.traceScalars.traceScalar β) :=
  W.toTheoremData.idempotent_eq_sum γ

/-- The blocked-basis/BNT-label coefficient comparison carried by an
existential witness.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      W.coeffs.coeff n
        (W.sourceLabel n hn i)
        (W.sourceLabel n hn j)
        (W.targetLabel n hn k) :=
  W.toTheoremData.blocked_coeff_eq n hn i j k

/-- The blocked-basis comparison carried by an existential witness may be
written using the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def blockedComparison_ofChi :
    BNTBlockedBasisCoefficientComparison data
      (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi) :=
  W.toTheoremData.blockedComparison_ofChi

/-- The blocked-basis coefficient comparison carried by an existential
witness, written with the canonical coefficient family determined by the same
\(\chi_{\alpha,\beta,\gamma}\)-matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_ofChi
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (BNTLabelCoefficientFamily.ofChi W.positiveChi.chi).coeff n
        (W.sourceLabel n hn i)
        (W.sourceLabel n hn j)
        (W.targetLabel n hn k) :=
  W.toTheoremData.blocked_coeff_eq_ofChi n hn i j k

/-- The BNT product expansion carried by an existential witness, with
coefficients written as traces of the length-independent chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem same_length_product_eq_sum_chi_trace_pow
    (L : ℕ) (hL : 0 < L) (α β : W.Label) :
    W.operators.operator L α * W.operators.operator L β =
      ∑ γ : W.Label, (W.positiveChi.chi.matrix α β γ ^ L).trace •
        W.operators.operator L γ :=
  W.toTheoremData.same_length_product_eq_sum_chi_trace_pow L hL α β

/-- The idempotent scalar identity carried by an existential witness, with
length-one coefficients written as traces of the chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem idempotent_eq_sum_chi_trace (γ : W.Label) :
    W.traceScalars.traceScalar γ =
      ∑ α : W.Label, ∑ β : W.Label,
        (W.positiveChi.chi.matrix α β γ).trace *
          (W.traceScalars.traceScalar α * W.traceScalars.traceScalar β) :=
  W.toTheoremData.idempotent_eq_sum_chi_trace γ

/-- The blocked-basis coefficients pulled back by an existential witness are
traces of powers of the BNT-label chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_trace_pow
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (W.positiveChi.chi.matrix
        (W.sourceLabel n hn i)
        (W.sourceLabel n hn j)
        (W.targetLabel n hn k) ^ n).trace :=
  W.toTheoremData.blocked_coeff_eq_trace_pow n hn i j k

/-- An existential BNT-label theorem witness gives a positive blocked
trace-power witness for the chosen algebra-structure data.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def toPositiveBlockedStructureChiTracePowerForm :
    AlgebraStructureData.PositiveBlockedStructureChiTracePowerForm data :=
  W.toTheoremData.toPositiveBlockedStructureChiTracePowerForm

/-- The blocked-basis chi family obtained by pulling back the uniform
BNT-label chi family in an existential witness along the blocked-basis
comparison maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def positiveBlockedChi : AlgebraStructureData.BlockedStructureChiFamily data :=
  W.toPositiveBlockedStructureChiTracePowerForm.chi

/-- At positive blocked length, the blocked-basis chi family obtained from an
existential BNT-label theorem witness is exactly the BNT-label chi family
composed with the source and target comparison maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_toDiagonal_of_pos
    (n : ℕ) (hn : 0 < n) :
    W.positiveBlockedChi.toDiagonal n =
      W.positiveChi.chi.comap (W.blockedComparison.blockedLabel n hn) :=
  W.toTheoremData.positiveBlockedChi_toDiagonal_of_pos n hn

/-- At positive blocked length, the finite-sum trace-power coefficient of the
blocked-basis chi family obtained from an existential BNT-label theorem witness
is the corresponding BNT-label trace-power coefficient.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_tracePowerCoeff_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    W.positiveBlockedChi.tracePowerCoeff n i j k L =
      W.positiveChi.chi.tracePowerCoeff
        (W.sourceLabel n hn i) (W.sourceLabel n hn j) (W.targetLabel n hn k) L :=
  W.toTheoremData.positiveBlockedChi_tracePowerCoeff_of_pos n hn i j k L

/-- At positive blocked length, the size of the blocked-basis chi matrix obtained
from an existential BNT-label theorem witness is the corresponding BNT-label
chi-matrix size.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_dim_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    W.positiveBlockedChi.dim n i j k =
      W.positiveChi.chi.dim
        (W.sourceLabel n hn i) (W.sourceLabel n hn j) (W.targetLabel n hn k) :=
  W.toTheoremData.positiveBlockedChi_dim_of_pos n hn i j k

/-- At positive blocked length, the trace of the `L`-th power of the
blocked-basis chi matrix obtained from an existential BNT-label theorem witness
is the trace of the `L`-th power of the corresponding BNT-label chi matrix.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_trace_matrix_pow_of_pos
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    (W.positiveBlockedChi.matrix n i j k ^ L).trace =
      (W.positiveChi.chi.matrix
        (W.sourceLabel n hn i) (W.sourceLabel n hn j) (W.targetLabel n hn k) ^
          L).trace :=
  W.toTheoremData.positiveBlockedChi_trace_matrix_pow_of_pos n hn i j k L

/-- The pulled-back blocked-basis chi family obtained from an existential
BNT-label theorem witness satisfies the blocked trace-power predicate.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_tracePower :
    data.HasBlockedStructureChiTracePowerForm W.positiveBlockedChi :=
  W.toPositiveBlockedStructureChiTracePowerForm.tracePower

/-- The pulled-back blocked-basis chi family obtained from an existential
BNT-label theorem witness has positive diagonal entries.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_posEntries :
    W.positiveBlockedChi.PosEntries :=
  W.toPositiveBlockedStructureChiTracePowerForm.posEntries

/-- The pulled-back blocked-basis chi entries obtained from an existential
BNT-label theorem witness are positive.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem positiveBlockedChi_entry_pos
    (n : ℕ) (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (r : Fin (W.positiveBlockedChi.dim n i j k)) :
    0 < W.positiveBlockedChi.entry n i j k r :=
  W.toPositiveBlockedStructureChiTracePowerForm.posEntries n i j k r

/-- For an existential BNT-label theorem witness, the blocked-basis
coefficients are traces of powers of the pulled-back blocked-basis chi
matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_positiveBlockedChi_trace_pow
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (W.positiveBlockedChi.matrix n i j k ^ n).trace :=
  W.toPositiveBlockedStructureChiTracePowerForm.eq_trace_pow n hn i j k

end BNTLabelTheoremWitness

end MPOTensor
