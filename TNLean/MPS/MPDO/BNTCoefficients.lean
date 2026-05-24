/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AlgebraStructure

/-!
# BNT-label coefficient statements for MPDO algebra structures

This file records the BNT-label coefficient side of arXiv:1606.00608,
Theorem IV.13(ii).  It separates the paper's fixed BNT-label coefficients from
the chosen blocked-basis coefficients in `AlgebraStructure.lean`.

The declarations here state the coefficient, product, trace-scalar, and
blocked-basis comparison predicates.  They do not yet construct those objects
from an MPDO tensor; that construction remains part of the Appendix C.3--C.4
comparison work.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.3--C.4
-/

open scoped BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The BNT-label structure coefficients \(c_{\alpha,\beta,\gamma}^{(L)}\)
appearing in the same-length operator algebra of
arXiv:1606.00608, Theorem IV.13(ii).

Here `Λ` is the type of BNT labels.  The coefficient `coeff L α β γ` is the
scalar multiplying the length-`L` BNT operator with label `γ` in the product of
the length-`L` operators with labels `α` and `β`.

This structure only stores the coefficient system.  Its role is to keep the
BNT-label indices from the paper distinct from chosen blocked-basis indices.
The same-length product formula is recorded separately by
`BNTLabelOperatorFamily.HasSameLengthProductForm`:
\[
  O_L(M_\alpha)O_L(M_\beta)
    = \sum_\gamma c^{(L)}_{\alpha,\beta,\gamma}O_L(M_\gamma),
\]
It also does not yet compare these coefficients with the chosen blocked-basis
coefficients of the support algebras.  That comparison step is one of the
remaining obligations recorded in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 1925--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelCoefficientFamily (Λ : Type*) where
  /-- The coefficient \(c_{\alpha,\beta,\gamma}^{(L)}\). -/
  coeff : ℕ → Λ → Λ → Λ → ℂ

namespace BNTLabelCoefficientFamily

variable {Λ : Type*} (c : BNTLabelCoefficientFamily Λ)

/-- Positive-length trace-power compatibility for BNT-label coefficients.

This is the faithful quantifier shape of arXiv:1606.00608, Theorem IV.13(ii):
for every positive chain length `L`, the coefficient
`c^{(L)}_{\alpha,\beta,\gamma}` is the trace of the `L`-th power of the same
diagonal matrix `χ_{\alpha,\beta,\gamma}`.  The matrix family is independent of
`L`; only the exponent changes.  Unlike the unrestricted function-level
predicate `HasChiTracePowerForm`, this predicate has exactly the positive-length
quantifier used for Theorem IV.13(ii). -/
def HasPositiveLengthChiTracePowerForm (χ : DiagonalChiFamily Λ) : Prop :=
  ∀ L : ℕ, 0 < L → ∀ α β γ : Λ,
    c.coeff L α β γ = χ.tracePowerCoeff α β γ L

/-- Trace reformulation of positive-length BNT-label trace-power form. -/
theorem HasPositiveLengthChiTracePowerForm.eq_trace_matrix_pow
    {χ : DiagonalChiFamily Λ} (h : c.HasPositiveLengthChiTracePowerForm χ)
    (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (χ.matrix α β γ ^ L).trace := by
  rw [h L hL α β γ, χ.trace_matrix_pow]

end BNTLabelCoefficientFamily

/-- BNT-label operators \(O_L(M_\alpha)\) at each positive chain length.

Here `Λ` is the fixed BNT-label type, and `O L` is the ambient algebra of
length-`L` operators.  This structure records only the family
\(\alpha \mapsto O_L(M_\alpha)\) for each length; the product law is the
separate predicate `BNTLabelOperatorFamily.HasSameLengthProductForm`.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelOperatorFamily (Λ : Type*) (O : ℕ → Type*) where
  /-- The length-`L` operator \(O_L(M_\alpha)\). -/
  operator : ∀ L : ℕ, Λ → O L

namespace BNTLabelOperatorFamily

variable {Λ : Type*} {O : ℕ → Type*} (op : BNTLabelOperatorFamily Λ O)

/-- Same-length BNT product formula from Theorem IV.13(ii).

For every positive length `L`, the product of the two length-`L` BNT operators
with labels `α` and `β` expands again in the length-`L` BNT operators, with
coefficients \(c^{(L)}_{\alpha,\beta,\gamma}\):
\[
  O_L(M_\alpha)O_L(M_\beta)
    = \sum_\gamma c^{(L)}_{\alpha,\beta,\gamma}O_L(M_\gamma).
\]
The predicate is abstract in the ambient length-`L` algebra.  Later comparison
theorems must relate this same-length algebra to the chosen blocked support
algebras.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def HasSameLengthProductForm [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    (c : BNTLabelCoefficientFamily Λ) : Prop :=
  ∀ L : ℕ, 0 < L → ∀ α β : Λ,
    op.operator L α * op.operator L β =
      ∑ γ : Λ, c.coeff L α β γ • op.operator L γ

/-- Restatement of the same-length BNT product formula as an equality. -/
theorem HasSameLengthProductForm.eq_sum [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    {c : BNTLabelCoefficientFamily Λ}
    (h : op.HasSameLengthProductForm c)
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    op.operator L α * op.operator L β =
      ∑ γ : Λ, c.coeff L α β γ • op.operator L γ :=
  h L hL α β

end BNTLabelOperatorFamily

/-- The trace scalars \(m_\alpha=\operatorname{tr}(\mu_\alpha)\) appearing in
the idempotent condition of Theorem IV.13(ii).

Here `Λ` is the fixed BNT-label type, and `traceScalar α` is the scalar
\(m_\alpha\) attached to the positive diagonal matrix \(\mu_\alpha\) in the
source proof.  The coefficient identity itself is the predicate
`BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm`.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelTraceScalarFamily (Λ : Type*) where
  /-- The scalar \(m_\alpha=\operatorname{tr}(\mu_\alpha)\). -/
  traceScalar : Λ → ℂ

namespace BNTLabelTraceScalarFamily

variable {Λ : Type*} (m : BNTLabelTraceScalarFamily Λ)

/-- Idempotent coefficient condition from Theorem IV.13(ii).

The length-one BNT coefficients reconstruct each trace scalar as
\[
  m_\gamma =
    \sum_{\alpha,\beta} c^{(1)}_{\alpha,\beta,\gamma} m_\alpha m_\beta.
\]
This predicate records only that scalar identity; constructing the scalars from
an MPDO tensor and comparing the coefficients with the blocked support-algebra
coefficients are separate obligations.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 981--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def HasIdempotentCoefficientForm [Fintype Λ]
    (c : BNTLabelCoefficientFamily Λ) : Prop :=
  ∀ γ : Λ, m.traceScalar γ =
    ∑ α : Λ, ∑ β : Λ,
      c.coeff 1 α β γ * (m.traceScalar α * m.traceScalar β)

/-- Restatement of the BNT idempotent coefficient condition as an equality. -/
theorem HasIdempotentCoefficientForm.eq_sum [Fintype Λ]
    {c : BNTLabelCoefficientFamily Λ}
    (h : m.HasIdempotentCoefficientForm c) (γ : Λ) :
    m.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        c.coeff 1 α β γ * (m.traceScalar α * m.traceScalar β) :=
  h γ

end BNTLabelTraceScalarFamily

/-- Comparison between chosen blocked-basis multiplication coefficients and
BNT-label coefficients.

For each positive blocked length `n`, the maps `sourceLabel` and `targetLabel`
read the chosen basis labels of \(\mathcal A_n\) and \(\mathcal A_{2n}\) as
BNT labels.  The comparison equality says that the blocked-basis coefficient of
the product of two chosen basis elements is the corresponding BNT-label
coefficient:
\[
  c^{(n)}_{i,j,k}
    =
  c^{(n)}_{\alpha(i),\alpha(j),\alpha(k)}.
\]
This structure records the comparison statement only.  Constructing the label
maps from the Appendix C.3 decomposition and relating this blocked product to
the same-length BNT operator product remain separate obligations.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTBlockedBasisCoefficientComparison
    (data : AlgebraStructureData d D) {Λ : Type*}
    (c : BNTLabelCoefficientFamily Λ) where
  /-- BNT label attached to a chosen basis element of \(\mathcal A_n\). -/
  sourceLabel :
    ∀ n : ℕ, 0 < n → AlgebraStructureData.BlockedIndex data n → Λ
  /-- BNT label attached to a chosen basis element of \(\mathcal A_{2n}\). -/
  targetLabel :
    ∀ n : ℕ, 0 < n → AlgebraStructureData.BlockedIndex data (2 * n) → Λ
  /-- The blocked-basis coefficient is the pullback of the BNT-label coefficient. -/
  coeff_eq : ∀ (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)),
    data.blockedStructureCoefficients n i j k =
      c.coeff n (sourceLabel n hn i) (sourceLabel n hn j) (targetLabel n hn k)

namespace BNTBlockedBasisCoefficientComparison

variable {data : AlgebraStructureData d D} {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}
  (cmp : BNTBlockedBasisCoefficientComparison data c)

/-- Restatement of the blocked-basis/BNT-label coefficient comparison. -/
theorem blocked_coeff_eq (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      c.coeff n (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j)
        (cmp.targetLabel n hn k) :=
  cmp.coeff_eq n hn i j k

end BNTBlockedBasisCoefficientComparison

/-- A positive BNT-label chi witness for Theorem IV.13(ii).

The witness consists of the paper's positive diagonal matrices
\(\chi_{\alpha,\beta,\gamma}\), indexed by fixed BNT labels and independent of
the chain length, together with the positive-length trace-power identity for
the BNT-label coefficient system.

This is not yet a proof of Theorem IV.13(ii) from an MPDO tensor: it is the
paper-faithful coefficient statement to be constructed.  The construction of
this witness and the comparison to blocked bases remain the obligations
described in `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and Appendix C.4,
lines 1925--1942 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure PositiveBNTLabelChiTracePowerForm
    {Λ : Type*} (c : BNTLabelCoefficientFamily Λ) where
  /-- The length-independent BNT-label chi family. -/
  chi : DiagonalChiFamily Λ
  /-- Positivity of every diagonal entry. -/
  posEntries : chi.PosEntries
  /-- Positive-length trace-power form for the BNT-label coefficients. -/
  tracePower : c.HasPositiveLengthChiTracePowerForm chi

namespace PositiveBNTLabelChiTracePowerForm

variable {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- A positive BNT-label chi witness gives the trace formula at every positive
length. -/
theorem eq_trace_pow (h : PositiveBNTLabelChiTracePowerForm c)
    (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (h.chi.matrix α β γ ^ L).trace :=
  BNTLabelCoefficientFamily.HasPositiveLengthChiTracePowerForm.eq_trace_matrix_pow
    (c := c) h.tracePower L hL α β γ

end PositiveBNTLabelChiTracePowerForm

end MPOTensor
