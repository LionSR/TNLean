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
the chosen blocked-basis coefficients attached to the support algebras.

The declarations here state the coefficient, product, trace-scalar, chi, and
blocked-basis comparison predicates.  The theorem-data layer built from these
predicates and the corresponding existential witness are recorded in separate
files.  These files do not yet construct the source objects from an MPDO tensor;
that construction remains part of the Appendix C.3--C.4 comparison work.

The source comparison and remaining construction plan for these coefficient
objects are recorded in `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`,
Section "BNT-label coefficient objects and remaining elimination plan".

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem IV.13(ii) and Appendix C.3--C.4
-/

open scoped BigOperators ComplexOrder

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
Comparison with chosen blocked-basis coefficients is deliberately separated.
The predicate
`BNTBlockedBasisCoefficientComparison` records that comparison once the
Appendix C.3 label maps have been supplied; constructing those maps from an
MPDO tensor remains part of the gap recorded in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`, Section "BNT-label
coefficient objects and remaining elimination plan".
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.4, lines 1925--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelCoefficientFamily (Λ : Type*) where
  /-- The coefficient \(c_{\alpha,\beta,\gamma}^{(L)}\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  coeff : ℕ → Λ → Λ → Λ → ℂ

namespace BNTLabelCoefficientFamily

variable {Λ : Type*} (c : BNTLabelCoefficientFamily Λ)

/-- The BNT-label coefficient family canonically determined by a diagonal
\(\chi_{\alpha,\beta,\gamma}\)-family.

This is the source-side specialization used after Appendix C.4 constructs the
positive diagonal matrices:
\[
  c^{(L)}_{\alpha,\beta,\gamma}
    = \operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L}).
\]
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def ofChi (χ : DiagonalChiFamily Λ) : BNTLabelCoefficientFamily Λ where
  coeff L α β γ := χ.tracePowerCoeff α β γ L

/-- Coefficients of the canonical BNT-label coefficient family associated to
a \(\chi\)-family.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem ofChi_coeff (χ : DiagonalChiFamily Λ) (L : ℕ) (α β γ : Λ) :
    (ofChi χ).coeff L α β γ = χ.tracePowerCoeff α β γ L :=
  rfl

/-- Coefficients of the canonical BNT-label coefficient family are traces of
powers of the corresponding diagonal \(\chi\)-matrices.

The source theorem uses this expression for positive chain lengths in the
same-length product formula; the canonical coefficient family is indexed by
all natural lengths, and this equality follows from the definition and the
diagonal trace identity.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem ofChi_coeff_eq_trace_matrix_pow
    (χ : DiagonalChiFamily Λ) (L : ℕ) (α β γ : Λ) :
    (ofChi χ).coeff L α β γ = (χ.matrix α β γ ^ L).trace := by
  rw [ofChi_coeff, χ.trace_matrix_pow]

/-- Positive-length trace-power compatibility for BNT-label coefficients.

This is the faithful quantifier shape of arXiv:1606.00608, Theorem IV.13(ii):
for every positive chain length `L`, the coefficient
`c^{(L)}_{\alpha,\beta,\gamma}` is the trace of the `L`-th power of the same
diagonal matrix `χ_{\alpha,\beta,\gamma}`.  The matrix family is independent of
`L`; only the exponent changes.  Unlike the unrestricted function-level
predicate `HasChiTracePowerForm`, this predicate has exactly the positive-length
quantifier used for Theorem IV.13(ii).

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def HasPositiveLengthChiTracePowerForm (χ : DiagonalChiFamily Λ) : Prop :=
  ∀ L : ℕ, 0 < L → ∀ α β γ : Λ,
    c.coeff L α β γ = χ.tracePowerCoeff α β γ L

/-- Trace reformulation of positive-length BNT-label trace-power form.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasPositiveLengthChiTracePowerForm.eq_trace_matrix_pow
    {χ : DiagonalChiFamily Λ} (h : c.HasPositiveLengthChiTracePowerForm χ)
    (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (χ.matrix α β γ ^ L).trace := by
  rw [h L hL α β γ, χ.trace_matrix_pow]

/-- The coefficient family canonically associated to a \(\chi\)-family has the
positive-length trace-power form with respect to that same \(\chi\)-family.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem ofChi_hasPositiveLengthChiTracePowerForm (χ : DiagonalChiFamily Λ) :
    (ofChi χ).HasPositiveLengthChiTracePowerForm χ := by
  intro L _hL α β γ
  rfl

end BNTLabelCoefficientFamily

/-- BNT-label operators \(O_L(M_\alpha)\) at each positive chain length.

Here `Λ` is the fixed BNT-label type, and `O L` is the ambient algebra of
length-`L` operators.  This structure records only the family
\(\alpha \mapsto O_L(M_\alpha)\) for each length; the product law is the
separate predicate `BNTLabelOperatorFamily.HasSameLengthProductForm`.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTLabelOperatorFamily (Λ : Type*) (O : ℕ → Type*) where
  /-- The length-`L` operator \(O_L(M_\alpha)\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
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
  /-- The scalar \(m_\alpha=\operatorname{tr}(\mu_\alpha)\).

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 981--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
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

/-- Assignment of BNT labels to chosen blocked-basis elements.

For each positive blocked length `n`, the source map reads a chosen basis label
of \(\mathcal A_n\) as a BNT label, while the target map reads a chosen basis
label of \(\mathcal A_{2n}\) as a BNT label.  This is the source-side
Appendix C.3 input needed before one can compare the blocked-basis
coefficients with the BNT-label coefficient system.

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTBlockedBasisLabelAssignment (data : AlgebraStructureData d D)
    (Λ : Type*) where
  /-- BNT label attached to a chosen basis element of \(\mathcal A_n\).

  Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  sourceLabel :
    ∀ n : ℕ, 0 < n → AlgebraStructureData.BlockedIndex data n → Λ
  /-- BNT label attached to a chosen basis element of \(\mathcal A_{2n}\).

  Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  targetLabel :
    ∀ n : ℕ, 0 < n → AlgebraStructureData.BlockedIndex data (2 * n) → Λ

namespace BNTBlockedBasisLabelAssignment

variable {data : AlgebraStructureData d D} {Λ : Type*}
  (labels : BNTBlockedBasisLabelAssignment data Λ)

/-- The single label map on the disjoint union of source- and target-length
blocked-basis labels.

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def blockedLabel (n : ℕ) (hn : 0 < n) :
    AlgebraStructureData.BlockedIndex data n ⊕
      AlgebraStructureData.BlockedIndex data (2 * n) → Λ
  | Sum.inl i => labels.sourceLabel n hn i
  | Sum.inr k => labels.targetLabel n hn k

end BNTBlockedBasisLabelAssignment

/-- Comparison between chosen blocked-basis multiplication coefficients and
BNT-label coefficients.

The label assignment reads chosen basis labels of \(\mathcal A_n\) and
\(\mathcal A_{2n}\) as BNT labels.  The comparison equality says that the
blocked-basis coefficient of the product of two chosen basis elements is the
corresponding BNT-label coefficient:
\[
  c^{(n)}_{i,j,k}
    =
  c^{(n)}_{\sigma_n(i),\sigma_n(j),\tau_n(k)}.
\]
Here \(\sigma_n\) denotes the source label map, and \(\tau_n\) denotes the target
label map.
**Scope restriction (blocked product length):** The source product law is a
same-length identity for the BNT operators.  This predicate still compares the
blocked support-algebra product
\(\mathcal A_n \times \mathcal A_n \to \mathcal A_{2n}\), so the target label
map is defined on the chosen basis of \(\mathcal A_{2n}\).  It is a
blocked-basis comparison statement, not the same-length product law itself.
The restriction is documented in
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`, Section "BNT-label
coefficient objects and remaining elimination plan".

This structure records the comparison statement only.  Constructing the label
maps from the Appendix C.3 decomposition and relating this blocked product to
the same-length BNT operator product remain separate obligations.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTBlockedBasisCoefficientComparison
    (data : AlgebraStructureData d D) {Λ : Type*}
    (c : BNTLabelCoefficientFamily Λ) where
  /-- The Appendix C.3 BNT-label assignment for the chosen blocked bases.

  Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  labelAssignment : BNTBlockedBasisLabelAssignment data Λ
  /-- The blocked-basis coefficient is pulled back from the source-length
  BNT-label coefficient.

  Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
  Appendix C.3, lines 1830--1922 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  coeff_eq : ∀ (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)),
    data.blockedStructureCoefficients n i j k =
      c.coeff n (labelAssignment.sourceLabel n hn i)
        (labelAssignment.sourceLabel n hn j) (labelAssignment.targetLabel n hn k)

namespace BNTBlockedBasisCoefficientComparison

variable {data : AlgebraStructureData d D} {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}
  (cmp : BNTBlockedBasisCoefficientComparison data c)

/-- The source BNT label attached to a chosen basis element of
\(\mathcal A_n\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def sourceLabel (n : ℕ) (hn : 0 < n)
    (i : AlgebraStructureData.BlockedIndex data n) : Λ :=
  cmp.labelAssignment.sourceLabel n hn i

/-- The target BNT label attached to a chosen basis element of
\(\mathcal A_{2n}\).

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def targetLabel (n : ℕ) (hn : 0 < n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) : Λ :=
  cmp.labelAssignment.targetLabel n hn k

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
this witness from the Appendix C.3--C.4 data remains the main obligation
described in `docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`, Section
"BNT-label coefficient objects and remaining elimination plan"; the
blocked-basis comparison predicate is recorded separately below.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and Appendix C.4,
lines 1925--1942 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure PositiveBNTLabelChiTracePowerForm
    {Λ : Type*} (c : BNTLabelCoefficientFamily Λ) where
  /-- The length-independent BNT-label chi family.

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
  Appendix C.4, lines 1925--1942 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  chi : DiagonalChiFamily Λ
  /-- Positivity of every diagonal entry.

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  posEntries : chi.PosEntries
  /-- Positive-length trace-power form for the BNT-label coefficients.

  Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
  `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
  tracePower : c.HasPositiveLengthChiTracePowerForm chi

namespace PositiveBNTLabelChiTracePowerForm

variable {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- Build a positive BNT-label trace-power witness from a positive
\(\chi\)-family by taking the coefficient family to be
\(\operatorname{tr}(\chi_{\alpha,\beta,\gamma}^{L})\).

This records the coefficient part of the Appendix C.4 construction: once the
positive diagonal matrices \(\chi_{\alpha,\beta,\gamma}\) have been produced,
the corresponding coefficient system is their trace-power family.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def ofChi (χ : DiagonalChiFamily Λ) (hχ : χ.PosEntries) :
    PositiveBNTLabelChiTracePowerForm (BNTLabelCoefficientFamily.ofChi χ) where
  chi := χ
  posEntries := hχ
  tracePower := BNTLabelCoefficientFamily.ofChi_hasPositiveLengthChiTracePowerForm χ

/-- A positive BNT-label chi witness gives the trace formula at every positive
length. -/
theorem eq_trace_pow (h : PositiveBNTLabelChiTracePowerForm c)
    (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    c.coeff L α β γ = (h.chi.matrix α β γ ^ L).trace :=
  BNTLabelCoefficientFamily.HasPositiveLengthChiTracePowerForm.eq_trace_matrix_pow
    (c := c) h.tracePower L hL α β γ

end PositiveBNTLabelChiTracePowerForm

namespace BNTLabelOperatorFamily

variable {Λ : Type*} {O : ℕ → Type*} {c : BNTLabelCoefficientFamily Λ}
  {op : BNTLabelOperatorFamily Λ O}

/-- The same-length BNT product formula, after substituting the trace-power
formula supplied by a positive BNT-label chi witness.

This is the coefficient-level combination of the product identity in
arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, with the trace-power
formula for \(c^{(L)}_{\alpha,\beta,\gamma}\). -/
theorem HasSameLengthProductForm.eq_sum_chi_trace_pow [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    (hop : op.HasSameLengthProductForm c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    op.operator L α * op.operator L β =
      ∑ γ : Λ, (hχ.chi.matrix α β γ ^ L).trace • op.operator L γ := by
  rw [BNTLabelOperatorFamily.HasSameLengthProductForm.eq_sum (op := op) hop L hL α β]
  refine Finset.sum_congr rfl ?_
  intro γ _hγ
  rw [hχ.eq_trace_pow L hL α β γ]

/-- The same-length BNT product formula for the canonical coefficient family
associated to a \(\chi\)-family, written directly with trace-power
coefficients.

This is the coefficient-level form of arXiv:1606.00608,
Theorem IV.13(ii), eq:algebra, lines 972--985, after choosing the canonical
coefficient family described in Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasSameLengthProductForm.eq_sum_ofChi_trace_pow [Fintype Λ]
    [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
    [∀ L : ℕ, Mul (O L)]
    {χ : DiagonalChiFamily Λ}
    (hop : op.HasSameLengthProductForm (BNTLabelCoefficientFamily.ofChi χ))
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    op.operator L α * op.operator L β =
      ∑ γ : Λ, (χ.matrix α β γ ^ L).trace • op.operator L γ := by
  rw [BNTLabelOperatorFamily.HasSameLengthProductForm.eq_sum (op := op) hop L hL α β]
  refine Finset.sum_congr rfl ?_
  intro γ _hγ
  rw [BNTLabelCoefficientFamily.ofChi_coeff_eq_trace_matrix_pow]

end BNTLabelOperatorFamily

namespace BNTLabelTraceScalarFamily

variable {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}
  {m : BNTLabelTraceScalarFamily Λ}

/-- The BNT idempotent scalar identity, after substituting the length-one
trace formula supplied by a positive BNT-label chi witness.

This is the coefficient-level combination of the idempotent condition in
arXiv:1606.00608, Theorem IV.13(ii), lines 981--985, with the trace-power
formula for \(c^{(1)}_{\alpha,\beta,\gamma}\). -/
theorem HasIdempotentCoefficientForm.eq_sum_chi_trace [Fintype Λ]
    (hm : m.HasIdempotentCoefficientForm c)
    (hχ : PositiveBNTLabelChiTracePowerForm c) (γ : Λ) :
    m.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        (hχ.chi.matrix α β γ).trace * (m.traceScalar α * m.traceScalar β) := by
  rw [BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm.eq_sum (m := m) hm γ]
  refine Finset.sum_congr rfl ?_
  intro α _hα
  refine Finset.sum_congr rfl ?_
  intro β _hβ
  rw [hχ.eq_trace_pow 1 Nat.zero_lt_one α β γ]
  simp

/-- The BNT idempotent scalar identity for the canonical coefficient family
associated to a \(\chi\)-family, written directly with length-one traces.

This is the coefficient-level form of arXiv:1606.00608,
Theorem IV.13(ii), idempotent equation, lines 981--985, after choosing the
canonical coefficient family described in Appendix C.4, lines 2015--2037 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem HasIdempotentCoefficientForm.eq_sum_ofChi_trace [Fintype Λ]
    {χ : DiagonalChiFamily Λ}
    (hm : m.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi χ))
    (γ : Λ) :
    m.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        (χ.matrix α β γ).trace * (m.traceScalar α * m.traceScalar β) := by
  rw [BNTLabelTraceScalarFamily.HasIdempotentCoefficientForm.eq_sum (m := m) hm γ]
  refine Finset.sum_congr rfl ?_
  intro α _hα
  refine Finset.sum_congr rfl ?_
  intro β _hβ
  rw [BNTLabelCoefficientFamily.ofChi_coeff_eq_trace_matrix_pow]
  simp

end BNTLabelTraceScalarFamily

namespace BNTBlockedBasisCoefficientComparison

variable {data : AlgebraStructureData d D} {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- The label map on the disjoint union of source and target blocked basis
indices at a positive blocked length.

Source: arXiv:1606.00608, Appendix C.3, lines 1830--1922, and Theorem
IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def blockedLabel (cmp : BNTBlockedBasisCoefficientComparison data c)
    (n : ℕ) (hn : 0 < n) :
    AlgebraStructureData.BlockedIndex data n ⊕
      AlgebraStructureData.BlockedIndex data (2 * n) → Λ :=
  cmp.labelAssignment.blockedLabel n hn

/-- A blocked-basis/BNT-label coefficient comparison transports a positive
BNT-label chi trace-power witness to each blocked-basis coefficient. -/
theorem blocked_coeff_eq_trace_pow
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (hχ.chi.matrix (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j)
        (cmp.targetLabel n hn k) ^ n).trace := by
  rw [cmp.blocked_coeff_eq n hn i j k]
  exact hχ.eq_trace_pow n hn
    (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k)

/-- A blocked-basis/BNT-label coefficient comparison against the canonical
coefficient family associated to a \(\chi\)-family rewrites each
positive-length blocked coefficient as the corresponding trace power.

This is the canonical-coefficient version of the blocked-basis comparison
corollary.  It does not construct the comparison maps or the \(\chi\)-family
from an MPDO tensor.
Source: arXiv:1606.00608, Theorem IV.13(ii), eq:algebra, lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_ofChi_trace_pow
    {χ : DiagonalChiFamily Λ}
    (cmp :
      BNTBlockedBasisCoefficientComparison data (BNTLabelCoefficientFamily.ofChi χ))
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (χ.matrix (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j)
        (cmp.targetLabel n hn k) ^ n).trace := by
  rw [cmp.blocked_coeff_eq n hn i j k]
  rw [BNTLabelCoefficientFamily.ofChi_coeff_eq_trace_matrix_pow]

/-- The blocked chi family obtained by pulling back a BNT-label chi witness
along a blocked-basis comparison.

The comparison maps are defined only for positive lengths.  The value at
`n = 0` is therefore the empty diagonal family; this component is not used by
the positive-length blocked trace-power identity. -/
def pulledBlockedChiFamily
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c) :
    AlgebraStructureData.BlockedStructureChiFamily data where
  toDiagonal n :=
    if hn : 0 < n then
      hχ.chi.comap (cmp.blockedLabel n hn)
    else
      DiagonalChiFamily.empty _

/-- At positive blocked length, the pulled-back blocked chi family is exactly
the BNT-label chi family composed with the source and target comparison maps.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem pulledBlockedChiFamily_toDiagonal_of_pos
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n) :
    (cmp.pulledBlockedChiFamily hχ).toDiagonal n =
      hχ.chi.comap (cmp.blockedLabel n hn) := by
  simp [pulledBlockedChiFamily, hn]

/-- At positive blocked length, the finite-sum trace-power coefficient of the
pulled-back blocked chi family is the corresponding BNT-label trace-power
coefficient.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem pulledBlockedChi_tracePowerCoeff_of_pos
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    (cmp.pulledBlockedChiFamily hχ).tracePowerCoeff n i j k L =
      hχ.chi.tracePowerCoeff
        (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k) L := by
  rw [AlgebraStructureData.BlockedStructureChiFamily.tracePowerCoeff]
  rw [cmp.pulledBlockedChiFamily_toDiagonal_of_pos hχ n hn]
  rfl

/-- At positive blocked length, the size of the pulled-back blocked chi matrix
is the corresponding BNT-label chi-matrix size.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem pulledBlockedChi_dim_of_pos
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    (cmp.pulledBlockedChiFamily hχ).dim n i j k =
      hχ.chi.dim
        (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k) := by
  rw [AlgebraStructureData.BlockedStructureChiFamily.dim]
  rw [cmp.pulledBlockedChiFamily_toDiagonal_of_pos hχ n hn]
  rfl

/-- At positive blocked length, the trace of the `L`-th power of the
pulled-back blocked chi matrix is the trace of the `L`-th power of the
corresponding BNT-label chi matrix.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem pulledBlockedChi_trace_matrix_pow_of_pos
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n))
    (L : ℕ) :
    ((cmp.pulledBlockedChiFamily hχ).matrix n i j k ^ L).trace =
      (hχ.chi.matrix
        (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k) ^
          L).trace := by
  rw [AlgebraStructureData.BlockedStructureChiFamily.trace_matrix_pow]
  rw [cmp.pulledBlockedChi_tracePowerCoeff_of_pos hχ n hn i j k L]
  rw [← hχ.chi.trace_matrix_pow
    (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k) L]

/-- A blocked-basis/BNT-label coefficient comparison transports a positive
BNT-label chi witness to the trace-power formula for the pulled-back
blocked-basis chi matrix.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and
Appendix C.3--C.4, lines 1830--1942 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem blocked_coeff_eq_pulledBlockedChi_trace_pow
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c)
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      ((cmp.pulledBlockedChiFamily hχ).matrix n i j k ^ n).trace := by
  rw [cmp.blocked_coeff_eq_trace_pow hχ n hn i j k]
  rw [cmp.pulledBlockedChi_trace_matrix_pow_of_pos hχ n hn i j k n]

/-- A positive BNT-label chi witness and a blocked-basis comparison give a
positive blocked chi trace-power witness.

This is a derived blocked-basis statement.  It does not construct the BNT-label
coefficient family or comparison maps from an MPDO tensor; it only transports an
already given uniform BNT-label witness along an already given comparison.  The
unused zero-length component of the blocked chi family is filled by empty
diagonal matrices.
Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985, and Appendix C.3--C.4,
lines 1830--1942 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
def toPositiveBlockedStructureChiTracePowerForm
    (cmp : BNTBlockedBasisCoefficientComparison data c)
    (hχ : PositiveBNTLabelChiTracePowerForm c) :
    AlgebraStructureData.PositiveBlockedStructureChiTracePowerForm data where
  chi := cmp.pulledBlockedChiFamily hχ
  posEntries := by
    intro n i j k r
    by_cases hn : 0 < n
    · have hpos : ((cmp.pulledBlockedChiFamily hχ).toDiagonal n).PosEntries := by
        simpa only [pulledBlockedChiFamily, dif_pos hn] using
          hχ.posEntries.comap (cmp.blockedLabel n hn)
      exact hpos (Sum.inl i) (Sum.inl j) (Sum.inr k) r
    · have hpos : ((cmp.pulledBlockedChiFamily hχ).toDiagonal n).PosEntries := by
        simpa only [pulledBlockedChiFamily, dif_neg hn] using
          DiagonalChiFamily.PosEntries.empty
            (AlgebraStructureData.BlockedIndex data n ⊕
              AlgebraStructureData.BlockedIndex data (2 * n))
      exact hpos (Sum.inl i) (Sum.inl j) (Sum.inr k) r
  tracePower := by
    intro n hn i j k
    rw [cmp.blocked_coeff_eq n hn i j k]
    rw [cmp.pulledBlockedChi_tracePowerCoeff_of_pos hχ n hn i j k n]
    exact hχ.tracePower n hn
      (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k)

end BNTBlockedBasisCoefficientComparison

end MPOTensor
