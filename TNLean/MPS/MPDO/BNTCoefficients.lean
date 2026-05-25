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
`docs/paper-gaps/cpgsv17_blocked_chi_uniformity.tex`.

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
  /-- The blocked-basis coefficient is pulled back from the source-length
  BNT-label coefficient. -/
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

end BNTLabelTraceScalarFamily

namespace BNTBlockedBasisCoefficientComparison

variable {data : AlgebraStructureData d D} {Λ : Type*} {c : BNTLabelCoefficientFamily Λ}

/-- The label map on the disjoint union of source and target blocked basis
indices at a positive blocked length. -/
def blockedLabel (cmp : BNTBlockedBasisCoefficientComparison data c)
    (n : ℕ) (hn : 0 < n) :
    AlgebraStructureData.BlockedIndex data n ⊕
      AlgebraStructureData.BlockedIndex data (2 * n) → Λ
  | Sum.inl i => cmp.sourceLabel n hn i
  | Sum.inr k => cmp.targetLabel n hn k

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
    simpa only [AlgebraStructureData.BlockedStructureChiFamily.tracePowerCoeff,
      pulledBlockedChiFamily, DiagonalChiFamily.comap, blockedLabel, dif_pos hn] using
      hχ.tracePower n hn
        (cmp.sourceLabel n hn i) (cmp.sourceLabel n hn j) (cmp.targetLabel n hn k)

end BNTBlockedBasisCoefficientComparison

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
  /-- The BNT-label coefficient system \(c^{(L)}_{\alpha,\beta,\gamma}\). -/
  coeffs : BNTLabelCoefficientFamily Λ
  /-- The BNT-label operator family \(O_L(M_\alpha)\). -/
  operators : BNTLabelOperatorFamily Λ O
  /-- The trace scalars \(m_\alpha=\operatorname{tr}(\mu_\alpha)\). -/
  traceScalars : BNTLabelTraceScalarFamily Λ
  /-- The same-length BNT product law. -/
  sameLengthProduct : operators.HasSameLengthProductForm coeffs
  /-- The idempotent scalar condition. -/
  idempotent : traceScalars.HasIdempotentCoefficientForm coeffs
  /-- The positive length-independent BNT-label chi witness. -/
  positiveChi : PositiveBNTLabelChiTracePowerForm coeffs
  /-- Comparison of the chosen blocked-basis coefficients with the BNT labels. -/
  blockedComparison : BNTBlockedBasisCoefficientComparison data coeffs

namespace BNTLabelTheoremData

variable {data : AlgebraStructureData d D} {Λ : Type*} {O : ℕ → Type*}
  [Fintype Λ] [∀ L : ℕ, AddCommMonoid (O L)] [∀ L : ℕ, Module ℂ (O L)]
  [∀ L : ℕ, Mul (O L)] (H : BNTLabelTheoremData data Λ O)

/-- The BNT-label coefficients in theorem data are traces of powers of the
length-independent chi matrices.

Source: arXiv:1606.00608, Theorem IV.13(ii), lines 972--985 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem coeff_eq_trace_pow (L : ℕ) (hL : 0 < L) (α β γ : Λ) :
    H.coeffs.coeff L α β γ =
      (H.positiveChi.chi.matrix α β γ ^ L).trace :=
  H.positiveChi.eq_trace_pow L hL α β γ

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

/-- The BNT product expansion with the coefficients written as traces of the
length-independent chi matrices. -/
theorem same_length_product_eq_sum_chi_trace_pow
    (L : ℕ) (hL : 0 < L) (α β : Λ) :
    H.operators.operator L α * H.operators.operator L β =
      ∑ γ : Λ, (H.positiveChi.chi.matrix α β γ ^ L).trace •
        H.operators.operator L γ :=
  H.sameLengthProduct.eq_sum_chi_trace_pow H.positiveChi L hL α β

/-- The idempotent scalar identity with length-one coefficients written as
traces of the chi matrices. -/
theorem idempotent_eq_sum_chi_trace (γ : Λ) :
    H.traceScalars.traceScalar γ =
      ∑ α : Λ, ∑ β : Λ,
        (H.positiveChi.chi.matrix α β γ).trace *
          (H.traceScalars.traceScalar α * H.traceScalars.traceScalar β) :=
  H.idempotent.eq_sum_chi_trace H.positiveChi γ

/-- The blocked-basis coefficients obtained from BNT-label theorem data are
traces of powers of the pulled-back BNT-label chi matrices. -/
theorem blocked_coeff_eq_trace_pow
    (n : ℕ) (hn : 0 < n)
    (i j : AlgebraStructureData.BlockedIndex data n)
    (k : AlgebraStructureData.BlockedIndex data (2 * n)) :
    data.blockedStructureCoefficients n i j k =
      (H.positiveChi.chi.matrix
        (H.blockedComparison.sourceLabel n hn i)
        (H.blockedComparison.sourceLabel n hn j)
        (H.blockedComparison.targetLabel n hn k) ^ n).trace :=
  H.blockedComparison.blocked_coeff_eq_trace_pow H.positiveChi n hn i j k

/-- The positive blocked chi witness obtained from the BNT-label theorem data
and the blocked-basis comparison. -/
def toPositiveBlockedStructureChiTracePowerForm :
    AlgebraStructureData.PositiveBlockedStructureChiTracePowerForm data :=
  H.blockedComparison.toPositiveBlockedStructureChiTracePowerForm H.positiveChi

end BNTLabelTheoremData

end MPOTensor
