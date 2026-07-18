/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingBondEtaCyclicTransport

/-!
# Boundary trace of cyclic neighboring operators

This file computes the two-boundary edge contraction used after the cyclic
neighboring-operator identity.  Tracing two adjacent boundary sites fully
traces the neighboring operator on the middle edge and leaves one partial
trace on each adjacent edge.  An explicit rank-one factorization of the middle
trace separates the two boundary sector sums.

## Main declarations

* `Matrix.EtaRankOneTraceFactorization`: an explicit factorization
  $\operatorname{tr}(\eta_{q,h})=a_qb_h$ for the neighboring family.
* `Matrix.etaTwoBoundaryContraction_eq_separated`: separation of the two
  boundary sector sums.
* `Matrix.eta_fourth_region_trace_formula`: the direct-sum formula with the
  untouched bulk neighboring product.

## References

* arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1606 and
  1613--1617.
-/

open scoped BigOperators Kronecker Matrix

namespace Matrix

/-- An explicit rank-one trace factorization of a cyclic neighboring family:
$\operatorname{tr}(\eta_{q,h})=a_qb_h$ and $\sum_q a_qb_q=1$.

**Scope restriction:** this structure records the factorization as an
assumption; it does not derive it from zero correlation length.  This
restriction is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, line 1613. -/
structure EtaRankOneTraceFactorization {K : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ) where
  /-- The left factors $a_q$ in
  $\operatorname{tr}(\eta_{q,h})=a_qb_h$.

  Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, line 1613. -/
  a : Fin K → ℝ
  /-- The right factors $b_h$ in
  $\operatorname{tr}(\eta_{q,h})=a_qb_h$.

  Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, line 1613. -/
  b : Fin K → ℝ
  /-- The trace factorization
  $\operatorname{tr}(\eta_{q,h})=a_qb_h$.

  Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, line 1613. -/
  trace_eta : ∀ q h, (η q h).trace = ((a q * b h : ℝ) : ℂ)
  /-- The normalization $\sum_q a_qb_q=1$ accompanying the source
  factorization.

  Source: arXiv:1606.00608, Appendix C.2, lines 1395--1402. -/
  sum_mul : ∑ q, a q * b q = 1

/-- The indices on the untouched neighboring edges of a nonempty open chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1615--1617. -/
abbrev EtaRetainedBulkIndex {K L : ℕ} (dl dr : Fin K → ℕ)
    (hL : 1 ≤ L) (k : Fin L → Fin K) :=
  (n : Fin (L - 1)) →
    EtaEdgeIndex dl dr
      (k ⟨(n : ℕ), by omega⟩) (k ⟨(n : ℕ) + 1, by omega⟩)

/-- The tensor product of the neighboring operators on the untouched bulk
edges.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1615--1617. -/
noncomputable def etaRetainedBulkProduct {K L : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ)
    (hL : 1 ≤ L) (k : Fin L → Fin K) :
    Matrix (EtaRetainedBulkIndex dl dr hL k)
      (EtaRetainedBulkIndex dl dr hL k) ℂ :=
  fun x y ↦ ∏ n : Fin (L - 1),
    η (k ⟨(n : ℕ), by omega⟩) (k ⟨(n : ℕ) + 1, by omega⟩) (x n) (y n)

/-- The contraction obtained by tracing two adjacent boundary sites: the
middle neighboring operator is fully traced, while the two adjacent operators
retain their right and left partial traces.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1613--1617. -/
noncomputable def etaTwoBoundaryContraction {K : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ)
    (kFirst kLast : Fin K) :
    Matrix (Fin (dr kLast) × Fin (dl kFirst))
      (Fin (dr kLast) × Fin (dl kFirst)) ℂ :=
  ∑ q, ∑ h, (η q h).trace •
    (partialTraceRight (η kLast q) ⊗ₖ partialTraceLeft (η h kFirst))

/-- The separated right and left boundary sums appearing in the source
fourth-region formula.  The right partial trace acts on the last retained
right factor, and the left partial trace acts on the first retained left
factor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1615--1617. -/
noncomputable def etaSeparatedBoundary {K : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ)
    (factor : EtaRankOneTraceFactorization dl dr η)
    (kFirst kLast : Fin K) :
    Matrix (Fin (dr kLast) × Fin (dl kFirst))
      (Fin (dr kLast) × Fin (dl kFirst)) ℂ :=
  (∑ q, ((factor.a q : ℂ) • partialTraceRight (η kLast q))) ⊗ₖ
    (∑ h, ((factor.b h : ℂ) • partialTraceLeft (η h kFirst)))

/-- The rank-one trace identity separates the double boundary contraction:
\[
\sum_{q,h}\operatorname{tr}(\eta_{q,h})
  \bigl(\operatorname{tr}_{L_q}(\eta_{k,q})\otimes
        \operatorname{tr}_{R_h}(\eta_{h,l})\bigr)
=
\left(\sum_q a_q\operatorname{tr}_{L_q}(\eta_{k,q})\right)
\otimes
\left(\sum_h b_h\operatorname{tr}_{R_h}(\eta_{h,l})\right).
\]

**Scope restriction:** the rank-one trace factorization is assumed.
This theorem does not derive it from zero correlation length and does not
assert a Markov decomposition or saturation of the area law.  This restriction
is documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1613--1617. -/
theorem etaTwoBoundaryContraction_eq_separated
    {K : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ)
    (factor : EtaRankOneTraceFactorization dl dr η)
    (kFirst kLast : Fin K) :
    etaTwoBoundaryContraction dl dr η kFirst kLast =
      etaSeparatedBoundary dl dr η factor kFirst kLast := by
  classical
  change (∑ q, ∑ h, (η q h).trace •
      (partialTraceRight (η kLast q) ⊗ₖ partialTraceLeft (η h kFirst))) =
    (∑ q, ((factor.a q : ℂ) • partialTraceRight (η kLast q))) ⊗ₖ
      (∑ h, ((factor.b h : ℂ) • partialTraceLeft (η h kFirst)))
  ext x y
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    factor.trace_eta, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [Complex.ofReal_mul]
  ring

/-- The first retained sector of a nonempty open chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1615--1617. -/
def etaRetainedFirstSector {K L : ℕ} (hL : 1 ≤ L)
    (k : Fin L → Fin K) : Fin K :=
  k ⟨0, by omega⟩

/-- The last retained sector of a nonempty open chain.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1615--1617. -/
def etaRetainedLastSector {K L : ℕ} (hL : 1 ≤ L)
    (k : Fin L → Fin K) : Fin K :=
  k ⟨L - 1, by omega⟩

/-- **Conditional fourth-region trace formula.**  For every retained sector
configuration, the untouched bulk neighboring product tensored with the
two-boundary contraction equals the same bulk product tensored with the
separated $a$- and $b$-weighted boundary sums.  Taking the dependent direct
sum gives the displayed formula for $\widetilde\sigma_{ABC}$.

The contraction is the edge-coordinate form of tracing two boundary sites of
the longer cyclic chain used at source line 1613.  It fully traces the middle
$\eta_{q,h}$ and retains `Matrix.partialTraceRight` and
`Matrix.partialTraceLeft` on the adjacent operators.  The notation at source
line 1616 suppresses these two partial-trace symbols.

**Scope restriction:** the theorem assumes
$\operatorname{tr}(\eta_{q,h})=a_qb_h$ explicitly.  It neither proves the
source replacement of a one-site marginal using zero correlation length nor
formalizes Proposition `4to2`, a Markov decomposition, or saturation of the
area law.  This restriction is documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1606 and
1613--1617. -/
theorem eta_fourth_region_trace_formula
    {K L : ℕ} (dl dr : Fin K → ℕ)
    (η : (q h : Fin K) →
      Matrix (EtaEdgeIndex dl dr q h) (EtaEdgeIndex dl dr q h) ℂ)
    (factor : EtaRankOneTraceFactorization dl dr η) (hL : 1 ≤ L) :
    (Matrix.blockDiagonal' fun k : Fin L → Fin K ↦
      etaRetainedBulkProduct dl dr η hL k ⊗ₖ
        etaTwoBoundaryContraction dl dr η
          (etaRetainedFirstSector hL k) (etaRetainedLastSector hL k)) =
      Matrix.blockDiagonal' fun k : Fin L → Fin K ↦
        etaRetainedBulkProduct dl dr η hL k ⊗ₖ
          etaSeparatedBoundary dl dr η factor
            (etaRetainedFirstSector hL k) (etaRetainedLastSector hL k) := by
  classical
  apply congrArg Matrix.blockDiagonal'
  funext k
  rw [etaTwoBoundaryContraction_eq_separated]

end Matrix
