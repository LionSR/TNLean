/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveSectorRestriction
import TNLean.MPS.MPDO.PhysicalSectorTraceActions

/-!
# Three-boundary trace on cyclic-active sectors

This file identifies the coefficient obtained by summing the three-site
partial trace over the intermediate cyclic-active sector.  If
$T_{q,h}=\operatorname{Re}\operatorname{tr}(\eta_{q,h})$, then positivity of
the neighboring operators gives
\[
  \sum_r \operatorname{tr}(\eta_{q,r})
    \operatorname{tr}(\eta_{r,h})=(T^2)_{q,h}.
\]
Consequently, the corresponding sum of three-site partial traces is
$(T^2)_{q,h}$ times the outer boundary operator.

These are coordinate identities.  They do not identify $T$ with $T^2$, do
not assert that $T$ has rank one, and do not construct a quantum Markov
decomposition.

## Main results

* `MPOTensor.PhysicalSectorFactorization.sum_cyclicActive_trace_mul_trace_eq_pow_two`.
* `MPOTensor.PhysicalSectorFactorization.sum_cyclicActive_normalized_trace_mul_trace_eq_pow_two`.
* `MPOTensor.PhysicalSectorFactorization.sum_cyclicActive_partialTraceRight_threeSiteSectorClosure`.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The two fully traced middle neighboring operators give the square of the
cyclic-active trace matrix:
\[
  \sum_{r\in C}\operatorname{tr}(\eta_{q,r})
    \operatorname{tr}(\eta_{r,h})=(T_C^2)_{q,h}.
\]

Positive semidefiniteness is used only to replace each complex trace by the
complexification of its real part.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** The sum is restricted to sectors
on positive-length directed cycles and yields the square of the restricted
trace matrix.  It does not replace this square by the one-step trace matrix
printed at source line 1613.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sum_cyclicActive_trace_mul_trace_eq_pow_two
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (q h : F.CyclicActiveSector) :
    ∑ r : F.CyclicActiveSector,
        (F.neighboringOperator q r).trace *
          (F.neighboringOperator r h).trace =
      ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) := by
  classical
  rw [pow_two, Matrix.mul_apply]
  have htrace (a b : F.CyclicActiveSector) :
      (F.neighboringOperator a b).trace =
        (F.cyclicActiveSectorTraceMatrix a b : ℂ) := by
    change (F.neighboringOperator a b).trace =
      ((F.neighboringOperator a b).trace.re : ℂ)
    exact (hpos a b).isHermitian.trace_eq_ofReal_re
  simp_rw [htrace]
  norm_cast

/-- After rescaling each traced neighboring edge by \(\lambda^{-1}\), the two
fully traced middle edges give the square of the normalized cyclic-active
trace matrix:
\[
  \sum_{r\in C}\lambda^{-1}\operatorname{tr}(\eta_{q,r})
    \lambda^{-1}\operatorname{tr}(\eta_{r,h})
  =\bigl((\lambda^{-1}T_C)^2\bigr)_{q,h}.
\]

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This is the normalized two-step
coefficient on the positive-length cyclic support.  It does not identify the
one-step matrix with its square or with the unreduced Beigi matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sum_cyclicActive_normalized_trace_mul_trace_eq_pow_two
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (lam : ℝ) (q h : F.CyclicActiveSector) :
    ∑ r : F.CyclicActiveSector,
        ((lam⁻¹ : ℝ) : ℂ) * (F.neighboringOperator q r).trace *
          (((lam⁻¹ : ℝ) : ℂ) * (F.neighboringOperator r h).trace) =
      ((((lam⁻¹ : ℝ) • F.cyclicActiveSectorTraceMatrix) ^ 2) q h : ℂ) := by
  classical
  rw [pow_two, Matrix.mul_apply]
  have htrace (a b : F.CyclicActiveSector) :
      (F.neighboringOperator a b).trace =
        (F.cyclicActiveSectorTraceMatrix a b : ℂ) := by
    change (F.neighboringOperator a b).trace =
      ((F.neighboringOperator a b).trace.re : ℂ)
    exact (hpos a b).isHermitian.trace_eq_ofReal_re
  simp_rw [htrace, Matrix.smul_apply]
  push_cast

/-- Summing the partial traces of the three-site closures over the
intermediate cyclic-active sector leaves the outer boundary operator with
coefficient $(T_C^2)_{q,h}$.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This is the three-boundary
coordinate identity for the positive-length cyclic support.  It proves only
the appearance of the two-step coefficient; the identification with the
source-ZCL reduced state and the Markov decomposition remain separate.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sum_cyclicActive_partialTraceRight_threeSiteSectorClosure
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (q h : F.CyclicActiveSector) (X : Matrix (Fin D) (Fin D) ℂ) :
    ∑ r : F.CyclicActiveSector,
        Matrix.partialTraceRight (F.threeSiteSectorClosure q r h X) =
      ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) •
        F.boundaryOperator q h X := by
  classical
  simp_rw [F.partialTraceRight_threeSiteSectorClosure]
  rw [← Finset.sum_smul, F.sum_cyclicActive_trace_mul_trace_eq_pow_two hpos q h]

end MPOTensor.PhysicalSectorFactorization
