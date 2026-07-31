/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveSectorRestriction
import TNLean.MPS.MPDO.PhysicalSectorTraceActions
import TNLean.Channel.MaximalOverlap

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
* `MPOTensor.PhysicalSectorFactorization.cyclicActiveTwoStepBoundaryContraction_eq_separated`.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The trace of a positive neighboring operator is the complexification of
the corresponding cyclic-active trace-matrix entry.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1455.

**Scope restriction (cyclic-active restriction):** This equality is recorded on the
positive-length cyclic support used in the three-boundary coefficient.  It
does not identify the restricted trace matrix with the unreduced Beigi
matrix.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (a b : F.CyclicActiveSector) :
    (F.neighboringOperator a b).trace =
      (F.cyclicActiveSectorTraceMatrix a b : ℂ) := by
  change (F.neighboringOperator a b).trace =
    ((F.neighboringOperator a b).trace.re : ℂ)
  exact (hpos a b).isHermitian.trace_eq_ofReal_re

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

**Scope restriction (cyclic-active restriction):** The sum is restricted to sectors
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
  simp_rw [F.neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix hpos]
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

**Scope restriction (cyclic-active restriction):** This is the normalized two-step
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
  simp_rw [F.neighboringOperator_trace_eq_cyclicActiveSectorTraceMatrix hpos,
    Matrix.smul_apply]
  norm_cast

/-- Summing the partial traces of the three-site closures over the
intermediate cyclic-active sector leaves the outer boundary operator with
coefficient $(T_C^2)_{q,h}$.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This is the three-boundary
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

/-- The unnormalized fourth-region boundary contraction on cyclic-active
sectors.  Its coefficient is the restricted two-step trace matrix
$T_C^2$.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The coefficient is the square of
the restricted trace matrix.  It is not replaced by the one-step matrix
printed at source line 1613.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveUnnormalizedTwoStepBoundaryContraction
    (F : PhysicalSectorFactorization K)
    (kFirst kLast : F.CyclicActiveSector) :
    Matrix (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst))
      (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst)) ℂ :=
  ∑ q, ∑ h,
    ((F.cyclicActiveSectorTraceMatrix ^ 2) q h : ℂ) •
      (Matrix.partialTraceRight (F.neighboringOperator kLast q) ⊗ₖ
        Matrix.partialTraceLeft (F.neighboringOperator h kFirst))

/-- The fourth-region boundary contraction with the normalized two-step
coefficient on cyclic-active sectors.  The two outer neighboring operators
retain one partial trace each.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The coefficient is the square of
the restricted normalized trace matrix, not the one-step coefficient printed
at source line 1613.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveTwoStepBoundaryContraction
    (F : PhysicalSectorFactorization K) (lam : ℝ)
    (kFirst kLast : F.CyclicActiveSector) :
    Matrix (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst))
      (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst)) ℂ :=
  ∑ q, ∑ h,
    (((lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2) q h : ℂ) •
      (Matrix.partialTraceRight (F.neighboringOperator kLast q) ⊗ₖ
        Matrix.partialTraceLeft (F.neighboringOperator h kFirst))

/-- Rescaling the restricted trace matrix by a positive scalar extracts the
corresponding square from the unnormalized fourth-region boundary.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This identity relates $T_C^2$ to
$(\lambda^{-1}T_C)^2$ and does not identify either square with $T_C$.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveUnnormalizedTwoStepBoundaryContraction_eq_smul
    (F : PhysicalSectorFactorization K) (lam : ℝ) (hlam : 0 < lam)
    (kFirst kLast : F.CyclicActiveSector) :
    F.cyclicActiveUnnormalizedTwoStepBoundaryContraction kFirst kLast =
      ((lam : ℂ) ^ 2) •
        F.cyclicActiveTwoStepBoundaryContraction lam kFirst kLast := by
  classical
  ext x y
  simp only [cyclicActiveUnnormalizedTwoStepBoundaryContraction,
    cyclicActiveTwoStepBoundaryContraction, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hcoeff :
      (F.cyclicActiveSectorTraceMatrix ^ 2) q h =
        lam ^ 2 *
          ((lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2) q h := by
    rw [show F.cyclicActiveSectorTraceMatrix ^ 2 =
        F.cyclicActiveSectorTraceMatrix * F.cyclicActiveSectorTraceMatrix by
          simp [pow_two],
      show (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
        (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) *
          (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) by simp [pow_two],
      Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    field_simp [ne_of_gt hlam]
  rw [hcoeff, Complex.ofReal_mul]
  push_cast
  ring

/-- The separated boundary operators associated with positive factors of the
normalized two-step cyclic-active coefficient.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The factors belong to
$(\lambda^{-1}T_C)^2$ and do not factor the one-step matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveSeparatedBoundary
    (F : PhysicalSectorFactorization K)
    (a b : F.CyclicActiveSector → ℝ)
    (kFirst kLast : F.CyclicActiveSector) :
    Matrix (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst))
      (Fin (F.rightDim kLast) × Fin (F.leftDim kFirst)) ℂ :=
  (∑ q, ((a q : ℂ) •
      Matrix.partialTraceRight (F.neighboringOperator kLast q))) ⊗ₖ
    (∑ h, ((b h : ℂ) •
      Matrix.partialTraceLeft (F.neighboringOperator h kFirst)))

/-- A rank-one factorization of the normalized two-step coefficient separates
the two surviving fourth-region boundaries.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** This theorem uses a factorization
of $(\lambda^{-1}T_C)^2$.  It neither identifies $T_C$ with its square nor
uses the unreduced sector matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveTwoStepBoundaryContraction_eq_separated
    (F : PhysicalSectorFactorization K) (lam : ℝ)
    (a b : F.CyclicActiveSector → ℝ)
    (hab : (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
      Matrix.vecMulVec a b)
    (kFirst kLast : F.CyclicActiveSector) :
    F.cyclicActiveTwoStepBoundaryContraction lam kFirst kLast =
      F.cyclicActiveSeparatedBoundary a b kFirst kLast := by
  classical
  ext x y
  simp only [cyclicActiveTwoStepBoundaryContraction,
    cyclicActiveSeparatedBoundary, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hentry := congrFun (congrFun hab q) h
  simp only [Matrix.vecMulVec_apply] at hentry
  rw [hentry, Complex.ofReal_mul]
  ring

end MPOTensor.PhysicalSectorFactorization
