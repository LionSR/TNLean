/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalSectorClosureTwo
import TNLean.MPS.MPDO.PhysicalSectorClosureThree

/-!
# Partial traces of physical-sector closures

This file computes the partial trace of the two-site physical closure in fixed
sectors.  Once the physical indices have been regrouped into their two outer
factors and the neighboring pair, tracing the neighboring pair multiplies the
boundary operator by the trace of the neighboring operator.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1518--1522
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Tracing the neighboring factors of a fixed-sector two-site closure leaves
the boundary operator multiplied by the trace of the neighboring operator:
\[
  \operatorname{tr}_{B_k^R\otimes B_h^L}
    \bigl(\mathcal K_{2;k,h}(X)\bigr)
  =\operatorname{tr}(\eta_{k,h})B_{k,h}(X).
\]

This is the first partial-trace calculation in the construction of
$\mathcal T$ in Proposition C.7.

Source: arXiv:1606.00608, Appendix C.2, lines 1518--1522. -/
theorem partialTraceRight_twoSiteSectorClosure
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.partialTraceRight (F.twoSiteSectorClosure k h X) =
      (F.neighboringOperator k h).trace • F.boundaryOperator k h X := by
  rw [F.twoSiteSectorClosure_eq, Matrix.partialTraceRight_kronecker]

/-- Under the rank-one trace factorization, the two-site partial trace has
coefficient \(a_kb_h\).

Source: arXiv:1606.00608, Appendix C.2, lines 1518--1522. -/
theorem NeighboringTraceFactorization.partialTraceRight_twoSiteSectorClosure
    {F : PhysicalSectorFactorization K} (H : NeighboringTraceFactorization F)
    (k h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.partialTraceRight (F.twoSiteSectorClosure k h X) =
      ((H.a k * H.b h : ℝ) : ℂ) • F.boundaryOperator k h X := by
  rw [F.partialTraceRight_twoSiteSectorClosure, H.trace_neighboringOperator]

/-- Tracing the four middle factors of a fixed-sector three-site closure
leaves the boundary operator multiplied by the traces of the two neighboring
operators.

Source: arXiv:1606.00608, Appendix C.2, lines 1547--1555. -/
theorem partialTraceRight_threeSiteSectorClosure
    (F : PhysicalSectorFactorization K) (k l h : Fin F.sectorCount)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.partialTraceRight (F.threeSiteSectorClosure k l h X) =
      ((F.neighboringOperator k l).trace *
          (F.neighboringOperator l h).trace) • F.boundaryOperator k h X := by
  rw [F.threeSiteSectorClosure_eq, Matrix.partialTraceRight_kronecker,
    Matrix.trace_kronecker]

/-- Summing the three-site partial-trace coefficients over the intermediate
sector gives \(a_kb_h\).

Source: arXiv:1606.00608, Appendix C.2, lines 1547--1555. -/
theorem NeighboringTraceFactorization.sum_threeSite_trace_coefficients
    {F : PhysicalSectorFactorization K} (H : NeighboringTraceFactorization F)
    (k h : Fin F.sectorCount) :
    ∑ l, (F.neighboringOperator k l).trace *
        (F.neighboringOperator l h).trace = ((H.a k * H.b h : ℝ) : ℂ) := by
  simp_rw [H.trace_neighboringOperator]
  norm_cast
  calc
    ∑ l, H.a k * H.b l * (H.a l * H.b h) =
        H.a k * (∑ l, H.a l * H.b l) * H.b h := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = H.a k * H.b h := by rw [H.sum_mul]; ring

end MPOTensor.PhysicalSectorFactorization
