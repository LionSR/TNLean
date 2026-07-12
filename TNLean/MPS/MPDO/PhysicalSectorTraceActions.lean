/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorClosureTwo

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

end MPOTensor.PhysicalSectorFactorization
