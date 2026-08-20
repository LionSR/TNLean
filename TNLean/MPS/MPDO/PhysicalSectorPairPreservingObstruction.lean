/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Trace obstruction to preserving every pair of physical sectors

For a physical-sector factorization, fix the two outer sectors `k` and `h`.
The middle subspins of two sites carry the neighboring operator
\(\eta_{k,h}\).  The middle subspins of four sites carry
\[
  \Theta_{k,h}
    = \bigoplus_{l,m}
        \eta_{k,l}\otimes\eta_{l,m}\otimes\eta_{m,h}.
\]
If a trace-preserving map sends each \(\eta_{k,h}\) to the corresponding
\(\Theta_{k,h}\), or conversely, then the trace matrix
\(C_{k,h}=\operatorname{tr}(\eta_{k,h})\) satisfies \(C=C^3\).

This is the trace-level condition imposed by a two-to-four-site map which
preserves the two outer sector labels.  It is stronger than the identity
\(C^2=C^3\) obtained by comparing three and four sites.  A channel which
mixes or coarsens the sector labels need not satisfy it.

## Reference

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, neighboring operators at lines 1435--1455, the
  sector-controlled maps at lines 1522--1555, and their second iterates at
  lines 1821--1825
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The three neighboring subspin pairs between fixed outer sectors of four
physical sites.  The indices `l` and `m` are the two intermediate physical
sectors.

Derived from arXiv:1606.00608, Appendix C.2, lines 1435--1455, by the
iteration at lines 1821--1825. -/
abbrev FourSiteMiddleIndex (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :=
  Σ l : Fin F.sectorCount, Σ m : Fin F.sectorCount,
    NeighborIndex F k l × (NeighborIndex F l m × NeighborIndex F m h)

/-- The four-site neighboring operator with fixed outer sectors:
\[
  \Theta_{k,h}
    = \bigoplus_{l,m}
        \eta_{k,l}\otimes\eta_{l,m}\otimes\eta_{m,h}.
\]

Derived from arXiv:1606.00608, Appendix C.2, lines 1435--1455, by the
iteration at lines 1821--1825. -/
noncomputable def fourSiteNeighboringOperator
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    Matrix (FourSiteMiddleIndex F k h) (FourSiteMiddleIndex F k h) ℂ :=
  Matrix.blockDiagonal' fun l ↦
    Matrix.blockDiagonal' fun m ↦
      F.neighboringOperator k l ⊗ₖ
        (F.neighboringOperator l m ⊗ₖ F.neighboringOperator m h)

/-- The complex trace matrix \(C_{k,h}=\operatorname{tr}(\eta_{k,h})\).

Source: arXiv:1606.00608, Appendix C.2, equation `StochT`, lines 1452--1456. -/
noncomputable def neighboringTraceMatrix (F : PhysicalSectorFactorization K) :
    Matrix (Fin F.sectorCount) (Fin F.sectorCount) ℂ :=
  fun k h ↦ (F.neighboringOperator k h).trace

/-- The `(k,h)` entry of the trace matrix is
\(\operatorname{tr}(\eta_{k,h})\).

Source: arXiv:1606.00608, Appendix C.2, equation `StochT`, lines 1452--1456. -/
@[simp] theorem neighboringTraceMatrix_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    F.neighboringTraceMatrix k h = (F.neighboringOperator k h).trace :=
  rfl

/-- The trace of \(\Theta_{k,h}\) is the `(k,h)` entry of \(C^3\).

Derived from arXiv:1606.00608, Appendix C.2, lines 1527--1535, by the
iteration at lines 1821--1825. -/
theorem trace_fourSiteNeighboringOperator
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount) :
    (F.fourSiteNeighboringOperator k h).trace =
      (F.neighboringTraceMatrix ^ 3) k h := by
  rw [fourSiteNeighboringOperator, Matrix.trace_blockDiagonal']
  simp only [Matrix.trace_blockDiagonal', Matrix.trace_kronecker]
  change (∑ l, ∑ m, F.neighboringTraceMatrix k l *
      (F.neighboringTraceMatrix l m * F.neighboringTraceMatrix m h)) = _
  rw [pow_three', Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- A trace-preserving family which sends each four-site neighboring operator
to the two-site neighboring operator forces \(C=C^3\).  The common indices
`k,h` express preservation of the two outer physical sectors.

This is derived from trace preservation applied to the twice-iterated
sectorwise maps in arXiv:1606.00608, Appendix C.2, lines 1522--1555 and
1821--1825. -/
theorem neighboringTraceMatrix_eq_pow_three_of_pairwise_coarsening
    (F : PhysicalSectorFactorization K)
    (S : (k h : Fin F.sectorCount) →
      Matrix (FourSiteMiddleIndex F k h) (FourSiteMiddleIndex F k h) ℂ →ₗ[ℂ]
        Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ)
    (htrace : ∀ k h X, (S k h X).trace = X.trace)
    (hmap : ∀ k h,
      S k h (F.fourSiteNeighboringOperator k h) = F.neighboringOperator k h) :
    F.neighboringTraceMatrix = F.neighboringTraceMatrix ^ 3 := by
  ext k h
  rw [neighboringTraceMatrix_apply, ← hmap k h, htrace k h,
    F.trace_fourSiteNeighboringOperator]

/-- A trace-preserving family which sends each two-site neighboring operator
to the four-site neighboring operator forces \(C=C^3\).  The common indices
`k,h` express preservation of the two outer physical sectors.

This is derived from trace preservation applied to the twice-iterated
sectorwise maps in arXiv:1606.00608, Appendix C.2, lines 1522--1555 and
1821--1825. -/
theorem neighboringTraceMatrix_eq_pow_three_of_pairwise_refinement
    (F : PhysicalSectorFactorization K)
    (T : (k h : Fin F.sectorCount) →
      Matrix (NeighborIndex F k h) (NeighborIndex F k h) ℂ →ₗ[ℂ]
        Matrix (FourSiteMiddleIndex F k h) (FourSiteMiddleIndex F k h) ℂ)
    (htrace : ∀ k h X, (T k h X).trace = X.trace)
    (hmap : ∀ k h,
      T k h (F.neighboringOperator k h) = F.fourSiteNeighboringOperator k h) :
    F.neighboringTraceMatrix = F.neighboringTraceMatrix ^ 3 := by
  ext k h
  rw [neighboringTraceMatrix_apply, ← htrace k h,
    hmap k h, F.trace_fourSiteNeighboringOperator]

end MPOTensor.PhysicalSectorFactorization
