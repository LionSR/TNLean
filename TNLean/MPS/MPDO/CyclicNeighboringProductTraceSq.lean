/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveSuffixMarginal

/-!
# Cyclic neighboring product trace-squared identity

The trace of the square of the cyclic tensor product of neighboring operators
equals the product of the traces of their squares.

## Reference

* arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499.
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The trace of the square of the cyclic tensor product of neighboring
operators equals the product of the traces of their squares.

The proof expands `trace(M²) = ∑_{x,y} M_{x,y}·M_{y,x}`, reindexes through
`cyclicEdgeEquiv` to expose the Kronecker-product entries, then uses
`Finset.prod_univ_sum` to swap sums and products.  The resulting inner sums
give `(η_n²)(x_n, x_n)`, whose sum over `x_n` is `trace(η_n²)`.

Source: arXiv:1606.00608, Appendix C.2, Lemma C.5, lines 1473--1499. -/
theorem trace_cyclicNeighboringProduct_sq_eq_prod_trace_sq
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    Matrix.trace ((F.cyclicNeighboringProduct k) ^ 2) =
      ∏ i : Fin N, Matrix.trace ((F.neighboringOperator (k i) (k (i + 1))) ^ 2) := by
  classical
  -- Rewrite only the left side to expand trace(M²)
  have h_expand : Matrix.trace ((F.cyclicNeighboringProduct k) ^ 2) =
      ∑ x : F.SectorChainFiber k, ∑ y : F.SectorChainFiber k,
        F.cyclicNeighboringProduct k x y * F.cyclicNeighboringProduct k y x := by
    simp [Matrix.trace, sq, Matrix.diag_apply, Matrix.mul_apply]
  rw [h_expand]
  calc
    (∑ x : F.SectorChainFiber k, ∑ y : F.SectorChainFiber k,
        F.cyclicNeighboringProduct k x y *
          F.cyclicNeighboringProduct k y x) =
      ∑ x : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
        ∑ y : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
          F.cyclicNeighboringProduct k
            ((F.cyclicEdgeEquiv k).symm x) ((F.cyclicEdgeEquiv k).symm y) *
          F.cyclicNeighboringProduct k
            ((F.cyclicEdgeEquiv k).symm y) ((F.cyclicEdgeEquiv k).symm x) := by
      apply Fintype.sum_equiv (F.cyclicEdgeEquiv k)
      intro x
      apply Fintype.sum_equiv (F.cyclicEdgeEquiv k)
      intro y
      simp [Equiv.symm_apply_apply]
    _ = ∑ x : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
          ∑ y : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
            (∏ n : Fin N,
              F.neighboringOperator (k n) (k (n + 1)) (x n) (y n)) *
            (∏ n : Fin N,
              F.neighboringOperator (k n) (k (n + 1)) (y n) (x n)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [cyclicNeighboringProduct]
      congr 1
      · refine Finset.prod_congr rfl fun n _ => ?_
        have hx := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) n
        have hy := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply y) n
        simpa only [cyclicEdgeEquiv_apply] using
          congrArg₂ (F.neighboringOperator (k n) (k (n + 1))) hx hy
      · refine Finset.prod_congr rfl fun n _ => ?_
        have hx := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply y) n
        have hy := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) n
        simpa only [cyclicEdgeEquiv_apply] using
          congrArg₂ (F.neighboringOperator (k n) (k (n + 1))) hx hy
    _ = ∑ x : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
          ∑ y : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
            ∏ n : Fin N,
              (F.neighboringOperator (k n) (k (n + 1)) (x n) (y n) *
                F.neighboringOperator (k n) (k (n + 1)) (y n) (x n)) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp [Finset.prod_mul_distrib]
    _ = ∑ x : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
          ∏ n : Fin N,
            ∑ (y_n : F.NeighborIndex (k n) (k (n + 1))),
              F.neighboringOperator (k n) (k (n + 1)) (x n) y_n *
                F.neighboringOperator (k n) (k (n + 1)) y_n (x n) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∑ x : ((n : Fin N) → F.NeighborIndex (k n) (k (n + 1))),
          ∏ n : Fin N,
            ((F.neighboringOperator (k n) (k (n + 1))) ^ 2) (x n) (x n) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      refine Finset.prod_congr rfl fun n _ => ?_
      simp only [sq, Matrix.mul_apply]
    _ = ∏ n : Fin N,
          ∑ (x_n : F.NeighborIndex (k n) (k (n + 1))),
            ((F.neighboringOperator (k n) (k (n + 1))) ^ 2) x_n x_n := by
      simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ n : Fin N,
          Matrix.trace ((F.neighboringOperator (k n) (k (n + 1))) ^ 2) := by
      simp only [Matrix.trace, Matrix.diag_apply]

end MPOTensor.PhysicalSectorFactorization
