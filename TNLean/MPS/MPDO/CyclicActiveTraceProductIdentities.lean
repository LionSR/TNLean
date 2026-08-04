/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorProductRealization

/-!
# Cyclic-active trace product identities

Two fundamental trace identities for the cyclic tensor product of
neighboring operators in a physical-sector factorization:
`tr(⊗_n η_{k_n,k_{n+1}}) = ∏_n tr(η_{k_n,k_{n+1}})`
and its squared variant `tr((⊗_n η_{k_n,k_{n+1}})²) = ∏_n tr(η_{k_n,k_{n+1}}²)`.

These are the coefficient-extraction lemmas needed in the Lemma C.5
Case-I route (arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines
1473--1499; cyclic direct-sum form, lines 1580--1593).

## Main declarations

* `trace_cyclicNeighboringProduct_eq_prod_trace`: trace of a cyclic
  tensor product equals the product of individual traces.
* `trace_cyclicNeighboringProduct_sq_eq_prod_trace_sq`: trace of the
  square of a cyclic tensor product equals the product of individual
  squared traces.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The trace of the cyclic tensor product of neighboring operators equals
the product of their individual traces.

Source: arXiv:1606.00608, Appendix C.2, equation `sigmaNK2`, lines
1586--1589. -/
theorem trace_cyclicNeighboringProduct_eq_prod_trace
    (F : PhysicalSectorFactorization K) {N : ℕ} [NeZero N]
    (k : Fin N → Fin F.sectorCount) :
    Matrix.trace (F.cyclicNeighboringProduct k) =
      ∏ i : Fin N, Matrix.trace (F.neighboringOperator (k i) (k (i + 1))) := by
  classical
  rw [Matrix.trace]
  calc
    (∑ x : F.SectorChainFiber k, Matrix.diag (F.cyclicNeighboringProduct k) x) =
        ∑ x : (i : Fin N) → F.NeighborIndex (k i) (k (i + 1)),
          Matrix.diag (F.cyclicNeighboringProduct k)
            ((F.cyclicEdgeEquiv k).symm x) := by
      apply Fintype.sum_equiv (F.cyclicEdgeEquiv k)
      intro x
      rw [Equiv.symm_apply_apply]
    _ = ∑ x : (i : Fin N) → F.NeighborIndex (k i) (k (i + 1)),
          ∏ i : Fin N, F.neighboringOperator (k i) (k (i + 1)) (x i) (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Matrix.diag_apply, cyclicNeighboringProduct]
      apply Finset.prod_congr rfl
      intro i _
      have hx := congrFun ((F.cyclicEdgeEquiv k).apply_symm_apply x) i
      simpa only [cyclicEdgeEquiv_apply] using
        congrArg₂ (F.neighboringOperator (k i) (k (i + 1))) hx hx
    _ = _ := by
      simp_rw [Matrix.trace, Matrix.diag_apply]
      rw [Finset.prod_univ_sum
        (fun i : Fin N ↦
          (Finset.univ : Finset (F.NeighborIndex (k i) (k (i + 1)))))
        (fun i x ↦ F.neighboringOperator (k i) (k (i + 1)) x x)]
      simp only [Fintype.piFinset_univ]


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
