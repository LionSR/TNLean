/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Two-site closures in fixed physical sectors

This file computes the two-site physical closure of a tensor satisfying the
source-minimal physical-sector factorization from Appendix C.2 of
arXiv:1606.00608.  After restricting the two physical sites to sectors `k`
and `h`, the factors are regrouped as
\[
  ((L_k,R_k),(L_h,R_h))\longmapsto ((L_k,R_h),(R_k,L_h)).
\]
The resulting matrix is the Kronecker product of the outer boundary operator
with the neighboring operator.  This is only an algebraic contraction
identity; no positivity, normalization, or renormalization fixed-point claim
is made.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `etarl`, lines 1381--1388 and
  1441--1450
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Regroup the two fixed-sector physical indices into the two outer factors
and the two neighboring factors:
\[
  ((L_k,R_k),(L_h,R_h))\longmapsto ((L_k,R_h),(R_k,L_h)).
\]

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1388 and 1441--1445. -/
def twoSiteRegroupEquiv (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :
    (SectorIndex F k × SectorIndex F h) ≃
      (BoundaryIndex F k h × NeighborIndex F k h) where
  toFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  invFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  left_inv := by rintro ⟨⟨lk, rk⟩, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨lk, rh⟩, rk, lh⟩; rfl

/-- The inverse regrouping reconstructs the two complete sector indices.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1388 and 1441--1445. -/
@[simp] theorem twoSiteRegroupEquiv_symm_apply
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (x : BoundaryIndex F k h × NeighborIndex F k h) :
    (F.twoSiteRegroupEquiv k h).symm x =
      ((x.1.1, x.2.1), (x.2.2, x.1.2)) :=
  rfl

/-- Embed a pair of fixed-sector physical indices into the two-site index
space of the sector-coordinate tensor.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def twoSiteSectorEmbedding (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :
    SectorIndex F k × SectorIndex F h →
      Fin (Fintype.card (Σ l : Fin F.sectorCount, SectorIndex F l)) ×
        Fin (Fintype.card (Σ l : Fin F.sectorCount, SectorIndex F l)) :=
  fun x ↦ (F.sectorFinEquiv.symm ⟨k, x.1⟩, F.sectorFinEquiv.symm ⟨h, x.2⟩)

/-- The two-site closure restricted to the physical sectors `k,h` and then
regrouped as `((L_k,R_k),(L_h,R_h)) ↦ ((L_k,R_h),(R_k,L_h))`.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1388 and 1441--1450. -/
noncomputable def physicalSectorClosureTwo (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (BoundaryIndex F k h × NeighborIndex F k h)
      (BoundaryIndex F k h × NeighborIndex F k h) ℂ :=
  (physClose2 F.sectorCoordinateTensor X).submatrix
    (F.twoSiteSectorEmbedding k h ∘ (F.twoSiteRegroupEquiv k h).symm)
    (F.twoSiteSectorEmbedding k h ∘ (F.twoSiteRegroupEquiv k h).symm)

/-- For arbitrary virtual boundary matrix `X`, the fixed-sector two-site
closure factors into its outer boundary contraction and its neighboring
contraction:
\[
  \mathcal K_{2;k,h}(X)=B_{k,h}(X)\otimes\eta_{k,h}.
\]

This theorem uses only the physical-sector factorization.  In particular it
does not assume positivity or trace preservation and does not assert
Proposition C.7.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1388 and 1441--1450. -/
theorem physicalSectorClosureTwo_eq_kronecker (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    F.physicalSectorClosureTwo k h X =
      Matrix.kroneckerMap (· * ·) (F.boundaryOperator k h X)
        (F.neighboringOperator k h) := by
  ext x y
  simp only [physicalSectorClosureTwo, Matrix.submatrix_apply, Function.comp_apply,
    twoSiteRegroupEquiv_symm_apply, twoSiteSectorEmbedding, physClose2_apply,
    sectorCoordinateTensor_apply_same, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, boundaryOperator_apply,
    neighboringOperator_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    enter [2, a]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

end MPOTensor.PhysicalSectorFactorization
