/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Three-site closure in fixed physical sectors

This file evaluates the three-site physical closure of a tensor admitting a
physical-sector factorization.  After restricting the three physical sites to
fixed sectors `k`, `l`, and `h`, the physical indices are regrouped into the
two outer factors and the two neighboring pairs.  The resulting matrix is the
Kronecker product of the boundary operator with the two neighboring
operators.

Only the algebraic sector factorization is used.  No positivity,
normalization, or quantum-channel assertion is made.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `etarl`, lines 1381--1450, and the
  three-site contraction in Proposition C.7, lines 1510--1516
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The inclusion of three fixed physical sectors into the right-associated
three-site physical index space.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450. -/
noncomputable def threeSiteSectorEmbedding (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount) :
    SectorIndex F k × (SectorIndex F l × SectorIndex F h) →
      Fin (Fintype.card (Σ q : Fin F.sectorCount, SectorIndex F q)) ×
        (Fin (Fintype.card (Σ q : Fin F.sectorCount, SectorIndex F q)) ×
          Fin (Fintype.card (Σ q : Fin F.sectorCount, SectorIndex F q))) :=
  fun x ↦
    (F.sectorFinEquiv.symm ⟨k, x.1⟩,
      (F.sectorFinEquiv.symm ⟨l, x.2.1⟩,
        F.sectorFinEquiv.symm ⟨h, x.2.2⟩))

/-- Regroup the three fixed physical sectors into the outer boundary factors
and the two neighboring pairs:
\[
 ((l_k,r_k),((l_l,r_l),(l_h,r_h)))
 \longmapsto ((l_k,r_h),((r_k,l_l),(r_l,l_h))).
\]

Source: arXiv:1606.00608, Appendix C.2, line 1547 and the accompanying
diagram. -/
def threeSiteRegroupEquiv (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount) :
    (SectorIndex F k × (SectorIndex F l × SectorIndex F h)) ≃
      (BoundaryIndex F k h × (NeighborIndex F k l × NeighborIndex F l h)) where
  toFun x := ((x.1.1, x.2.2.2), ((x.1.2, x.2.1.1), (x.2.1.2, x.2.2.1)))
  invFun x := ((x.1.1, x.2.1.1), ((x.2.1.2, x.2.2.1), (x.2.2.2, x.1.2)))
  left_inv := by rintro ⟨⟨lk, rk⟩, ⟨ll, rl⟩, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨lk, rh⟩, ⟨rk, ll⟩, rl, lh⟩; rfl

/-- The fixed-`(k,l,h)` submatrix of the three-site closure, reindexed into
the outer boundary factors and the two neighboring pairs.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450, and Proposition C.7, lines 1510--1516. -/
noncomputable def threeSiteSectorClosure (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (BoundaryIndex F k h × (NeighborIndex F k l × NeighborIndex F l h))
      (BoundaryIndex F k h × (NeighborIndex F k l × NeighborIndex F l h)) ℂ :=
  Matrix.reindex (threeSiteRegroupEquiv F k l h) (threeSiteRegroupEquiv F k l h)
    ((MPOTensor.physClose3 F.sectorCoordinateTensor X).submatrix
      (threeSiteSectorEmbedding F k l h) (threeSiteSectorEmbedding F k l h))

/-- The three-site closure in fixed physical sectors factors into its outer
boundary contraction and the two neighboring contractions:
\[
 K_{3;k,l,h}(X)=B_{k,h}(X)\otimes
   \bigl(\eta_{k,l}\otimes\eta_{l,h}\bigr).
\]

This is an identity for an arbitrary virtual matrix `X`.  It asserts neither
positivity nor normalization of any factor.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `etarl`,
lines 1381--1450, and the three-site contraction in Proposition C.7, lines
1510--1516. -/
theorem threeSiteSectorClosure_eq (F : PhysicalSectorFactorization K)
    (k l h : Fin F.sectorCount) (X : Matrix (Fin D) (Fin D) ℂ) :
    F.threeSiteSectorClosure k l h X =
      F.boundaryOperator k h X ⊗ₖ
        (F.neighboringOperator k l ⊗ₖ F.neighboringOperator l h) := by
  ext x y
  simp [threeSiteSectorClosure, threeSiteSectorEmbedding, threeSiteRegroupEquiv,
    MPOTensor.physClose3, Matrix.trace, Matrix.mul_apply, Matrix.mul_assoc]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have sum_permute (f : Fin D → Fin D → Fin D → Fin D → ℂ) :
      (∑ a, ∑ c, ∑ e, ∑ b, f a c e b) =
        ∑ e, ∑ a, ∑ b, ∑ c, f a c e b := by
    calc
      _ = ∑ a, ∑ e, ∑ c, ∑ b, f a c e b := by
        congr 1 with a
        rw [Finset.sum_comm]
      _ = ∑ e, ∑ a, ∑ c, ∑ b, f a c e b := Finset.sum_comm
      _ = _ := by
        congr 1 with e
        congr 1 with a
        rw [Finset.sum_comm]
  rw [sum_permute]
  congr 1 with e
  congr 1 with a
  congr 1 with b
  rw [Finset.mul_sum]
  congr 1 with c
  ring

end MPOTensor.PhysicalSectorFactorization
