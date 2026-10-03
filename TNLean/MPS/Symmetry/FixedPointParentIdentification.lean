/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BondProductEndpointGroundSpace
import TNLean.MPS.Symmetry.TwoSiteBondContraction

/-!
# The canonical parent interaction of the matrix-unit fixed point

For the tensor with letters \(D^{-1/2}|a\rangle\langle b|\), the two-site
open-boundary ground space consists of an arbitrary pair of exterior
registers and a maximally entangled vector on the interior bond. Consequently,
the canonical two-site parent interaction is exactly the independent-bond
penalty in Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.D.2
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor

/-- The complement of the bond penalty maps an arbitrary two-site vector to
an open-boundary vector of the matrix-unit tensor. The boundary matrix is
obtained by contracting the interior diagonal. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem one_sub_twoSiteBondInteraction_mulVec_sptFixedPointTensor
    (D : ℕ) (f : Cfg (D * D) 2 → ℂ) :
    (1 - twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D)))).mulVec f =
      groundSpaceMap (sptFixedPointTensor D) 2
        (fun d a => ∑ x : Fin D,
          f ![finProdFinEquiv (a, x), finProdFinEquiv (x, d)]) := by
  classical
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    twoSiteBondInteraction_mulVec_apply]
  erw [groundSpaceMap_sptFixedPointTensor_two_apply]
  simp only [sptPair, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [bondPenalty, Matrix.sub_apply, Matrix.one_apply,
    bondVectorProjection, Matrix.vecMulVec_apply, sub_mul,
    Finset.sum_sub_distrib]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, ite_and,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero,
    Pi.star_apply, matrixUnitBondVector_apply]
  simp only [Prod.mk.eta, Equiv.apply_symm_apply, apply_ite star, star_inv₀,
    RCLike.star_def, Complex.conj_ofReal, star_zero, mul_ite,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [show ![s 0, s 1] = s from (finTwoArrowEquiv _).symm_apply_apply s,
    Complex.ofReal_sqrt_inv_mul_self (D : ℝ) (Nat.cast_nonneg D),
    Complex.ofReal_natCast, ← Finset.mul_sum, sub_sub_cancel]

/-- The kernel of the two-site bond penalty is precisely the open-boundary
MPS ground space of the matrix-unit fixed point. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_apply_eq_zero_iff_sptFixedPointTensor
    (D : ℕ) (hD : 0 < D) (v : EuclideanSpace ℂ (Cfg (D * D) 2)) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (matrixUnitBondVector D)))) v = 0 ↔
      v ∈ groundSpaceES (sptFixedPointTensor D) 2 := by
  rw [mem_groundSpaceES_iff, groundSpace, LinearMap.mem_range]
  constructor
  · intro hv
    refine ⟨fun d a => ∑ x : Fin D,
      v.ofLp ![finProdFinEquiv (a, x), finProdFinEquiv (x, d)], ?_⟩
    have hv' := congrArg WithLp.ofLp hv
    change (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D)))).mulVec v.ofLp = 0 at hv'
    change (groundSpaceMap (sptFixedPointTensor D) 2 _ : Cfg (D * D) 2 → ℂ) = v.ofLp
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, hv', sub_zero] using
      (one_sub_twoSiteBondInteraction_mulVec_sptFixedPointTensor D v.ofLp).symm
  · rintro ⟨X, hX⟩
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace (D * D) 2)).injective
    change (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D)))).mulVec
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace (D * D) 2)) v) = 0
    rw [← hX]
    exact twoSiteBondInteraction_groundSpaceMap_sptFixedPointTensor D hD X

/-- The canonical two-site parent interaction of the matrix-unit fixed point
is exactly the independent-bond penalty. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_eq_parentInteractionES_sptFixedPointTensor
    (D : ℕ) (hD : 0 < D) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (matrixUnitBondVector D)))) =
      parentInteractionES (sptFixedPointTensor D) 2 := by
  let B := Matrix.toEuclideanLin
    (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D))))
  have hB : B.IsSymmetricProjection :=
    twoSiteBondInteraction_bondPenalty_isSymmetricProjection
      (matrixUnitBondVector D) (matrixUnitBondVector_sum_normSq D hD)
  have hP := parentInteractionES_isSymmetricProjection (sptFixedPointTensor D) 2
  apply hB.ext hP
  rw [← Submodule.orthogonal_orthogonal B.range, hB.isSymmetric.orthogonal_range,
    ← Submodule.orthogonal_orthogonal (parentInteractionES (sptFixedPointTensor D) 2).range,
    hP.isSymmetric.orthogonal_range]
  congr 1
  ext v
  exact (twoSiteBondInteraction_apply_eq_zero_iff_sptFixedPointTensor D hD v).trans
    (parentInteractionES_apply_eq_zero_iff (sptFixedPointTensor D) 2 v).symm

end MPSTensor
