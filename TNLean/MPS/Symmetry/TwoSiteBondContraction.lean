/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.TwoSiteBondInteraction
import TNLean.MPS.Symmetry.SPTFixedPoint

/-!
# Contracting a two-site bond operator

A middle-bond operator acts only on the corresponding coefficient vector,
leaving arbitrary coefficients on the two exterior registers unchanged.
This contracts the two-site fixed-point parent interaction of
arXiv:1010.3732, Section II.D.2, `eq:phase-nosym:iso-hamiltonian`.
-/

open scoped Matrix

namespace MPSTensor

/-- The coefficient of a two-site bond operator is obtained by summing
only over the middle registers. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_mulVec_apply {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (f : Cfg (D * D) 2 → ℂ) (s : Cfg (D * D) 2) :
    (twoSiteBondInteraction K).mulVec f s =
      ∑ b : Fin D, ∑ c : Fin D,
        K ((sptPair (s 0)).2, (sptPair (s 1)).1) (b, c) *
          f ![finProdFinEquiv ((sptPair (s 0)).1, b),
            finProdFinEquiv (c, (sptPair (s 1)).2)] := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (twoSiteBondEquiv D).symm]
  simp [Fintype.sum_prod_type, twoSiteBondInteraction_apply, twoSiteBondEquiv, sptPair]

/-- A two-site bond operator acts only on the middle factor of a vector
whose exterior dependence is arbitrary. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_mulVec_separable {D : ℕ}
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (η : Fin D × Fin D → ℂ) (F : Fin D → Fin D → ℂ) :
    (twoSiteBondInteraction K).mulVec
      (fun s => η ((sptPair (s 0)).2, (sptPair (s 1)).1) *
        F (sptPair (s 0)).1 (sptPair (s 1)).2) =
      fun s => (K.mulVec η) ((sptPair (s 0)).2, (sptPair (s 1)).1) *
        F (sptPair (s 0)).1 (sptPair (s 1)).2 := by
  ext s
  rw [twoSiteBondInteraction_mulVec_apply]
  simp only [sptPair, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Equiv.symm_apply_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, ← mul_assoc, ← Finset.sum_mul]

/-- A unit bond vector is annihilated by its complementary penalty.
Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem bondPenalty_mulVec_self {q : ℕ} (η : Fin q → ℂ)
    (hη : ∑ x, Complex.normSq (η x) = 1) :
    (bondPenalty η).mulVec η = 0 := by
  have hnorm : star η ⬝ᵥ η = 1 := by
    simpa [dotProduct, Complex.normSq_eq_conj_mul_self, Complex.star_def] using
      congrArg (fun r : ℝ => (r : ℂ)) hη
  simp [bondPenalty, bondVectorProjection, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hnorm]

/-- A unit bond penalty annihilates a separable two-site vector with that
bond on its middle registers. The exterior coefficient is arbitrary.
Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondPenalty_mulVec_separable {D : ℕ}
    (η : Fin (D * D) → ℂ) (hη : ∑ x, Complex.normSq (η x) = 1)
    (F : Fin D → Fin D → ℂ) :
    (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm (bondPenalty η))).mulVec
      (fun s => η (finProdFinEquiv ((sptPair (s 0)).2, (sptPair (s 1)).1)) *
        F (sptPair (s 0)).1 (sptPair (s 1)).2) = 0 := by
  have hK : (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty η)).mulVec (η ∘ finProdFinEquiv) = 0 := by
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mulVec_equiv,
      Function.comp_def, Equiv.apply_symm_apply, bondPenalty_mulVec_self η hη,
      Pi.zero_apply]
    rfl
  simpa only [Function.comp_apply, hK, Pi.zero_apply, zero_mul, Pi.zero_def] using
    twoSiteBondInteraction_mulVec_separable
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm (bondPenalty η))
      (η ∘ finProdFinEquiv) F

end MPSTensor
