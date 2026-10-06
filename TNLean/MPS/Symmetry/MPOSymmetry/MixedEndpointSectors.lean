/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointSupport

/-!
# Physical sectors of the extended endpoint support

For the first endpoint of the mixed tensor of arXiv:2203.12563,
Section 5, lines 1586–1601 and 1690–1692, the inserted matrix is the
projection onto the first bond summand. The two outer physical-sector
projections correspond to multiplication of the boundary matrix on the
right and left. Hence the extended support is invariant under these
projections. These identities concern the actual arbitrary endpoint
tensors; no sector reduction is assumed.

This is a local ingredient for comparing the extended endpoint Hamiltonian
with the canonical parent of the embedded endpoint. No spectral-gap
comparison is asserted here.
-/

open scoped Matrix

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- Left multiplication by the block weight rescales each physical letter
by the weight of its row sector. Source: arXiv:2203.12563, `defAgamma`,
lines 1586–1601, used for the endpoint support at line 1690. -/
theorem bondInterpolationMatrix_mul_mixedEndpointBase
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (γ : ℝ) (p : Fin ((D₀ + D₁) * (D₀ + D₁))) :
    bondInterpolationMatrix D₀ D₁ γ * mixedEndpointBase A₀ A₁ p =
      bondInterpolationWeight D₀ D₁ γ (finProdFinEquiv.symm p).1 •
        mixedEndpointBase A₀ A₁ p := by
  ext i j
  simp only [bondInterpolationMatrix, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul]
  unfold mixedEndpointBase
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize ha : finSumFinEquiv.symm (finProdFinEquiv.symm p).1 = a
  generalize hb : finSumFinEquiv.symm (finProdFinEquiv.symm p).2 = b
  unfold bondInterpolationWeight
  rw [ha]
  cases a <;> cases b <;>
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [mixedEndpointLetter, Matrix.fromBlocks, Matrix.single_apply]

/-- Projection onto physical configurations whose row register at the
specified site belongs to the first endpoint sector.
Source: arXiv:2203.12563, Section 5, lines 1586–1601 and 1690–1692. -/
noncomputable def mixedEndpointRowSector (D₀ D₁ : ℕ) (site : Fin 2) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ site)).1)

/-- Projection onto physical configurations whose column register at the
specified site belongs to the first endpoint sector.
Source: arXiv:2203.12563, Section 5, lines 1586–1601 and 1690–1692. -/
noncomputable def mixedEndpointColumnSector (D₀ D₁ : ℕ) (site : Fin 2) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ =>
    bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ site)).2)

@[simp]
theorem mixedEndpointRowSector_apply (site : Fin 2)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :
    mixedEndpointRowSector D₀ D₁ site v σ =
      bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ site)).1 * v σ := by
  simp [mixedEndpointRowSector, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

@[simp]
theorem mixedEndpointColumnSector_apply (site : Fin 2)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :
    mixedEndpointColumnSector D₀ D₁ site v σ =
      bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm (σ site)).2 * v σ := by
  simp [mixedEndpointColumnSector, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec_diagonal]

/-- The first physical row projection is right multiplication of the
boundary by the first virtual projection. Source: arXiv:2203.12563,
Section 5, line 1690, decomposition of the extended support into outer sectors. -/
theorem mixedEndpointRowSector_insertedTwoSiteMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    mixedEndpointRowSector D₀ D₁ 0
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W
        (WithLp.toLp 2 (fun p => X p.1 p.2))) =
      insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W
        (WithLp.toLp 2 (fun p => (X * bondInterpolationMatrix D₀ D₁ 0) p.1 p.2)) := by
  apply PiLp.ext
  intro σ
  rw [mixedEndpointRowSector_apply, insertedTwoSiteMap_apply, insertedTwoSiteMap_apply]
  change _ = Matrix.trace (mixedEndpointBase A₀ A₁ (σ 0) * W *
    mixedEndpointBase A₀ A₁ (σ 1) * (X * bondInterpolationMatrix D₀ D₁ 0))
  conv_rhs => rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, bondInterpolationMatrix_mul_mixedEndpointBase,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

/-- The second physical column projection is left multiplication of the
boundary by the first virtual projection. Source: arXiv:2203.12563,
Section 5, line 1690, decomposition of the extended support into outer sectors. -/
theorem mixedEndpointColumnSector_insertedTwoSiteMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    mixedEndpointColumnSector D₀ D₁ 1
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W
        (WithLp.toLp 2 (fun p => X p.1 p.2))) =
      insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W
        (WithLp.toLp 2 (fun p => (bondInterpolationMatrix D₀ D₁ 0 * X) p.1 p.2)) := by
  apply PiLp.ext
  intro σ
  rw [mixedEndpointColumnSector_apply, insertedTwoSiteMap_apply, insertedTwoSiteMap_apply]
  change _ = Matrix.trace (mixedEndpointBase A₀ A₁ (σ 0) * W *
    mixedEndpointBase A₀ A₁ (σ 1) * (bondInterpolationMatrix D₀ D₁ 0 * X))
  have hright := mixedEndpointInterpolation_eq_smul A₀ A₁ 0 (σ 1)
  change mixedEndpointBase A₀ A₁ (σ 1) * bondInterpolationMatrix D₀ D₁ 0 = _ at hright
  conv_rhs =>
    rw [Matrix.mul_assoc (mixedEndpointBase A₀ A₁ (σ 0) * W),
      ← Matrix.mul_assoc (mixedEndpointBase A₀ A₁ (σ 1)), hright]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc]
  rfl

/-- The extended support is invariant under the first physical row-sector
projection. This is derived from the boundary action above.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem range_insertedTwoSiteMap_invariant_rowSector
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range.map
      (mixedEndpointRowSector D₀ D₁ 0) ≤
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := fun a b => v (a, b)
  refine ⟨WithLp.toLp 2 (fun p => (X * bondInterpolationMatrix D₀ D₁ 0) p.1 p.2), ?_⟩
  exact (mixedEndpointRowSector_insertedTwoSiteMap A₀ A₁ W X).symm

/-- The extended support is invariant under the second physical column-sector
projection. This is derived from the boundary action above.
Source: arXiv:2203.12563, Section 5, line 1690. -/
theorem range_insertedTwoSiteMap_invariant_columnSector
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (W : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range.map
      (mixedEndpointColumnSector D₀ D₁ 1) ≤
        (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) W).range := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  let X : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ := fun a b => v (a, b)
  refine ⟨WithLp.toLp 2 (fun p => (bondInterpolationMatrix D₀ D₁ 0 * X) p.1 p.2), ?_⟩
  exact (mixedEndpointColumnSector_insertedTwoSiteMap A₀ A₁ W X).symm

/-- At the first endpoint every extended-support vector has its first
physical column in the first sector. Source: arXiv:2203.12563,
Section 5, line 1690, the endpoint insertion `W(0)`. -/
theorem mixedEndpointColumnSector_zero_insertedTwoSiteMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (v : EuclideanSpace ℂ (Fin (D₀ + D₁) × Fin (D₀ + D₁))) :
    mixedEndpointColumnSector D₀ D₁ 0
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0) v) =
      insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0) v := by
  apply PiLp.ext
  intro σ
  rw [mixedEndpointColumnSector_apply, insertedTwoSiteMap_apply]
  cases h : finSumFinEquiv.symm (finProdFinEquiv.symm (σ 0)).2 with
  | inl a => simp only [bondInterpolationWeight, h, sub_zero, Complex.ofReal_one, one_mul]
  | inr a =>
      have hzero := mixedEndpointInterpolation_eq_smul A₀ A₁ 0 (σ 0)
      change mixedEndpointBase A₀ A₁ (σ 0) * bondInterpolationMatrix D₀ D₁ 0 = _ at hzero
      simp only [bondInterpolationWeight, h, Complex.ofReal_zero, zero_smul] at hzero
      simp only [bondInterpolationWeight, h, Complex.ofReal_zero, zero_mul, hzero,
        Matrix.trace_zero]

/-- At the first endpoint every extended-support vector has its second
physical row in the first sector. Source: arXiv:2203.12563,
Section 5, line 1690, the endpoint insertion `W(0)`. -/
theorem mixedEndpointRowSector_one_insertedTwoSiteMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (v : EuclideanSpace ℂ (Fin (D₀ + D₁) × Fin (D₀ + D₁))) :
    mixedEndpointRowSector D₀ D₁ 1
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0) v) =
      insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
        (bondInterpolationMatrix D₀ D₁ 0) v := by
  apply PiLp.ext
  intro σ
  rw [mixedEndpointRowSector_apply, insertedTwoSiteMap_apply]
  cases h : finSumFinEquiv.symm (finProdFinEquiv.symm (σ 1)).1 with
  | inl a => simp only [bondInterpolationWeight, h, sub_zero, Complex.ofReal_one, one_mul]
  | inr a =>
      have hzero := bondInterpolationMatrix_mul_mixedEndpointBase A₀ A₁ 0 (σ 1)
      simp only [bondInterpolationWeight, h, Complex.ofReal_zero, zero_smul] at hzero
      simp only [bondInterpolationWeight, h, Complex.ofReal_zero, zero_mul, Matrix.mul_assoc,
        hzero, Matrix.mul_zero, Matrix.trace_zero]

end MPOSymmetry
end MPSTensor
