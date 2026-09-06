/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceFactors
import TNLean.MPS.MPU.DaggerInverseGauge

/-!
# The first algebraic inverse-compatible cut construction

Let $U$ be a tensor and $T$ a unitary virtual gauge with
$U^\dagger_{ij}=T^\dagger U_{ij}T$. Put $A=I_d\otimes\overline T$ and
$B=T^T\otimes I_d$. The source cuts then satisfy
$\mathcal M_1(U)=A\mathcal M_2(U)^\dagger B$. Consequently the second source
factors give $X=AY_2^\dagger$ and $Y=X_2^\dagger B$, with explicit left and right inverses.

This is only the first algebraic construction in arXiv:2502.20257,
`main.tex` lines 5390–5432, not the full proposition at lines 5342–5350.
The factor space is `Fin ℓ[U]`; no identification with `Fin r[U]`, weighted
normalization, comparison matrix $K$, pleasant properties, or `eq:UUU` is asserted.
No simplicity or weight hypothesis is needed for this algebraic step.
The order in $B$ follows the maintained (virtual, physical) column indices of
$\mathcal M_1$, rather than silently swapping the factors in the printed formula.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The left dressing $A=I_d\otimes\overline T$ in the candidate first cut.
Source: arXiv:2502.20257, lines 5390–5432. -/
noncomputable def inverseCompatibleLeftGauge (T : Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin d × Fin D) (Fin d × Fin D) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
    (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)

/-- The right dressing $B=T^T\otimes I_d$, in (virtual, physical) index order.
Source: arXiv:2502.20257, lines 5390–5432. -/
noncomputable def inverseCompatibleRightGauge (T : Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin D × Fin d) (Fin D × Fin d) ℂ :=
  (T : Matrix (Fin D) (Fin D) ℂ)ᵀ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)

variable (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The candidate $X=AY_2^\dagger$, with factor space `Fin ℓ[U]`.
Source: arXiv:2502.20257, line 5432. -/
noncomputable def inverseCompatibleX₁ : Matrix (Fin d × Fin D) (Fin ℓ[U]) ℂ :=
  inverseCompatibleLeftGauge (d := d) T * (sourceY₂ U)ᴴ

/-- The candidate $Y=X_2^\dagger B$, with factor space `Fin ℓ[U]`.
Source: arXiv:2502.20257, line 5432. -/
noncomputable def inverseCompatibleY₁ : Matrix (Fin ℓ[U]) (Fin D × Fin d) ℂ :=
  (sourceX₂ U)ᴴ * inverseCompatibleRightGauge (d := d) T

/-- Unitary cancellation reverses the supplied adjoint gauge equation.
Source: arXiv:2502.20257, lines 5391–5410. -/
theorem eq_unitary_mul_physicalAdjointTensor_mul_conjTranspose
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) (i j : Fin d) :
    U i j = (T : Matrix (Fin D) (Fin D) ℂ) * physicalAdjointTensor U i j *
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  have hunit : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := T.property.2
  rw [hT]
  simp only [← Matrix.mul_assoc, hunit, Matrix.one_mul]
  rw [Matrix.mul_assoc, hunit, Matrix.mul_one]

/-- The first cut is the dressed adjoint of the second cut.
Source: arXiv:2502.20257, lines 5391–5431. -/
theorem sourceCutM₁_eq_inverseCompatible_dressed_cut
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) :
    sourceCutM₁ U = inverseCompatibleLeftGauge (d := d) T * (sourceCutM₂ U)ᴴ *
      inverseCompatibleRightGauge (d := d) T := by
  rw [← sourceCutM₁_physicalAdjointTensor]
  ext ⟨i, b⟩ ⟨a, j⟩
  have h := congrArg (fun M ↦ M a b)
    (eq_unitary_mul_physicalAdjointTensor_mul_conjTranspose U T hT i j)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simpa [inverseCompatibleLeftGauge, inverseCompatibleRightGauge, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply,
    sourceCutM₁, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h

private theorem inverseCompatibleLeftGauge_isometry :
    (inverseCompatibleLeftGauge (d := d) T)ᴴ * inverseCompatibleLeftGauge (d := d) T = 1 := by
  have h : ((T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ))ᴴ *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 :=
    (Matrix.map_star_mem_unitaryGroup_iff.mpr T.property).1
  simp only [inverseCompatibleLeftGauge, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul, h,
    Matrix.one_kronecker_one]

private theorem inverseCompatibleRightGauge_coisometry :
    inverseCompatibleRightGauge (d := d) T * (inverseCompatibleRightGauge (d := d) T)ᴴ = 1 := by
  have h : (T : Matrix (Fin D) (Fin D) ℂ)ᵀ *
      ((T : Matrix (Fin D) (Fin D) ℂ)ᵀ)ᴴ = 1 :=
    (Matrix.transpose_mem_unitaryGroup_iff.mpr T.property).2
  simp only [inverseCompatibleRightGauge, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul, h,
    Matrix.one_kronecker_one]

/-- The candidate factors multiply to the first source cut.
Source: arXiv:2502.20257, lines 5390–5432. -/
theorem sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T) :
    sourceCutM₁ U = inverseCompatibleX₁ U T * inverseCompatibleY₁ U T := by
  rw [sourceCutM₁_eq_inverseCompatible_dressed_cut U T hT,
    sourceCutM₂_eq_sourceX₂_mul_sourceY₂, Matrix.conjTranspose_mul]
  simp only [inverseCompatibleX₁, inverseCompatibleY₁, Matrix.mul_assoc]

/-- The candidate $X$ has the explicit left inverse $Z_2^\dagger A^\dagger$.
This verifies the left-invertibility used in arXiv:2502.20257, line 5432. -/
theorem inverseCompatibleX₁_leftInverse :
    ((sourceZ₂ U)ᴴ * (inverseCompatibleLeftGauge (d := d) T)ᴴ) * inverseCompatibleX₁ U T = 1 := by
  rw [inverseCompatibleX₁, Matrix.mul_assoc, ← Matrix.mul_assoc
    (inverseCompatibleLeftGauge (d := d) T)ᴴ, inverseCompatibleLeftGauge_isometry,
    Matrix.one_mul, ← Matrix.conjTranspose_mul, sourceY₂_mul_sourceZ₂,
    Matrix.conjTranspose_one]

/-- The candidate $Y$ has the explicit right inverse $B^\dagger X_2$.
This verifies the right-invertibility used in arXiv:2502.20257, line 5432. -/
theorem inverseCompatibleY₁_rightInverse :
    inverseCompatibleY₁ U T * ((inverseCompatibleRightGauge (d := d) T)ᴴ * sourceX₂ U) = 1 := by
  rw [inverseCompatibleY₁, Matrix.mul_assoc, ← Matrix.mul_assoc
    (inverseCompatibleRightGauge (d := d) T), inverseCompatibleRightGauge_coisometry,
    Matrix.one_mul]
  exact sourceX₂_isometry U

namespace GroupFamily

variable {G : Type*} [Group G]

omit [Group G] in
private theorem reindex_tensor_toMPSTensor_eq
    (F : MPOTensor.GroupFamily G d) (x y : G) (hxy : x = y)
    (hD : F.bondDim x = F.bondDim y) :
    MPSTensor.reindex hD (F.tensor x).toMPSTensor = (F.tensor y).toMPSTensor := by
  subst y
  exact MPSTensor.reindex_rfl _

/-- At an involutive group element, the chosen dagger-inverse gauge relates
the tensor to its own physical adjoint. Canonicality is stated explicitly as
left-canonicality of every normalized flattening.
Source: arXiv:2502.20257, `eq:defT`, lines 1552–1557, and lines 1933–1955. -/
theorem IsRepresentation.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ a : G,
      MPSTensor.IsLeftCanonical (F.tensor a).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) (i j : Fin d) :
    let T := hF.daggerInverseGauge F hcanonical g
    physicalAdjointTensor (F.tensor g) i j =
      (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ * F.tensor g i j * T := by
  have hinv : inverseFlattening F hF g = (F.tensor g).toMPSTensor :=
    reindex_tensor_toMPSTensor_eq F g⁻¹ g hg (hF.bondDim_inv F g).symm
  have h := hF.physicalAdjointTensor_eq_daggerInverseGauge F hcanonical g
    (finProdFinEquiv (i, j))
  rw [hinv] at h
  simpa only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] using h

/-- The first algebraic construction and both one-sided inverses, specialized
to the chosen gauge of an involutive element in a canonical representation family.
This is the construction at arXiv:2502.20257, lines 5390–5432, using `eq:defT`
(lines 1552–1557); it does not assert the full proposition at lines 5342–5350. -/
theorem IsRepresentation.inverseCompatibleFirstCut_of_inv_eq
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ a : G,
      MPSTensor.IsLeftCanonical (F.tensor a).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) :
    let T := hF.daggerInverseGauge F hcanonical g
    let X := inverseCompatibleX₁ (F.tensor g) T
    let Y := inverseCompatibleY₁ (F.tensor g) T
    sourceCutM₁ (F.tensor g) = X * Y ∧
      ((sourceZ₂ (F.tensor g))ᴴ * (inverseCompatibleLeftGauge (d := d) T)ᴴ) * X = 1 ∧
      Y * ((inverseCompatibleRightGauge (d := d) T)ᴴ * sourceX₂ (F.tensor g)) = 1 := by
  refine ⟨sourceCutM₁_eq_inverseCompatibleX₁_mul_inverseCompatibleY₁ _ _ ?_,
    inverseCompatibleX₁_leftInverse _ _, inverseCompatibleY₁_rightInverse _ _⟩
  exact hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg

end GroupFamily

end MPOTensor
