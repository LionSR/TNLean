/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFrameSupport
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointReducingSectors

/-!
# One-sided product supports of the actual joint endpoint

Let \(L\) and \(R\) be the orthogonal projections onto the ranges of the
two full joint boundary polar frames. The actual two-site support is fixed
by \(L\otimes P_{\mathrm{row},0}\) and
\(P_{\mathrm{column},0}\otimes R\). These are orthogonal product
projections on the original physical alphabet. Their complementary
projections are bounded by the actual parent interaction with coefficient
one.

The construction uses the full joint column spaces, including cross-label
Gram entries. It neither crops physical sites nor assumes that a rectangular
frame is surjective. No positivity of a dimension or one-site spanning
hypothesis is needed.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix Kronecker ComplexOrder

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private def rangeProjectionMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι κ ℂ) : Matrix ι ι ℂ :=
  Matrix.toEuclideanLin.symm (Matrix.toEuclideanLin U).range.starProjection.toLinearMap

private theorem rangeProjectionMatrix_isSymmetricProjection
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) :
    (Matrix.toEuclideanLin (rangeProjectionMatrix U)).IsSymmetricProjection := by
  simpa only [rangeProjectionMatrix, LinearEquiv.apply_symm_apply] using
    Submodule.isSymmetricProjection_starProjection (Matrix.toEuclideanLin U).range

private theorem rangeProjectionMatrix_mul_self
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) :
    rangeProjectionMatrix U * rangeProjectionMatrix U = rangeProjectionMatrix U := by
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
    (rangeProjectionMatrix_isSymmetricProjection U).isIdempotentElem.eq

private theorem rangeProjectionMatrix_mul
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) : rangeProjectionMatrix U * U = U := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, rangeProjectionMatrix,
    LinearEquiv.apply_symm_apply]
  ext v
  exact Submodule.starProjection_eq_self_iff.mpr ⟨v, rfl⟩

/-- Matrix of the orthogonal projection onto the full first joint polar
frame range. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstFrameProjectionMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ :=
  rangeProjectionMatrix (Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁))

/-- Matrix of the orthogonal projection onto the full last joint polar
frame range. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastFrameProjectionMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ :=
  rangeProjectionMatrix (Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁))

@[simp]
theorem toEuclideanLin_jointMixedFirstFrameProjectionMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix.toEuclideanLin (jointMixedFirstFrameProjectionMatrix A₀ A₁) =
      (Matrix.toEuclideanLin (Matrix.polarIso
        (jointMixedFirstBoundaryColumns A₀ A₁))).range.starProjection.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

@[simp]
theorem toEuclideanLin_jointMixedLastFrameProjectionMatrix
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix.toEuclideanLin (jointMixedLastFrameProjectionMatrix A₀ A₁) =
      (Matrix.toEuclideanLin (Matrix.polarIso
        (jointMixedLastBoundaryColumns A₀ A₁))).range.starProjection.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- The full first frame projection is Hermitian, including for empty
boundary spaces. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstFrameProjectionMatrix_isHermitian
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedFirstFrameProjectionMatrix A₀ A₁).IsHermitian :=
  Matrix.isSymmetric_toEuclideanLin_iff.mp
    (rangeProjectionMatrix_isSymmetricProjection _).isSymmetric

/-- The full last frame projection is Hermitian.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastFrameProjectionMatrix_isHermitian
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedLastFrameProjectionMatrix A₀ A₁).IsHermitian :=
  Matrix.isSymmetric_toEuclideanLin_iff.mp
    (rangeProjectionMatrix_isSymmetricProjection _).isSymmetric

@[simp]
theorem jointMixedFirstFrameProjectionMatrix_mul_self
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedFirstFrameProjectionMatrix A₀ A₁ *
      jointMixedFirstFrameProjectionMatrix A₀ A₁ =
        jointMixedFirstFrameProjectionMatrix A₀ A₁ := rangeProjectionMatrix_mul_self _

@[simp]
theorem jointMixedLastFrameProjectionMatrix_mul_self
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedLastFrameProjectionMatrix A₀ A₁ *
      jointMixedLastFrameProjectionMatrix A₀ A₁ =
        jointMixedLastFrameProjectionMatrix A₀ A₁ := rangeProjectionMatrix_mul_self _

@[simp]
theorem jointMixedFirstFrameProjectionMatrix_mul_polarIso
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedFirstFrameProjectionMatrix A₀ A₁ *
      Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) =
        Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) := rangeProjectionMatrix_mul _

@[simp]
theorem jointMixedLastFrameProjectionMatrix_mul_polarIso
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedLastFrameProjectionMatrix A₀ A₁ *
      Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁) =
        Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁) := rangeProjectionMatrix_mul _

private theorem binaryDiagonal_isHermitian {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (hf : ∀ i, f i = 0 ∨ f i = 1) :
    (Matrix.diagonal f).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  simp only [Pi.star_apply]
  rcases hf i with h | h <;> simp [h]

private theorem binaryDiagonal_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (hf : ∀ i, f i = 0 ∨ f i = 1) :
    Matrix.diagonal f * Matrix.diagonal f = Matrix.diagonal f := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases hf i with h | h <;> simp [h]

private theorem kroneckerCfg_isSymmetricProjection {d : ℕ}
    (P Q : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q) :
    (Matrix.toEuclideanLin ((P ⊗ₖ Q).submatrix
      (finTwoArrowEquiv _) (finTwoArrowEquiv _))).IsSymmetricProjection := by
  let M := (P ⊗ₖ Q).submatrix (finTwoArrowEquiv _) (finTwoArrowEquiv _)
  have hMM : M * M = M := by
    dsimp [M]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, hPP, hQQ]
  constructor
  · change Matrix.toEuclideanLin M ∘ₗ Matrix.toEuclideanLin M = Matrix.toEuclideanLin M
    rw [← Matrix.toLpLin_mul_same, hMM]
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.IsHermitian.submatrix
    change (P ⊗ₖ Q)ᴴ = P ⊗ₖ Q
    rw [Matrix.conjTranspose_kronecker, hP, hQ]

/-- The full two-site product projection onto the first frame range and
row phase zero at the second site. No physical alphabet is cropped.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstOneSidedProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  Matrix.toEuclideanLin ((jointMixedFirstFrameProjectionMatrix A₀ A₁ ⊗ₖ
    Matrix.diagonal jointMixedRowWeight).submatrix
      (finTwoArrowEquiv _) (finTwoArrowEquiv _))

/-- The reflected full product projection onto column phase zero at the
first site and the last frame range at the second site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastOneSidedProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  Matrix.toEuclideanLin ((Matrix.diagonal jointMixedColumnWeight ⊗ₖ
    jointMixedLastFrameProjectionMatrix A₀ A₁).submatrix
      (finTwoArrowEquiv _) (finTwoArrowEquiv _))

/-- The first one-sided product constraint is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstOneSidedProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedFirstOneSidedProjection A₀ A₁).IsSymmetricProjection :=
  kroneckerCfg_isSymmetricProjection _ _
    (jointMixedFirstFrameProjectionMatrix_isHermitian A₀ A₁)
    (binaryDiagonal_isHermitian _ jointMixedRowWeight_eq_zero_or_one)
    (jointMixedFirstFrameProjectionMatrix_mul_self A₀ A₁)
    (binaryDiagonal_mul_self _ jointMixedRowWeight_eq_zero_or_one)

/-- The last one-sided product constraint is an orthogonal projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastOneSidedProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedLastOneSidedProjection A₀ A₁).IsSymmetricProjection :=
  kroneckerCfg_isSymmetricProjection _ _
    (binaryDiagonal_isHermitian _ jointMixedColumnWeight_eq_zero_or_one)
    (jointMixedLastFrameProjectionMatrix_isHermitian A₀ A₁)
    (binaryDiagonal_mul_self _ jointMixedColumnWeight_eq_zero_or_one)
    (jointMixedLastFrameProjectionMatrix_mul_self A₀ A₁)

private theorem firstOneSidedProjection_comp_polarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedFirstOneSidedProjection A₀ A₁ ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) =
      jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2) ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) := by
  change Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _ =
    Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
  congr 1
  unfold jointMixedTwoSitePolarFrame
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    jointMixedFirstFrameProjectionMatrix_mul_polarIso]
  ext σ j
  simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    finTwoArrowEquiv_apply, id_eq]
  ring

private theorem lastOneSidedProjection_comp_polarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedLastOneSidedProjection A₀ A₁ ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) =
      jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2) ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) := by
  change Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _ =
    Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
  congr 1
  unfold jointMixedTwoSitePolarFrame
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    jointMixedLastFrameProjectionMatrix_mul_polarIso]
  ext σ j
  simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    finTwoArrowEquiv_apply, id_eq]
  ring

/-- The actual two-site support is fixed by the first one-sided product
projection, using the full product frame and the fixed inner row phase.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstOneSidedProjection_apply_of_mem_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)}
    (hv : v ∈ (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range) :
    jointMixedFirstOneSidedProjection A₀ A₁ v = v := by
  obtain ⟨z, hz⟩ := range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁ hv
  have hfix : jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2) v = v := by
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective w
    exact jointMixedRowSector_one_blockInsertedBoundaryMap A₀ A₁ X
  calc
    _ = jointMixedFirstOneSidedProjection A₀ A₁
        (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) z) := by rw [hz]
    _ = jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2)
        (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) z) :=
      LinearMap.congr_fun (firstOneSidedProjection_comp_polarFrame A₀ A₁) z
    _ = v := by rw [hz, hfix]

/-- The reflected one-sided product projection likewise fixes the actual
support, using its fixed inner column phase.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastOneSidedProjection_apply_of_mem_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)}
    (hv : v ∈ (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range) :
    jointMixedLastOneSidedProjection A₀ A₁ v = v := by
  obtain ⟨z, hz⟩ := range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁ hv
  have hfix : jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2) v = v := by
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨X, rfl⟩ := blockBoundaryEquiv.symm.surjective w
    exact jointMixedColumnSector_zero_blockInsertedBoundaryMap A₀ A₁ X
  calc
    _ = jointMixedLastOneSidedProjection A₀ A₁
        (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) z) := by rw [hz]
    _ = jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2)
        (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) z) :=
      LinearMap.congr_fun (lastOneSidedProjection_comp_polarFrame A₀ A₁) z
    _ = v := by rw [hz, hfix]

/-- Actual support containment in the full first one-sided orthogonal
product frame. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_le_firstOneSidedProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range ≤
        (jointMixedFirstOneSidedProjection A₀ A₁).range := by
  intro v hv
  exact ⟨v, jointMixedFirstOneSidedProjection_apply_of_mem_support A₀ A₁ hv⟩

/-- Actual support containment in the full last one-sided orthogonal
product frame. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_le_lastOneSidedProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range ≤
        (jointMixedLastOneSidedProjection A₀ A₁).range := by
  intro v hv
  exact ⟨v, jointMixedLastOneSidedProjection_apply_of_mem_support A₀ A₁ hv⟩

/-- The first one-sided complementary penalty is bounded by the actual
parent interaction with coefficient one.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedFirstOneSidedProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedFirstOneSidedProjection A₀ A₁ ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply sub_le_sub_left
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
    (jointMixedFirstOneSidedProjection_isSymmetricProjection A₀ A₁) |>.mpr
  rw [Submodule.range_starProjection]
  exact range_blockInsertedBoundaryMap_jointMixed_le_firstOneSidedProjection A₀ A₁

/-- The reflected one-sided complementary penalty has the same
coefficient-one bound. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedLastOneSidedProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedLastOneSidedProjection A₀ A₁ ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply sub_le_sub_left
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
    (jointMixedLastOneSidedProjection_isSymmetricProjection A₀ A₁) |>.mpr
  rw [Submodule.range_starProjection]
  exact range_blockInsertedBoundaryMap_jointMixed_le_lastOneSidedProjection A₀ A₁

/-- The first full one-sided product projection reduces the actual
interaction. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstOneSidedProjection_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedFirstOneSidedProjection A₀ A₁)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply (Commute.one_right _).sub_right
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedFirstOneSidedProjection_isSymmetricProjection A₀ A₁).isSymmetric
  rintro _ ⟨v, hv, rfl⟩
  rwa [jointMixedFirstOneSidedProjection_apply_of_mem_support A₀ A₁ hv]

/-- The last full one-sided product projection reduces the actual
interaction. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastOneSidedProjection_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedLastOneSidedProjection A₀ A₁)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply (Commute.one_right _).sub_right
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedLastOneSidedProjection_isSymmetricProjection A₀ A₁).isSymmetric
  rintro _ ⟨v, hv, rfl⟩
  rwa [jointMixedLastOneSidedProjection_apply_of_mem_support A₀ A₁ hv]

/-- The first frame projection at the first site, with the full identity
at the second site. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstFrameAtZeroProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  Matrix.toEuclideanLin ((jointMixedFirstFrameProjectionMatrix A₀ A₁ ⊗ₖ
    (1 : Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ)).submatrix
        (finTwoArrowEquiv _) (finTwoArrowEquiv _))

/-- The last frame projection at the second site, with the full identity
at the first site. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastFrameAtOneProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  Matrix.toEuclideanLin (((1 : Matrix (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))
    (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) ℂ) ⊗ₖ
      jointMixedLastFrameProjectionMatrix A₀ A₁).submatrix
        (finTwoArrowEquiv _) (finTwoArrowEquiv _))

/-- The first-site frame selector is orthogonal.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstFrameAtZeroProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedFirstFrameAtZeroProjection A₀ A₁).IsSymmetricProjection :=
  kroneckerCfg_isSymmetricProjection _ _
    (jointMixedFirstFrameProjectionMatrix_isHermitian A₀ A₁) Matrix.isHermitian_one
    (jointMixedFirstFrameProjectionMatrix_mul_self A₀ A₁) (Matrix.one_mul _)

/-- The second-site frame selector is orthogonal.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastFrameAtOneProjection_isSymmetricProjection
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (jointMixedLastFrameAtOneProjection A₀ A₁).IsSymmetricProjection :=
  kroneckerCfg_isSymmetricProjection _ _ Matrix.isHermitian_one
    (jointMixedLastFrameProjectionMatrix_isHermitian A₀ A₁) (Matrix.one_mul _)
    (jointMixedLastFrameProjectionMatrix_mul_self A₀ A₁)

private theorem firstFrameAtZeroProjection_comp_polarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedFirstFrameAtZeroProjection A₀ A₁ ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) =
      Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) := by
  change Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _ = Matrix.toEuclideanLin _
  rw [← Matrix.toLpLin_mul_same]
  congr 1
  unfold jointMixedTwoSitePolarFrame
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    jointMixedFirstFrameProjectionMatrix_mul_polarIso, Matrix.one_mul]

private theorem lastFrameAtOneProjection_comp_polarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedLastFrameAtOneProjection A₀ A₁ ∘ₗ
        Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) =
      Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁) := by
  change Matrix.toEuclideanLin _ ∘ₗ Matrix.toEuclideanLin _ = Matrix.toEuclideanLin _
  rw [← Matrix.toLpLin_mul_same]
  congr 1
  unfold jointMixedTwoSitePolarFrame
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
    jointMixedLastFrameProjectionMatrix_mul_polarIso, Matrix.one_mul]

/-- The actual support is contained in the first boundary frame at site
zero, with no restriction on the other site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstFrameAtZeroProjection_apply_of_mem_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)}
    (hv : v ∈ (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range) :
    jointMixedFirstFrameAtZeroProjection A₀ A₁ v = v := by
  obtain ⟨z, rfl⟩ := range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁ hv
  exact LinearMap.congr_fun (firstFrameAtZeroProjection_comp_polarFrame A₀ A₁) z

/-- The actual support is contained in the last boundary frame at site
one, with no restriction on the other site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastFrameAtOneProjection_apply_of_mem_support
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)}
    (hv : v ∈ (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range) :
    jointMixedLastFrameAtOneProjection A₀ A₁ v = v := by
  obtain ⟨z, rfl⟩ := range_blockInsertedBoundaryMap_jointMixed_le_polarFrame A₀ A₁ hv
  exact LinearMap.congr_fun (lastFrameAtOneProjection_comp_polarFrame A₀ A₁) z

/-- The first boundary frame at site zero reduces the actual interaction.
This is the local commutator for the first boundary of an open chain.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstFrameAtZeroProjection_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedFirstFrameAtZeroProjection A₀ A₁)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply (Commute.one_right _).sub_right
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedFirstFrameAtZeroProjection_isSymmetricProjection A₀ A₁).isSymmetric
  rintro _ ⟨v, hv, rfl⟩
  rwa [jointMixedFirstFrameAtZeroProjection_apply_of_mem_support A₀ A₁ hv]

/-- The last boundary frame at site one reduces the actual interaction.
This is the local commutator for the last boundary of an open chain.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastFrameAtOneProjection_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedLastFrameAtOneProjection A₀ A₁)
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply (Commute.one_right _).sub_right
  apply Submodule.commute_starProjection_of_invariant _ _
    (jointMixedLastFrameAtOneProjection_isSymmetricProjection A₀ A₁).isSymmetric
  rintro _ ⟨v, hv, rfl⟩
  rwa [jointMixedLastFrameAtOneProjection_apply_of_mem_support A₀ A₁ hv]

/-- The actual interaction penalizes the complement of its first
boundary frame. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedFirstFrameAtZeroProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedFirstFrameAtZeroProjection A₀ A₁ ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply sub_le_sub_left
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
    (jointMixedFirstFrameAtZeroProjection_isSymmetricProjection A₀ A₁) |>.mpr
  rw [Submodule.range_starProjection]
  intro v hv
  exact ⟨v, jointMixedFirstFrameAtZeroProjection_apply_of_mem_support A₀ A₁ hv⟩

/-- The actual interaction penalizes the complement of its last boundary
frame. Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem one_sub_jointMixedLastFrameAtOneProjection_le_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    1 - jointMixedLastFrameAtOneProjection A₀ A₁ ≤
      (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  apply sub_le_sub_left
  apply (Submodule.isSymmetricProjection_starProjection _).le_iff_range_le_range
    (jointMixedLastFrameAtOneProjection_isSymmetricProjection A₀ A₁) |>.mpr
  rw [Submodule.range_starProjection]
  intro v hv
  exact ⟨v, jointMixedLastFrameAtOneProjection_apply_of_mem_support A₀ A₁ hv⟩

end

end MPSTensor.MPOSymmetry
