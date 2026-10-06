/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointBoundaryColumns
import TNLean.MPS.Symmetry.MPOSymmetry.JointInsertedBoundary
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Full joint boundary-frame support of the actual endpoint

The actual two-site coefficient is the trace of \(C_x^iV_xV_x^\dagger
C_x^jX_x\), summed over the block labels. Expanding its internal bond gives
an explicit coefficient vector in the product of the two joint boundary
column spaces. Thus the full extended support lies in
\(\operatorname{ran}L\otimes\operatorname{ran}R\), before cropping either
physical site. The same inclusion holds for the polar frames because
\(L=U_LP_L\) and \(R=U_RP_R\).

Every physical alphabet is retained. Block labels are summed coherently,
and neither an orthogonality assumption nor a positive dimension is used.
Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

/-- The product of the two full joint boundary column matrices, with its
physical rows written as two-site configurations.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSiteBoundaryColumns
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (JointMixedFirstBoundaryIndex D₀ D₁ × JointMixedLastBoundaryIndex D₀ D₁) ℂ :=
  (jointMixedFirstBoundaryColumns A₀ A₁ ⊗ₖ jointMixedLastBoundaryColumns A₀ A₁).submatrix
    (finTwoArrowEquiv _) id

/-- The product polar frame has the same two full physical sites and all
pairs of joint boundary coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSitePolarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Matrix (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2)
      (JointMixedFirstBoundaryIndex D₀ D₁ × JointMixedLastBoundaryIndex D₀ D₁) ℂ :=
  (Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
    Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)).submatrix (finTwoArrowEquiv _) id

/-- The internal first-endpoint bond joins two boundary columns with the
same block label. Labels are retained in the ambient product coordinate
space; the trace coefficient determines their coherent sum.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedTwoSiteBoundaryCoefficients
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    JointMixedFirstBoundaryIndex D₀ D₁ × JointMixedLastBoundaryIndex D₀ D₁ → ℂ :=
  ∑ x, ∑ a, ∑ e, ∑ b : Fin (D₀ x),
    X x e a • Pi.single (⟨x, a, b⟩, ⟨x, b, e⟩) 1

/-- The complete two-site inserted coefficient factors through the product
of the two actual joint boundary column matrices. This identity starts
from the actual trace contraction and does not crop either physical site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (X : (x : Fin r) → Matrix (Fin (D₀ x + D₁ x)) (Fin (D₀ x + D₁ x)) ℂ) :
    blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 X =
      jointMixedTwoSiteBoundaryColumns A₀ A₁ *ᵥ jointMixedTwoSiteBoundaryCoefficients X := by
  classical
  ext σ
  have hword : List.ofFn σ = σ 0 :: ([] ++ [σ 1]) := by
    rw [show σ = ![σ 0, σ 1] from ((finTwoArrowEquiv _).left_inv σ).symm]
    simp
  simp only [blockInsertedGroundSpaceMap_apply, Finset.sum_apply,
    insertedGroundSpaceMap_apply, hword, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    jointMixedTwoSiteBoundaryCoefficients, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul,
    jointMixedTwoSiteBoundaryColumns, Matrix.col_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, finTwoArrowEquiv_apply, id_eq]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  rw [show σ 0 :: ([] ++ [σ 1]) =
    σ 0 :: (([] : List (Fin d₀)).map (jointMixedFirstPhysicalIndex d₁ D₀ D₁) ++
      [σ 1]) from rfl, jointMixedEndpoint_insertedEvalWord_originalBulk]
  simp [Kraus.evalWord, Matrix.one_apply, mul_comm, Finset.mul_sum]

/-- The actual product columns are obtained from the product polar frame
by the two joint positive factors. No change occurs at an interior site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSiteBoundaryColumns_eq_polarFrame_mul
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedTwoSiteBoundaryColumns A₀ A₁ =
      jointMixedTwoSitePolarFrame A₀ A₁ *
        (Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
          Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)) := by
  unfold jointMixedTwoSiteBoundaryColumns jointMixedTwoSitePolarFrame
  calc
    _ = ((Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
        Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)) *
          (Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
            Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁))).submatrix
              (finTwoArrowEquiv _) id := by
      rw [← Matrix.mul_kronecker_mul, Matrix.polarIso_mul_polarPos,
        Matrix.polarIso_mul_polarPos]
    _ = _ := Matrix.submatrix_mul _ _ _ id id Function.bijective_id

/-- The actual Hilbert-space support lies in the full product column
range. This includes empty block labels, zero endpoint fibers, and unused
directions in either physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_le_boundaryColumns
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range ≤
        (Matrix.toEuclideanLin (jointMixedTwoSiteBoundaryColumns A₀ A₁)).range := by
  rintro _ ⟨v, rfl⟩
  refine ⟨WithLp.toLp 2 (jointMixedTwoSiteBoundaryCoefficients (blockBoundaryEquiv v)), ?_⟩
  apply PiLp.ext
  intro σ
  exact congrFun
    (blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns A₀ A₁
      (blockBoundaryEquiv v)).symm σ

/-- The same actual support lies in the product polar-frame range. This
uses only polar reconstruction, so no injectivity premise is necessary.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem range_blockInsertedBoundaryMap_jointMixed_le_polarFrame
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range ≤
        (Matrix.toEuclideanLin (jointMixedTwoSitePolarFrame A₀ A₁)).range := by
  apply le_trans (range_blockInsertedBoundaryMap_jointMixed_le_boundaryColumns A₀ A₁)
  rintro _ ⟨v, rfl⟩
  refine ⟨Matrix.toEuclideanLin
    (Matrix.polarPos (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
      Matrix.polarPos (jointMixedLastBoundaryColumns A₀ A₁)) v, ?_⟩
  rw [jointMixedTwoSiteBoundaryColumns_eq_polarFrame_mul]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]

/-- Simultaneous one-site spanning makes the full rectangular product
polar frame isometric. It need not cover the entire physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedTwoSitePolarFrame_isIsometry
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    (jointMixedTwoSitePolarFrame A₀ A₁).IsIsometry := by
  have hL := Matrix.isIsometry_polarIso_of_injective _
    (jointMixedFirstBoundaryColumns_injective A₀ A₁ h₀ h₁)
  have hR := Matrix.isIsometry_polarIso_of_injective _
    (jointMixedLastBoundaryColumns_injective A₀ A₁ h₀ h₁)
  have hprod : (Matrix.polarIso (jointMixedFirstBoundaryColumns A₀ A₁) ⊗ₖ
      Matrix.polarIso (jointMixedLastBoundaryColumns A₀ A₁)).IsIsometry :=
    Matrix.IsIsometry.kronecker _ _ hL hR
  exact hprod.reindex _ (finTwoArrowEquiv _).symm (Equiv.refl _)

end

end MPSTensor.MPOSymmetry
