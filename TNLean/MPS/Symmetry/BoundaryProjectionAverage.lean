/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.BoundaryParentCommutation
import TNLean.MPS.Symmetry.BoundaryUnitSupport
import TNLean.MPS.ParentHamiltonian.NonzeroInteraction

/-!
# Boundary averaging of the canonical MPS support

Write \(O_X\) for the actual length-\(n\) MPO with boundary \(X\),
\(Q_n=O_U\), and \(P_n\) for the canonical orthogonal projection onto the
MPS ground space. Length-independent boundary compatibility, a physical unit
at one positive injectivity length, and adjoint closure at the target length
imply \(Q_nP_n=P_n\) and \(P_nO_X=O_XP_n\).

For any finite boundary families satisfying the unit normalization
\(\sum_i O_{X_i}O_{Y_i}=Q_n\), these derived identities give
\(\sum_i O_{X_i}P_nO_{Y_i}=P_n\). Averaging the canonical parent therefore
gives \(Q_n-P_n\), whereas the ambient complement of the averaged support
is \(I-P_n\). The latter is nonzero when \(d^n>D^2\).

**Scope restriction (averaging hypotheses):** this is a consequence of the
normalization in GLM23 Appendix B, not a construction of its weak-Hopf
representation, canonical integral, or boundary normalization. Adjoint closure
and a positive injectivity/calibration length are explicit sufficient
hypotheses. The calibration and target lengths may differ in either direction.
The finite index type and physical and bond dimensions may be empty. Neither
\(Q_n=I\) nor nonzeroness of the literal averaged parent is asserted.
See `docs/paper-gaps/glm23_wha_parent_completion.tex`.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `eq:compatible`,
  lines 431--469; Section 5, lines 1276--1320; Appendix B, lines 2463--2466.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D₁ D₂ L n : ℕ} {T : MPOTensor d D₁} {A : MPSTensor d D₂}

attribute [local instance] MPSTensor.groundSpaceES_hasOrthogonalProjection

/-- Adjoint closure of the actual boundary range makes the canonical support
projection commute with every boundary operator. This is the orthogonal
reduction used in GLM23 Appendix B, lines 2463--2466; no averaging identity
is assumed. The closure hypothesis is explicit as in
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem IsBoundaryCompatible.groundSpaceES_starProjection_commute_mpoWithBoundary
    (h : IsBoundaryCompatible T A) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X n)ᴴ = mpoWithBoundary T Y n)
    (X : Matrix (Fin D₁) (Fin D₁) ℂ) :
    Commute (MPSTensor.groundSpaceES A n).starProjection.toLinearMap
      (Matrix.toEuclideanLin (mpoWithBoundary T X n)) := by
  apply LinearMap.ext
  intro ψ
  change (MPSTensor.groundSpaceES A n).starProjection
      (Matrix.toEuclideanLin (mpoWithBoundary T X n) ψ) =
    Matrix.toEuclideanLin (mpoWithBoundary T X n)
      ((MPSTensor.groundSpaceES A n).starProjection ψ)
  let S := StarAlgebra.adjoin ℂ (Set.range (fun Y ↦ mpoWithBoundary T Y n))
  exact S.starProjection_toEuclideanLin_comm
    (h.groundSpaceES_invariant_boundaryStarAlgebra hn hstar)
    (StarAlgebra.subset_adjoin ℂ _ ⟨X, rfl⟩) ψ

variable {ι : Type*} [Fintype ι]

/-- The standard unit normalization alone makes a finite boundary average
fix the canonical support projection, once unit support and commutation have
been derived from compatibility, calibration, and adjoint closure.

This proves the averaging consequence relevant to GLM23 Appendix B,
lines 2463--2466. The finite families and their normalization are supplied,
not constructed from a weak-Hopf integral; see
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem IsBoundaryCompatible.sum_mpoWithBoundary_groundSpaceES_starProjection
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X n)ᴴ = mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, mpoWithBoundary T (X i) n * mpoWithBoundary T (Y i) n =
      mpoWithBoundary T U n) :
    (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) =
      (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  have hsum :
      (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
        Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) =
      Matrix.toEuclideanLin (mpoWithBoundary T U n) := by
    simpa only [Matrix.toEuclideanLin, map_sum, Matrix.toLpLin_mul_same,
      Module.End.mul_eq_comp] using
      congrArg Matrix.toEuclideanLin hXY
  calc
    _ = (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
          Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc,
        (h.groundSpaceES_starProjection_commute_mpoWithBoundary hn hstar (Y i)).eq,
        ← mul_assoc]
    _ = _ := by
      rw [hsum]
      exact h.toEuclideanLin_comp_groundSpaceES_starProjection hInj hL hU hn

/-- Averaging the canonical parent gives \(Q_n-P_n\), which can vanish even
when the ambient complement \(I-P_n\) is nonzero. This is the linearity
consequence of the normalization in GLM23 Appendix B, lines 2463--2466,
with its distinction from ambient completion recorded in
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem IsBoundaryCompatible.sum_mpoWithBoundary_parentInteractionES
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X n)ᴴ = mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, mpoWithBoundary T (X i) n * mpoWithBoundary T (Y i) n =
      mpoWithBoundary T U n) :
    (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
        MPSTensor.parentInteractionES A n *
        Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) =
      Matrix.toEuclideanLin (mpoWithBoundary T U n) -
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap := by
  rw [MPSTensor.parentInteractionES, Submodule.starProjection_orthogonal']
  change (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
      (1 - (MPSTensor.groundSpaceES A n).starProjection.toLinearMap) *
      Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) = _
  simp only [mul_sub, mul_one, sub_mul, Finset.sum_sub_distrib]
  rw [h.sum_mpoWithBoundary_groundSpaceES_starProjection hInj hL hU hn hstar X Y hXY]
  congr 1
  simpa only [Matrix.toEuclideanLin, map_sum, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using
    congrArg Matrix.toEuclideanLin hXY

/-- The ambient complement of the averaged support is the original canonical
parent. This is the completed construction associated with GLM23 Appendix B,
lines 2463--2466, under the explicit sufficient hypotheses; it does not
identify this complement with the literal average of the parent.
See `docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X n)ᴴ = mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, mpoWithBoundary T (X i) n * mpoWithBoundary T (Y i) n =
      mpoWithBoundary T U n) :
    1 - (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) =
      MPSTensor.parentInteractionES A n := by
  rw [h.sum_mpoWithBoundary_groundSpaceES_starProjection hInj hL hU hn hstar X Y hXY,
    MPSTensor.parentInteractionES, Submodule.starProjection_orthogonal']
  rfl

/-- The ambient complement of the averaged support is nonzero if
\(d^n>D_2^2\). This sufficient proper-support criterion complements the
averaging argument of GLM23 Appendix B, lines 2463--2466. No corresponding
claim is made for the literal average \(Q_n-P_n\); see
`docs/paper-gaps/glm23_wha_parent_completion.tex`. -/
theorem IsBoundaryCompatible.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection_ne_zero
    (h : IsBoundaryCompatible T A) (hInj : Kraus.IsNBlkInjective A L)
    (hL : 0 < L) {U : Matrix (Fin D₁) (Fin D₁) ℂ}
    (hU : mpoWithBoundary T U L = 1) (hn : 0 < n)
    (hstar : ∀ X : Matrix (Fin D₁) (Fin D₁) ℂ,
      ∃ Y : Matrix (Fin D₁) (Fin D₁) ℂ,
        (mpoWithBoundary T X n)ᴴ = mpoWithBoundary T Y n)
    (X Y : ι → Matrix (Fin D₁) (Fin D₁) ℂ)
    (hXY : ∑ i, mpoWithBoundary T (X i) n * mpoWithBoundary T (Y i) n =
      mpoWithBoundary T U n) (hDim : d ^ n > D₂ ^ 2) :
    1 - (∑ i, Matrix.toEuclideanLin (mpoWithBoundary T (X i) n) *
        (MPSTensor.groundSpaceES A n).starProjection.toLinearMap *
        Matrix.toEuclideanLin (mpoWithBoundary T (Y i) n)) ≠ 0 := by
  rw [h.one_sub_sum_mpoWithBoundary_groundSpaceES_starProjection
    hInj hL hU hn hstar X Y hXY]
  exact MPSTensor.parentInteractionES_ne_zero A n hDim

end MPOTensor
