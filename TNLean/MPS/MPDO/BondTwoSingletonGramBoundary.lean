/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.ZCL
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Bond-two singleton Gram boundary

This module isolates the finite-dimensional obstruction behind the bond-two
singleton model suggested by the terminal-positivity boundary.  The one-site
operator is the rank-one all-ones matrix and the two-site operator is the
unnormalized Bell projector.  Similarity by a nonunitary matrix commuting with
the one-site operator preserves the positive terminal matrix, but its tensor
square makes the Bell projector non-Hermitian.

The converse uses only Hermiticity at lengths one and two.  Hermiticity of a
similarity forces its positive Gram matrix to commute with the original
Hermitian operator.  The one-site commutator and one off-diagonal coordinate
of the two-site Bell commutator then force the Gram matrix to be a positive
scalar multiple of the identity.

This is a model-specific necessary-condition result motivated by
arXiv:1606.00608, Appendix C.4, lines 2048--2057, and Proposition 4.13,
lines 1898--1921.  It does not construct a tensor-attached BNT algebra clause
or an all-length MPDO realization.
-/

open scoped Matrix ComplexOrder Kronecker

noncomputable section

namespace MPOTensor.BondTwoSingletonGramBoundary

private abbrev I := Fin 2
private abbrev I₂ := I × I

/-- The singleton retained tensor.  Its four diagonal doubled-physical letters
are the standard two-by-two matrix units, and all off-diagonal doubled-physical
letters vanish.

This model tests the marked comparison sought in arXiv:1606.00608,
Appendix C.4, lines 2048--2057; it is not a tensor stated in the source. -/
def singletonTensor : MPSTensor (4 * 4) 2 :=
  fun v ↦
    let p := finProdFinEquiv.symm v
    let ab := finProdFinEquiv.symm p.1
    if p.1 = p.2 then Matrix.single ab.1 ab.2 1 else 0

@[simp]
lemma singletonTensor_diagonal (a b : I) :
    singletonTensor
        (finProdFinEquiv (finProdFinEquiv (a, b), finProdFinEquiv (a, b))) =
      Matrix.single a b 1 := by
  simp [singletonTensor]

/-- The four diagonal letters span the full bond-two matrix algebra. -/
lemma singletonTensor_isInjective : singletonTensor.IsInjective := by
  rw [MPSTensor.IsInjective, eq_top_iff]
  intro M _
  have hsingle : ∀ a b : I, Matrix.single a b (1 : ℂ) ∈
      Submodule.span ℂ (Set.range singletonTensor) := by
    intro a b
    rw [← singletonTensor_diagonal a b]
    exact Submodule.subset_span ⟨_, rfl⟩
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ (fun a _ ↦ Submodule.sum_mem _ (fun b _ ↦ ?_))
  rw [show Matrix.single a b (M a b) =
      M a b • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (hsingle a b)

/-- The singleton retained tensor is normal at word length one. -/
lemma singletonTensor_isNormal : singletonTensor.IsNormal :=
  singletonTensor_isInjective.isNormal

/-- The unnormalized one-site GHZ projector, also the terminal all-ones matrix. -/
def terminalJ : Matrix I I ℂ :=
  !![1, 1; 1, 1]

/-- The terminal physical-trace transfer of the matrix-unit singleton tensor is
exactly the all-ones matrix.  This is the one-site necessary condition derived
from the setting of arXiv:1606.00608, Proposition 4.13, lines 1898--1921. -/
lemma physTraceTransfer_singletonTensor :
    physTraceTransfer (verticalBNTMPO singletonTensor) = terminalJ := by
  unfold physTraceTransfer
  change (∑ i : Fin 4,
    singletonTensor (finProdFinEquiv (i, i))) = terminalJ
  calc
    (∑ i : Fin 4, singletonTensor (finProdFinEquiv (i, i))) =
        ∑ ab : I × I, singletonTensor
          (finProdFinEquiv (finProdFinEquiv ab, finProdFinEquiv ab)) :=
      (Equiv.sum_comp (finProdFinEquiv : I × I ≃ Fin 4)
        (fun i : Fin 4 ↦ singletonTensor (finProdFinEquiv (i, i)))).symm
    _ = terminalJ := by
      rw [Fintype.sum_prod_type]
      simp only [singletonTensor_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [terminalJ, Fin.sum_univ_two, Matrix.single]

/-- The unnormalized Bell vector on two binary sites. -/
def bellVector : I₂ → ℂ :=
  fun x ↦ if x.1 = x.2 then 1 else 0

/-- The unnormalized two-site Bell projector. -/
def bellProjector : Matrix I₂ I₂ ℂ :=
  Matrix.vecMulVec bellVector (star bellVector)

/-- The terminal all-ones matrix is positive semidefinite. -/
lemma terminalJ_posSemidef : terminalJ.PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : I ↦ (1 : ℂ)) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [terminalJ, Matrix.vecMulVec]

/-- The two-site Bell operator is positive semidefinite. -/
lemma bellProjector_posSemidef : bellProjector.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star bellVector

private lemma gram_commutes_of_similarity_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    (S T P : Matrix n n ℂ) (hTS : T * S = 1)
    (hP : P.IsHermitian) (hSim : (S * P * T).IsHermitian) :
    (Sᴴ * S) * P = P * (Sᴴ * S) := by
  have hTSstar : Sᴴ * Tᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hTS, Matrix.conjTranspose_one]
  have hAdj : S * P * T = Tᴴ * P * Sᴴ := by
    rw [← hSim.eq]
    simp only [Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  calc
    (Sᴴ * S) * P = Sᴴ * (S * P * T) * S := by
      simp only [Matrix.mul_assoc, hTS, Matrix.mul_one]
    _ = Sᴴ * (Tᴴ * P * Sᴴ) * S := by rw [hAdj]
    _ = (Sᴴ * Tᴴ) * P * (Sᴴ * S) := by
      simp only [Matrix.mul_assoc]
    _ = P * (Sᴴ * S) := by rw [hTSstar, Matrix.one_mul]

/-- A positive definite two-by-two matrix commuting with the terminal matrix
and satisfying the Bell-cross coordinate is a positive scalar matrix.

This is a model-specific necessary condition for the comparison attempted in
arXiv:1606.00608, Appendix C.4, lines 2048--2057; it is not asserted there as
a separate theorem. -/
theorem posDef_eq_pos_smul_one_of_commutes_terminalJ_of_bellCross
    {G : Matrix I I ℂ} (hG : G.PosDef)
    (hcomm : G * terminalJ = terminalJ * G)
    (hcross : G 0 0 * G 0 1 + G 1 0 * G 1 1 = 0) :
    ∃ ω : ℝ, 0 < ω ∧ G = (ω : ℂ) • 1 := by
  have h00 := congrArg (fun M : Matrix I I ℂ ↦ M 0 0) hcomm
  have h01 := congrArg (fun M : Matrix I I ℂ ↦ M 0 1) hcomm
  have h10 := congrArg (fun M : Matrix I I ℂ ↦ M 1 0) hcomm
  simp only [Matrix.mul_apply, Fin.sum_univ_two, terminalJ] at h00 h01 h10
  norm_num at h00 h01 h10
  have hoff : G 0 1 = G 1 0 := by linear_combination h00
  have hdiag : G 0 0 = G 1 1 := by linear_combination h01
  have hdiagPos : (0 : ℂ) < G 0 0 := hG.diag_pos
  have hzero : G 0 1 = 0 := by
    have hdiagNe : G 0 0 ≠ 0 := ne_of_gt hdiagPos
    apply (mul_eq_zero.mp ?_).resolve_left hdiagNe
    calc
      G 0 0 * G 0 1 = (G 0 0 * G 0 1 + G 1 0 * G 1 1) / 2 := by
        rw [hoff, ← hdiag]
        ring
      _ = 0 := by rw [hcross]; norm_num
  have hω : 0 < (G 0 0).re := (Complex.pos_iff.mp hdiagPos).1
  refine ⟨(G 0 0).re, hω, ?_⟩
  have h00real : ((G 0 0).re : ℂ) = G 0 0 := by
    obtain ⟨_, him⟩ := Complex.pos_iff.mp hdiagPos
    exact Complex.ext (by simp) (by simpa using him)
  ext i j
  fin_cases i <;> fin_cases j
  · change G 0 0 = _
    simpa [Matrix.smul_apply] using h00real.symm
  · change G 0 1 = _
    simp [Matrix.smul_apply, hzero]
  · change G 1 0 = _
    rw [← hoff, hzero]
    simp [Matrix.smul_apply]
  · change G 1 1 = _
    rw [← hdiag, ← h00real]
    simp [Matrix.smul_apply]

/-- The concrete nonunitary similarity used for the deformation. -/
def gaugeMatrix : Matrix I I ℂ :=
  !![3 / 2, 1 / 2; 1 / 2, 3 / 2]

private lemma gaugeMatrix_det_ne_zero : gaugeMatrix.det ≠ 0 := by
  norm_num [gaugeMatrix, Matrix.det_fin_two]

/-- The concrete matrix as an invertible bond-two gauge. -/
def gauge : GL I ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero gaugeMatrix gaugeMatrix_det_ne_zero

@[simp] lemma gauge_val : (gauge : Matrix I I ℂ) = gaugeMatrix :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

@[simp] lemma gauge_inv_val :
    ((gauge⁻¹ : GL I ℂ) : Matrix I I ℂ) =
      !![3 / 4, -1 / 4; -1 / 4, 3 / 4] := by
  have h : gauge * Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![3 / 4, -1 / 4; -1 / 4, 3 / 4] : Matrix I I ℂ)
      (by norm_num [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gaugeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show gauge⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![3 / 4, -1 / 4; -1 / 4, 3 / 4] : Matrix I I ℂ)
      (by norm_num [Matrix.det_fin_two]) from inv_eq_of_mul_eq_one_right h]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- Similarity deformation of the one-site terminal operator. -/
def deformedOneSite : Matrix I I ℂ :=
  (gauge : Matrix I I ℂ) * terminalJ *
    ((gauge⁻¹ : GL I ℂ) : Matrix I I ℂ)

/-- Similarity deformation of the two-site Bell operator by the tensor-square gauge. -/
def deformedTwoSite : Matrix I₂ I₂ ℂ :=
  ((gauge : Matrix I I ℂ) ⊗ₖ (gauge : Matrix I I ℂ)) * bellProjector *
    (((gauge⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
      ((gauge⁻¹ : GL I ℂ) : Matrix I I ℂ))

/-- The concrete similarity commutes with the terminal matrix. -/
lemma gauge_commutes_terminalJ :
    (gauge : Matrix I I ℂ) * terminalJ = terminalJ * (gauge : Matrix I I ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeMatrix, terminalJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The one-site deformation leaves the positive terminal matrix unchanged. -/
lemma deformedOneSite_eq_terminalJ : deformedOneSite = terminalJ := by
  rw [deformedOneSite, gauge_commutes_terminalJ, Matrix.mul_assoc]
  change terminalJ * ((gauge * gauge⁻¹ : GL I ℂ) : Matrix I I ℂ) = terminalJ
  simp

/-- The one-site deformation remains positive semidefinite. -/
lemma deformedOneSite_posSemidef : deformedOneSite.PosSemidef := by
  rw [deformedOneSite_eq_terminalJ]
  exact terminalJ_posSemidef

/-- The concrete tensor-square deformation of the Bell projector is not
Hermitian.  This excludes this deformation from the positive ambient setting
of arXiv:1606.00608, Proposition 4.13, lines 1898--1921. -/
lemma deformedTwoSite_not_isHermitian : ¬ deformedTwoSite.IsHermitian := by
  intro h
  have hentry := congrArg
    (fun M : Matrix I₂ I₂ ℂ ↦ M (0, 0) (0, 1)) h.eq
  rw [deformedTwoSite, gauge_val, gauge_inv_val] at hentry
  norm_num [bellProjector, bellVector, gaugeMatrix, Matrix.vecMulVec,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two] at hentry

private lemma bellCross_of_kronecker_commutes
    (G : Matrix I I ℂ)
    (hcomm : (G ⊗ₖ G) * bellProjector = bellProjector * (G ⊗ₖ G)) :
    G 0 0 * G 0 1 + G 1 0 * G 1 1 = 0 := by
  have h := congrArg (fun M : Matrix I₂ I₂ ℂ ↦ M (0, 0) (0, 1)) hcomm
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, bellProjector,
    bellVector, Matrix.vecMulVec, Fintype.sum_prod_type,
    Fin.sum_univ_two] at h
  exact h.symm

/-- Hermiticity of the one-site similarity forces the gauge Gram matrix to
commute with the terminal all-ones matrix.

This is the one-site part of the model-specific boundary motivated by
arXiv:1606.00608, Appendix C.4, lines 2048--2057. -/
lemma gaugeGram_commutes_terminalJ_of_oneSite_isHermitian
    (X : GL I ℂ)
    (h : ((X : Matrix I I ℂ) * terminalJ *
      ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)).IsHermitian) :
    ((X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ)) * terminalJ =
      terminalJ * ((X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ)) := by
  apply gram_commutes_of_similarity_isHermitian
    (S := (X : Matrix I I ℂ))
    (T := ((X⁻¹ : GL I ℂ) : Matrix I I ℂ))
  · rw [← Units.val_mul]
    simp
  · exact terminalJ_posSemidef.isHermitian
  · exact h

/-- Hermiticity of the two-site tensor-square similarity gives the Bell-cross
equation for the gauge Gram matrix.

This is the two-site part of the model-specific boundary motivated by
arXiv:1606.00608, Appendix C.4, lines 2048--2057. -/
lemma gaugeGram_bellCross_of_twoSite_isHermitian
    (X : GL I ℂ)
    (h : (((X : Matrix I I ℂ) ⊗ₖ (X : Matrix I I ℂ)) * bellProjector *
      (((X⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ))).IsHermitian) :
    let G := (X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ)
    G 0 0 * G 0 1 + G 1 0 * G 1 1 = 0 := by
  let S : Matrix I₂ I₂ ℂ :=
    (X : Matrix I I ℂ) ⊗ₖ (X : Matrix I I ℂ)
  let T : Matrix I₂ I₂ ℂ :=
    ((X⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
      ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)
  have hTS : T * S = 1 := by
    dsimp only [S, T]
    rw [← Matrix.mul_kronecker_mul]
    change (((X⁻¹ * X : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
      ((X⁻¹ * X : GL I ℂ) : Matrix I I ℂ)) = 1
    simp
  have hcomm := gram_commutes_of_similarity_isHermitian S T bellProjector
    hTS bellProjector_posSemidef.isHermitian h
  have hGram : Sᴴ * S =
      (((X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ)) ⊗ₖ
        ((X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ))) := by
    dsimp only [S]
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
  rw [hGram] at hcomm
  exact bellCross_of_kronecker_commutes _ hcomm

/-- Model-specific Gram no-go: an invertible bond-two gauge whose one-site and
two-site GHZ-projector similarities are Hermitian has positive scalar Gram
matrix.

This is a necessary-condition theorem motivated by arXiv:1606.00608,
Appendix C.4, lines 2048--2057, and Proposition 4.13, lines 1898--1921.  It
does not construct the marked common-target realization missing from the
source argument. -/
theorem gaugeGram_eq_pos_smul_one_of_one_two_isHermitian
    (X : GL I ℂ)
    (hOne : ((X : Matrix I I ℂ) * terminalJ *
      ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)).IsHermitian)
    (hTwo : (((X : Matrix I I ℂ) ⊗ₖ (X : Matrix I I ℂ)) * bellProjector *
      (((X⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ))).IsHermitian) :
    ∃ ω : ℝ, 0 < ω ∧
      (X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ) = (ω : ℂ) • 1 := by
  let G : Matrix I I ℂ := (X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ)
  have hXunit : IsUnit (X : Matrix I I ℂ) := X.isUnit
  have hG : G.PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_of_isUnit hXunit)
  exact posDef_eq_pos_smul_one_of_commutes_terminalJ_of_bellCross hG
    (gaugeGram_commutes_terminalJ_of_oneSite_isHermitian X hOne)
    (gaugeGram_bellCross_of_twoSite_isHermitian X hTwo)

end MPOTensor.BondTwoSingletonGramBoundary
