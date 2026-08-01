/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BondTwoSingletonBaseModel
import TNLean.MPS.MPDO.InvariantProjection

/-!
# Physical similarities of the bond-two singleton base model

This module applies an invertible physical similarity to the explicit positive
MPO in `BondTwoSingletonBaseModel`.  Positivity of the resulting one- and
two-site operators forces the similarity's Gram matrix to be a positive scalar
multiple of the identity.  The concrete nonunitary gauge from
`BondTwoSingletonGramBoundary` therefore does not preserve the MPDO property.

The calculation is motivated by arXiv:1606.00608, Appendix C.4, lines
2048--2057, together with the metric argument of Proposition 4.13, lines
1898--1921.  It is a model-specific necessary-condition calculation, not a
theorem stated in the source.
-/

open scoped BigOperators ComplexOrder Matrix Kronecker

noncomputable section

open MPOTensor

namespace MPOTensor.BondTwoSingletonBaseModel

open BondTwoSingletonGramBoundary

private abbrev I := Fin 2

/-- The base MPO after ket-left multiplication by `X` and bra-right
multiplication by `X⁻¹`.

This is the physical-similarity deformation used in the model-specific
calculation motivated by arXiv:1606.00608, Appendix C.4, lines 2048--2057. -/
def gaugeDeformedBaseMPO (X : GL I ℂ) : MPOTensor 2 4 :=
  (baseMPO.ketLeftMul (X : Matrix I I ℂ)).braRightMul
    ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)

/-- The vertical tensor of the physically deformed MPO is the corresponding
letterwise similarity of the retained singleton tensor.

This is the explicit model attachment needed for the calculation motivated by
arXiv:1606.00608, Appendix C.4, lines 2048--2057; it is not a source theorem. -/
theorem verticalTensor_gaugeDeformedBaseMPO (X : GL I ℂ) :
    verticalTensor (gaugeDeformedBaseMPO X) = fun v ↦
      (X : Matrix I I ℂ) * singletonTensor v *
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ) := by
  funext v
  dsimp only [gaugeDeformedBaseMPO]
  rw [verticalTensor_braRightMul, verticalTensor_ketLeftMul,
    verticalTensor_baseMPO]

/-- After the canonical one-site reindexing, the deformed MPO is the similarity
of the terminal matrix `terminalJ`.

This is a model-specific one-site calculation motivated by
arXiv:1606.00608, Proposition 4.13, lines 1898--1921, not a theorem stated in
the source. -/
theorem oneSite_gaugeDeformedBaseMPO_eq_terminalJ (X : GL I ℂ) :
    Matrix.reindex (Equiv.funUnique (Fin 1) I) (Equiv.funUnique (Fin 1) I)
        (mpo (gaugeDeformedBaseMPO X) 1) =
      (X : Matrix I I ℂ) * terminalJ *
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.funUnique_symm_apply]
  change mpo (gaugeDeformedBaseMPO X) 1 (fun _ ↦ i) (fun _ ↦ j) = _
  rw [mpo_apply]
  unfold mpoMatrixEntry
  rw [List.ofFn_succ, List.ofFn_succ]
  simp only [evalWord_cons]
  simp [gaugeDeformedBaseMPO, ketLeftMul, braRightMul, baseMPO, Matrix.trace,
    terminalJ, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
    Matrix.single]
  have h00 : finProdFinEquiv ((0 : I), (0 : I)) = (0 : Fin 4) := by decide
  have h10 : finProdFinEquiv ((1 : I), (0 : I)) = (2 : Fin 4) := by decide
  have h01 : finProdFinEquiv ((0 : I), (1 : I)) = (1 : Fin 4) := by decide
  have h11 : finProdFinEquiv ((1 : I), (1 : I)) = (3 : Fin 4) := by decide
  simp [h00, h10, h01, h11]
  ring

/-- After the canonical two-site reindexing, the deformed MPO is the similarity
of the companion Bell projector, with `X ⊗ₖ X` on the left.

This is a model-specific two-site calculation motivated by
arXiv:1606.00608, Proposition 4.13, lines 1898--1921, not a theorem stated in
the source. -/
theorem twoSite_gaugeDeformedBaseMPO_eq_bellProjector (X : GL I ℂ) :
    Matrix.reindex (finTwoArrowEquiv I) (finTwoArrowEquiv I)
        (mpo (gaugeDeformedBaseMPO X) 2) =
      ((X : Matrix I I ℂ) ⊗ₖ (X : Matrix I I ℂ)) * bellProjector *
        (((X⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
          ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)) := by
  ext p q
  rcases p with ⟨p₀, p₁⟩
  rcases q with ⟨q₀, q₁⟩
  fin_cases p₀ <;> fin_cases p₁ <;> fin_cases q₀ <;> fin_cases q₁ <;>
    simp [Matrix.reindex_apply, mpo_apply, mpoMatrixEntry, evalWord,
      gaugeDeformedBaseMPO, ketLeftMul, braRightMul, baseMPO, Matrix.trace,
      bellProjector, bellVector, Matrix.vecMulVec, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, finTwoArrowEquiv, piFinTwoEquiv_apply, Matrix.single,
      finProdFinEquiv] <;> ring

/-- If the physically deformed base model is an MPDO, then the physical
similarity has positive scalar Gram matrix.

This model-specific necessary condition combines one- and two-site Hermiticity
with the metric calculation motivated by arXiv:1606.00608, Appendix C.4, lines
2048--2057, and Proposition 4.13, lines 1898--1921.  It is not a theorem stated
in the source. -/
theorem gaugeGram_eq_pos_smul_one_of_gaugeDeformedBaseMPO_isMPDO
    (X : GL I ℂ) (hM : IsMPDO (gaugeDeformedBaseMPO X)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ) = (ω : ℂ) • 1 := by
  apply gaugeGram_eq_pos_smul_one_of_terminal_companionBell_isHermitian X
  · have h := (hM 1 (by norm_num)).isHermitian.reindex
      (Equiv.funUnique (Fin 1) I)
    rwa [oneSite_gaugeDeformedBaseMPO_eq_terminalJ] at h
  · have h := (hM 2 (by norm_num)).isHermitian.reindex (finTwoArrowEquiv I)
    rwa [twoSite_gaugeDeformedBaseMPO_eq_bellProjector] at h

/-- The concrete nonunitary gauge has no scalar Gram matrix, strengthening
`gauge_gram_ne_one` to every real scalar.

This explicit obstruction supports the model-specific calculation motivated
by arXiv:1606.00608, Appendix C.4, lines 2048--2057; it is not a source
theorem. -/
lemma gauge_gram_ne_smul_one (ω : ℝ) :
    (gauge : Matrix I I ℂ)ᴴ * (gauge : Matrix I I ℂ) ≠ (ω : ℂ) • 1 := by
  intro h
  have h01 := congrArg (fun M : Matrix I I ℂ ↦ M 0 1) h
  norm_num [gaugeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Matrix.smul_apply, map_ofNat] at h01

/-- The concrete physical deformation by `gauge` is not an MPDO.

This is the model-specific obstruction motivated by arXiv:1606.00608,
Appendix C.4, lines 2048--2057, and Proposition 4.13, lines 1898--1921.  It is
not a theorem stated in the source. -/
theorem gaugeDeformedBaseMPO_gauge_not_isMPDO :
    ¬ IsMPDO (gaugeDeformedBaseMPO gauge) := by
  intro hM
  obtain ⟨ω, _hω, hGram⟩ :=
    gaugeGram_eq_pos_smul_one_of_gaugeDeformedBaseMPO_isMPDO gauge hM
  exact gauge_gram_ne_smul_one ω hGram

end MPOTensor.BondTwoSingletonBaseModel
