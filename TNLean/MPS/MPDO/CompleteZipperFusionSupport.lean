/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CompleteZipperFusionDefs

/-!
# Triple reconstruction from complete zipper fusion

This file proves the two-stage triple-fusion identities and reconstructs the
common triple-product support from the source-faithful zipper hypotheses.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

universe u

namespace CompleteZipperFusionFamily

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fus : CompleteZipperFusionFamily Λ p)

private abbrev LeftFirstStage (a b c : Λ) : Type u :=
  ((e : Λ) × (Fin (Fus.fusionMultiplicity a b e) × Fin (Fus.bondDim e))) ×
    Fin (Fus.bondDim c)

private abbrev LeftFirstStageNested (a b c : Λ) : Type u :=
  (e : Λ) × (Fin (Fus.fusionMultiplicity a b e) ×
    (Fin (Fus.bondDim e) × Fin (Fus.bondDim c)))

private abbrev LeftFinalNested (a b c : Λ) : Type u :=
  (e : Λ) × (Fin (Fus.fusionMultiplicity a b e) ×
    ((d : Λ) × (Fin (Fus.fusionMultiplicity e c d) × Fin (Fus.bondDim d))))

private def leftFirstStageEquiv (a b c : Λ) :
    Fus.LeftFirstStage a b c ≃ Fus.LeftFirstStageNested a b c :=
  (Equiv.sigmaProdDistrib
    (fun e => Fin (Fus.fusionMultiplicity a b e) × Fin (Fus.bondDim e))
    (Fin (Fus.bondDim c))).trans
      (Equiv.sigmaCongrRight fun _ => Equiv.prodAssoc _ _ _)

private def leftFinalFlattenEquiv (a b c : Λ) :
    Fus.LeftFinalNested a b c ≃ Fus.LeftTripleIndex a b c where
  toFun x := ⟨x.2.2.1, ⟨⟨x.1, x.2.1, x.2.2.2.1⟩, x.2.2.2.2⟩⟩
  invFun x := ⟨x.2.1.1, ⟨x.2.1.2.1, ⟨x.1, x.2.1.2.2, x.2.2⟩⟩⟩
  left_inv := by rintro ⟨e, μ, d, ν, z⟩; rfl
  right_inv := by rintro ⟨d, ⟨e, μ, ν⟩, z⟩; rfl

private noncomputable def leftFirstSynthesis (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.LeftFirstStage a b c) ℂ :=
  Fus.fusionSynthesis a b ⊗ₖ
    (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)

private noncomputable def leftFirstAnalysis (a b c : Λ) :
    Matrix (Fus.LeftFirstStage a b c) (Fus.TripleBond a b c) ℂ :=
  Fus.fusionAnalysis a b ⊗ₖ
    (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)

private noncomputable def leftSecondSynthesis (a b c : Λ) :
    Matrix (Fus.LeftFirstStage a b c) (Fus.LeftTripleIndex a b c) ℂ :=
  (Matrix.blockDiagonal' fun e =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
      (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionSynthesis e c).submatrix
        (Fus.leftFirstStageEquiv a b c) (Fus.leftFinalFlattenEquiv a b c).symm

private noncomputable def leftSecondAnalysis (a b c : Λ) :
    Matrix (Fus.LeftTripleIndex a b c) (Fus.LeftFirstStage a b c) ℂ :=
  (Matrix.blockDiagonal' fun e =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
      (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionAnalysis e c).submatrix
        (Fus.leftFinalFlattenEquiv a b c).symm (Fus.leftFirstStageEquiv a b c)

private theorem leftSynthesisFull_eq_stages (a b c : Λ) :
    Fus.leftTripleSynthesisFull a b c =
      Fus.leftFirstSynthesis a b c * Fus.leftSecondSynthesis a b c := by
  classical
  funext ⟨⟨xa, xb⟩, xc⟩ ⟨d, ⟨⟨e, μ, ν⟩, z⟩⟩
  simp [leftTripleSynthesisFull, leftTripleSynthesis, leftFirstSynthesis,
    leftSecondSynthesis, leftFirstStageEquiv, leftFinalFlattenEquiv,
    fusionTensor, Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
    Matrix.blockDiagonal'_apply, Matrix.one_apply]

private theorem leftAnalysisFull_eq_stages (a b c : Λ) :
    Fus.leftTripleAnalysisFull a b c =
      Fus.leftSecondAnalysis a b c * Fus.leftFirstAnalysis a b c := by
  classical
  funext ⟨d, ⟨⟨e, μ, ν⟩, z⟩⟩ ⟨⟨xa, xb⟩, xc⟩
  simp [leftTripleAnalysisFull, leftTripleAnalysis, leftFirstAnalysis,
    leftSecondAnalysis, leftFirstStageEquiv, leftFinalFlattenEquiv,
    fusionTensorLeftInverse, Matrix.mul_apply, Fintype.sum_sigma,
    Fintype.sum_prod_type, Matrix.blockDiagonal'_apply, Matrix.one_apply]

private theorem leftFirstAnalysis_mul_synthesis (a b c : Λ) :
    Fus.leftFirstAnalysis a b c * Fus.leftFirstSynthesis a b c = 1 := by
  rw [leftFirstSynthesis, leftFirstAnalysis, ← Matrix.mul_kronecker_mul,
    Fus.analysis_mul_synthesis, Matrix.one_mul, Matrix.one_kronecker_one]

private theorem leftSecondAnalysis_mul_synthesis (a b c : Λ) :
    Fus.leftSecondAnalysis a b c * Fus.leftSecondSynthesis a b c = 1 := by
  unfold leftSecondSynthesis leftSecondAnalysis
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.leftFirstStageEquiv a b c) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul, Fus.analysis_mul_synthesis, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal'
    (1 : (e : Λ) → Matrix
      (Fin (Fus.fusionMultiplicity a b e) ×
        ((d : Λ) × (Fin (Fus.fusionMultiplicity e c d) × Fin (Fus.bondDim d))))
      (Fin (Fus.fusionMultiplicity a b e) ×
        ((d : Λ) × (Fin (Fus.fusionMultiplicity e c d) × Fin (Fus.bondDim d)))) ℂ)).submatrix
          (Fus.leftFinalFlattenEquiv a b c).symm
          (Fus.leftFinalFlattenEquiv a b c).symm = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private abbrev RightFirstStage (a b c : Λ) : Type u :=
  Fin (Fus.bondDim a) ×
    ((f : Λ) × (Fin (Fus.fusionMultiplicity b c f) × Fin (Fus.bondDim f)))

private abbrev RightFirstStageNested (a b c : Λ) : Type u :=
  (f : Λ) × (Fin (Fus.fusionMultiplicity b c f) ×
    (Fin (Fus.bondDim a) × Fin (Fus.bondDim f)))

private abbrev RightFinalNested (a b c : Λ) : Type u :=
  (f : Λ) × (Fin (Fus.fusionMultiplicity b c f) ×
    ((d : Λ) × (Fin (Fus.fusionMultiplicity a f d) × Fin (Fus.bondDim d))))

private def rightBondAssocEquiv (a b c : Λ) :
    Fus.TripleBond a b c ≃
      Fin (Fus.bondDim a) × (Fin (Fus.bondDim b) × Fin (Fus.bondDim c)) :=
  Equiv.prodAssoc _ _ _

private def rightFirstStageEquiv (a b c : Λ) :
    Fus.RightFirstStage a b c ≃ Fus.RightFirstStageNested a b c where
  toFun x := ⟨x.2.1, x.2.2.1, x.1, x.2.2.2⟩
  invFun x := ⟨x.2.2.1, ⟨x.1, x.2.1, x.2.2.2⟩⟩
  left_inv := by rintro ⟨x, f, l, y⟩; rfl
  right_inv := by rintro ⟨f, l, x, y⟩; rfl

private def rightFinalFlattenEquiv (a b c : Λ) :
    Fus.RightFinalNested a b c ≃ Fus.RightTripleIndex a b c where
  toFun x := ⟨x.2.2.1, ⟨⟨x.1, x.2.1, x.2.2.2.1⟩, x.2.2.2.2⟩⟩
  invFun x := ⟨x.2.1.1, ⟨x.2.1.2.1, ⟨x.1, x.2.1.2.2, x.2.2⟩⟩⟩
  left_inv := by rintro ⟨f, l, d, s, z⟩; rfl
  right_inv := by rintro ⟨d, ⟨f, l, s⟩, z⟩; rfl

private noncomputable def rightFirstSynthesis (a b c : Λ) :
    Matrix (Fus.TripleBond a b c) (Fus.RightFirstStage a b c) ℂ :=
  ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
    Fus.fusionSynthesis b c).submatrix (Fus.rightBondAssocEquiv a b c) (Equiv.refl _)

private noncomputable def rightFirstAnalysis (a b c : Λ) :
    Matrix (Fus.RightFirstStage a b c) (Fus.TripleBond a b c) ℂ :=
  ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
    Fus.fusionAnalysis b c).submatrix (Equiv.refl _) (Fus.rightBondAssocEquiv a b c)

private noncomputable def rightSecondSynthesis (a b c : Λ) :
    Matrix (Fus.RightFirstStage a b c) (Fus.RightTripleIndex a b c) ℂ :=
  (Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
      (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionSynthesis a f).submatrix
        (Fus.rightFirstStageEquiv a b c) (Fus.rightFinalFlattenEquiv a b c).symm

private noncomputable def rightSecondAnalysis (a b c : Λ) :
    Matrix (Fus.RightTripleIndex a b c) (Fus.RightFirstStage a b c) ℂ :=
  (Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
      (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionAnalysis a f).submatrix
        (Fus.rightFinalFlattenEquiv a b c).symm (Fus.rightFirstStageEquiv a b c)

private theorem rightSynthesisFull_eq_stages (a b c : Λ) :
    Fus.rightTripleSynthesisFull a b c =
      Fus.rightFirstSynthesis a b c * Fus.rightSecondSynthesis a b c := by
  classical
  funext ⟨⟨xa, xb⟩, xc⟩ ⟨d, ⟨⟨f, l, s⟩, z⟩⟩
  simp [rightTripleSynthesisFull, rightTripleSynthesis, rightFirstSynthesis,
    rightSecondSynthesis, rightBondAssocEquiv, rightFirstStageEquiv,
    rightFinalFlattenEquiv, fusionTensor, Matrix.mul_apply, Fintype.sum_sigma,
    Fintype.sum_prod_type, Matrix.blockDiagonal'_apply, Matrix.one_apply]

private theorem rightAnalysisFull_eq_stages (a b c : Λ) :
    Fus.rightTripleAnalysisFull a b c =
      Fus.rightSecondAnalysis a b c * Fus.rightFirstAnalysis a b c := by
  classical
  funext ⟨d, ⟨⟨f, l, s⟩, z⟩⟩ ⟨⟨xa, xb⟩, xc⟩
  simp [rightTripleAnalysisFull, rightTripleAnalysis, rightFirstAnalysis,
    rightSecondAnalysis, rightBondAssocEquiv, rightFirstStageEquiv,
    rightFinalFlattenEquiv, fusionTensorLeftInverse, Matrix.mul_apply,
    Fintype.sum_sigma, Fintype.sum_prod_type, Matrix.blockDiagonal'_apply,
    Matrix.one_apply]

private theorem rightFirstAnalysis_mul_synthesis (a b c : Λ) :
    Fus.rightFirstAnalysis a b c * Fus.rightFirstSynthesis a b c = 1 := by
  unfold rightFirstSynthesis rightFirstAnalysis
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.rightBondAssocEquiv a b c) _,
    ← Matrix.mul_kronecker_mul, Fus.analysis_mul_synthesis, Matrix.one_mul,
    Matrix.one_kronecker_one]
  rfl

private theorem rightSecondAnalysis_mul_synthesis (a b c : Λ) :
    Fus.rightSecondAnalysis a b c * Fus.rightSecondSynthesis a b c = 1 := by
  unfold rightSecondSynthesis rightSecondAnalysis
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.rightFirstStageEquiv a b c) _,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.mul_kronecker_mul, Fus.analysis_mul_synthesis, Matrix.one_mul,
    Matrix.one_kronecker_one]
  change (Matrix.blockDiagonal' (1 : (f : Λ) → Matrix
    (Fin (Fus.fusionMultiplicity b c f) × ((d : Λ) ×
      (Fin (Fus.fusionMultiplicity a f d) × Fin (Fus.bondDim d)))) _ ℂ)).submatrix
        (Fus.rightFinalFlattenEquiv a b c).symm
        (Fus.rightFinalFlattenEquiv a b c).symm = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

private noncomputable def leftIntermediateLetter (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.LeftFirstStage a b c) (Fus.LeftFirstStage a b c) ℂ :=
  (Matrix.blockDiagonal' fun e =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
      (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ
        (∑ k : Fin p, Fus.tensor e i k ⊗ₖ Fus.tensor c k l)).submatrix
          (Fus.leftFirstStageEquiv a b c) (Fus.leftFirstStageEquiv a b c)

private noncomputable def leftNaturalDirectSumLetter
    (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.LeftFinalNested a b c) (Fus.LeftFinalNested a b c) ℂ :=
  Matrix.blockDiagonal' fun e =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
      (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ
        Matrix.blockDiagonal' (fun d =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity e c d))
            (Fin (Fus.fusionMultiplicity e c d)) ℂ) ⊗ₖ Fus.tensor d i l)

private theorem tripleProductLetter_mul_leftFirstSynthesis
    (a b c : Λ) (i l : Fin p) :
    Fus.tripleProductLetter a b c i l * Fus.leftFirstSynthesis a b c =
      Fus.leftFirstSynthesis a b c * Fus.leftIntermediateLetter a b c i l := by
  classical
  have hIntermediate : Fus.leftIntermediateLetter a b c i l =
      ∑ k : Fin p, (Matrix.blockDiagonal' fun e =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
          (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.tensor e i k) ⊗ₖ
            Fus.tensor c k l := by
    funext ⟨⟨e, μ, z⟩, x⟩ ⟨⟨e', μ', z'⟩, x'⟩
    by_cases he : e = e'
    · subst e'
      by_cases hμ : μ = μ'
      · subst μ'
        simp [leftIntermediateLetter, leftFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply]
      · simp [leftIntermediateLetter, leftFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply, hμ]
    · simp [leftIntermediateLetter, leftFirstStageEquiv,
        Matrix.blockDiagonal'_apply, Matrix.sum_apply, he]
  rw [tripleProductLetter, leftFirstSynthesis, hIntermediate,
    Matrix.sum_mul, Matrix.mul_sum]
  simp_rw [Matrix.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hPair := Fus.pairLetter_mul_synthesis a b i k
  calc
    (∑ j : Fin p,
      ((Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ Fus.tensor c k l) *
        (Fus.fusionSynthesis a b ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ))) =
        (((∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor b j k) *
          Fus.fusionSynthesis a b) ⊗ₖ Fus.tensor c k l) := by
      rw [← Matrix.sum_mul]
      have hTensor :
          (∑ j : Fin p,
            (Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ Fus.tensor c k l) =
            (∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ
              Fus.tensor c k l := by
        funext x y
        simp only [Matrix.sum_apply, kroneckerMap_apply]
        rw [Finset.sum_mul]
      rw [hTensor, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    _ = ((Fus.fusionSynthesis a b * Matrix.blockDiagonal' (fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.tensor e i k)) ⊗ₖ
          Fus.tensor c k l) := by rw [hPair]
    _ = (Fus.fusionSynthesis a b ⊗ₖ
          (1 : Matrix (Fin (Fus.bondDim c)) (Fin (Fus.bondDim c)) ℂ)) *
        ((Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.tensor e i k) ⊗ₖ
          Fus.tensor c k l) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

private theorem leftIntermediateLetter_mul_leftSecondSynthesis
    (a b c : Λ) (i l : Fin p) :
    Fus.leftIntermediateLetter a b c i l * Fus.leftSecondSynthesis a b c =
      Fus.leftSecondSynthesis a b c * Fus.leftTripleDirectSumLetter a b c i l := by
  classical
  have hBlock :
      (Matrix.blockDiagonal' fun e =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
          (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ
            (∑ k : Fin p, Fus.tensor e i k ⊗ₖ Fus.tensor c k l)) *
        (Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionSynthesis e c) =
      (Matrix.blockDiagonal' fun e =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
          (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionSynthesis e c) *
        Fus.leftNaturalDirectSumLetter a b c i l := by
    rw [← Matrix.blockDiagonal'_mul]
    unfold leftNaturalDirectSumLetter
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext e
    rw [← Matrix.mul_kronecker_mul, Fus.pairLetter_mul_synthesis,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hFinal : Fus.leftTripleDirectSumLetter a b c i l =
      (Fus.leftNaturalDirectSumLetter a b c i l).submatrix
        (Fus.leftFinalFlattenEquiv a b c).symm
        (Fus.leftFinalFlattenEquiv a b c).symm := by
    funext ⟨d, ⟨⟨e, μ, ν⟩, z⟩⟩ ⟨d', ⟨⟨e', μ', ν'⟩, z'⟩⟩
    by_cases hd : d = d'
    · subst d'
      by_cases he : e = e'
      · subst e'
        by_cases hμ : μ = μ'
        · subst μ'
          by_cases hν : ν = ν'
          · subst ν'
            simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
              leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply]
          · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
              leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hν]
        · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
            leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hμ]
      · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
          leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, he]
    · by_cases he : e = e'
      · subst e'
        simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
          leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd]
      · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
          leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd, he]
  unfold leftIntermediateLetter leftSecondSynthesis
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.leftFirstStageEquiv a b c) _, hBlock,
    hFinal, Matrix.submatrix_mul_equiv]

private noncomputable def rightIntermediateLetter (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.RightFirstStage a b c) (Fus.RightFirstStage a b c) ℂ :=
  (Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
      (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ
        (∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor f j l)).submatrix
          (Fus.rightFirstStageEquiv a b c) (Fus.rightFirstStageEquiv a b c)

private noncomputable def rightNaturalDirectSumLetter
    (a b c : Λ) (i l : Fin p) :
    Matrix (Fus.RightFinalNested a b c) (Fus.RightFinalNested a b c) ℂ :=
  Matrix.blockDiagonal' fun f =>
    (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
      (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ
        Matrix.blockDiagonal' (fun d =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a f d))
            (Fin (Fus.fusionMultiplicity a f d)) ℂ) ⊗ₖ Fus.tensor d i l)

private theorem rightSecondAnalysis_mul_rightIntermediateLetter
    (a b c : Λ) (i l : Fin p) :
    Fus.rightSecondAnalysis a b c * Fus.rightIntermediateLetter a b c i l =
      Fus.rightTripleDirectSumLetter a b c i l * Fus.rightSecondAnalysis a b c := by
  classical
  have hBlock :
      (Matrix.blockDiagonal' fun f =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
          (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionAnalysis a f) *
        (Matrix.blockDiagonal' fun f =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
            (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ
              (∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor f j l)) =
      Fus.rightNaturalDirectSumLetter a b c i l *
        (Matrix.blockDiagonal' fun f =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
            (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionAnalysis a f) := by
    rw [← Matrix.blockDiagonal'_mul]
    unfold rightNaturalDirectSumLetter
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext f
    rw [← Matrix.mul_kronecker_mul, Fus.analysis_mul_pairLetter,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hFinal : Fus.rightTripleDirectSumLetter a b c i l =
      (Fus.rightNaturalDirectSumLetter a b c i l).submatrix
        (Fus.rightFinalFlattenEquiv a b c).symm
        (Fus.rightFinalFlattenEquiv a b c).symm := by
    funext ⟨d, ⟨⟨f, m, n⟩, z⟩⟩ ⟨d', ⟨⟨f', m', n'⟩, z'⟩⟩
    by_cases hd : d = d'
    · subst d'
      by_cases hf : f = f'
      · subst f'
        by_cases hm : m = m'
        · subst m'
          by_cases hn : n = n'
          · subst n'
            simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
              rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply]
          · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
              rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hn]
        · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
            rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hm]
      · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
          rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hf]
    · by_cases hf : f = f'
      · subst f'
        simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
          rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd]
      · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
          rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd, hf]
  unfold rightSecondAnalysis rightIntermediateLetter
  rw [Matrix.submatrix_mul_equiv _ _ _ (Fus.rightFirstStageEquiv a b c) _, hBlock,
    hFinal, Matrix.submatrix_mul_equiv]

private theorem rightFirstAnalysis_mul_tripleProductLetter
    (a b c : Λ) (i l : Fin p) :
    Fus.rightFirstAnalysis a b c * Fus.tripleProductLetter a b c i l =
      Fus.rightIntermediateLetter a b c i l * Fus.rightFirstAnalysis a b c := by
  classical
  let P : Matrix
      (Fin (Fus.bondDim a) × (Fin (Fus.bondDim b) × Fin (Fus.bondDim c)))
      (Fin (Fus.bondDim a) × (Fin (Fus.bondDim b) × Fin (Fus.bondDim c))) ℂ :=
    ∑ j : Fin p, Fus.tensor a i j ⊗ₖ
      (∑ k : Fin p, Fus.tensor b j k ⊗ₖ Fus.tensor c k l)
  let E : Matrix (Fus.RightFirstStage a b c) (Fus.RightFirstStage a b c) ℂ :=
    ∑ j : Fin p, Fus.tensor a i j ⊗ₖ Matrix.blockDiagonal' (fun f =>
      (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
        (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.tensor f j l)
  have hP : Fus.tripleProductLetter a b c i l =
      P.submatrix (Fus.rightBondAssocEquiv a b c)
        (Fus.rightBondAssocEquiv a b c) := by
    funext ⟨⟨xa, xb⟩, xc⟩ ⟨⟨ya, yb⟩, yc⟩
    simp [P, tripleProductLetter, rightBondAssocEquiv, Matrix.sum_apply,
      Finset.mul_sum]
    ring_nf
  have hE : Fus.rightIntermediateLetter a b c i l = E := by
    funext ⟨x, ⟨f, m, z⟩⟩ ⟨x', ⟨f', m', z'⟩⟩
    by_cases hf : f = f'
    · subst f'
      by_cases hm : m = m'
      · subst m'
        simp [E, rightIntermediateLetter, rightFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply]
      · simp [E, rightIntermediateLetter, rightFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply, hm]
    · simp [E, rightIntermediateLetter, rightFirstStageEquiv,
        Matrix.blockDiagonal'_apply, Matrix.sum_apply, hf]
  have hCore :
      ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
          Fus.fusionAnalysis b c) * P =
        E * ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
          Fus.fusionAnalysis b c) := by
    dsimp only [P, E]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Fus.analysis_mul_pairLetter, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  unfold rightFirstAnalysis
  rw [hP, Matrix.submatrix_mul_equiv _ _ _ (Fus.rightBondAssocEquiv a b c) _,
    hCore, ← hE]
  simpa using Matrix.submatrix_mul
    (Fus.rightIntermediateLetter a b c i l)
    ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
      Fus.fusionAnalysis b c)
    (Equiv.refl _) (Equiv.refl _) (Fus.rightBondAssocEquiv a b c)
    (Equiv.refl _).bijective

/-- The left-associated triple synthesis satisfies the zipper identity.

Source: arXiv:1511.08090, equations `zippercondition2` and the first identity
at lines 242--245. -/
theorem tripleProductLetter_mul_leftTripleSynthesisFull
    (a b c : Λ) (i l : Fin p) :
    Fus.tripleProductLetter a b c i l * Fus.leftTripleSynthesisFull a b c =
      Fus.leftTripleSynthesisFull a b c * Fus.leftTripleDirectSumLetter a b c i l := by
  rw [Fus.leftSynthesisFull_eq_stages, ← Matrix.mul_assoc,
    Fus.tripleProductLetter_mul_leftFirstSynthesis, Matrix.mul_assoc,
    Fus.leftIntermediateLetter_mul_leftSecondSynthesis, Matrix.mul_assoc]

/-- The right-associated triple analysis satisfies the reverse zipper identity.

Source: arXiv:1511.08090, equations `zippercondition2` and the second identity
at lines 242--246. -/
theorem rightTripleAnalysisFull_mul_tripleProductLetter
    (a b c : Λ) (i l : Fin p) :
    Fus.rightTripleAnalysisFull a b c * Fus.tripleProductLetter a b c i l =
      Fus.rightTripleDirectSumLetter a b c i l *
        Fus.rightTripleAnalysisFull a b c := by
  rw [Fus.rightAnalysisFull_eq_stages, Matrix.mul_assoc,
    Fus.rightFirstAnalysis_mul_tripleProductLetter, ← Matrix.mul_assoc,
    Fus.rightSecondAnalysis_mul_rightIntermediateLetter, Matrix.mul_assoc]

/-- The left-associated triple analysis followed by its synthesis is the
identity on the full left fusion-coordinate space.

Source: arXiv:1511.08090, the biorthogonality relation at line 161, applied
twice. -/
theorem leftTripleAnalysisFull_mul_synthesis (a b c : Λ) :
    Fus.leftTripleAnalysisFull a b c * Fus.leftTripleSynthesisFull a b c = 1 := by
  rw [Fus.leftSynthesisFull_eq_stages, Fus.leftAnalysisFull_eq_stages,
    Matrix.mul_assoc, ← Matrix.mul_assoc (Fus.leftFirstAnalysis a b c),
    Fus.leftFirstAnalysis_mul_synthesis, Matrix.one_mul,
    Fus.leftSecondAnalysis_mul_synthesis]

/-- The right-associated triple analysis followed by its synthesis is the
identity on the full right fusion-coordinate space.

Source: arXiv:1511.08090, the biorthogonality relation at line 161, applied
twice. -/
theorem rightTripleAnalysisFull_mul_synthesis (a b c : Λ) :
    Fus.rightTripleAnalysisFull a b c * Fus.rightTripleSynthesisFull a b c = 1 := by
  rw [Fus.rightSynthesisFull_eq_stages, Fus.rightAnalysisFull_eq_stages,
    Matrix.mul_assoc, ← Matrix.mul_assoc (Fus.rightFirstAnalysis a b c),
    Fus.rightFirstAnalysis_mul_synthesis, Matrix.one_mul,
    Fus.rightSecondAnalysis_mul_synthesis]


/-- The coefficient selecting the diagonal matrix units of one final block.

Source: arXiv:1511.08090, the simultaneous inverse at lines 269--277. -/
private noncomputable def supportFinalBlockSelector
    (d : Λ) (ik : Fin p × Fin p) : ℂ :=
  ∑ x : Fin (Fus.bondDim d), Fus.blockLeftInverse ⟨d, x, x⟩ ik

private theorem supportFinalBlockSelector_apply (d e : Λ)
    (x y : Fin (Fus.bondDim e)) :
    (∑ i : Fin p, ∑ l : Fin p,
      Fus.supportFinalBlockSelector d (i, l) * Fus.tensor e i l x y) =
      if h : d = e then if _ : h ▸ x = y then 1 else 0 else 0 := by
  classical
  simp only [supportFinalBlockSelector, Finset.sum_mul]
  calc
    (∑ i : Fin p, ∑ l : Fin p, ∑ z : Fin (Fus.bondDim d),
        Fus.blockLeftInverse ⟨d, z, z⟩ (i, l) * Fus.tensor e i l x y) =
        ∑ z : Fin (Fus.bondDim d), ∑ i : Fin p, ∑ l : Fin p,
          Fus.blockLeftInverse ⟨d, z, z⟩ (i, l) * Fus.tensor e i l x y := by
      calc
        _ = ∑ i : Fin p, ∑ z : Fin (Fus.bondDim d), ∑ l : Fin p,
            Fus.blockLeftInverse ⟨d, z, z⟩ (i, l) * Fus.tensor e i l x y := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = if h : d = e then if _ : h ▸ x = y then 1 else 0 else 0 := by
      by_cases h : d = e
      · subst e
        simp_rw [Fus.blockLeftInverse_apply d d]
        simp
      · simp_rw [Fus.blockLeftInverse_apply d e]
        simp [h]

private theorem supportFinalBlockSelector_sum (d e : Λ) :
    (∑ i : Fin p, ∑ l : Fin p,
      Fus.supportFinalBlockSelector d (i, l) •
        (Fus.tensor e i l : Matrix (Fin (Fus.bondDim e))
          (Fin (Fus.bondDim e)) ℂ)) =
      if d = e then 1 else 0 := by
  classical
  funext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fus.supportFinalBlockSelector_apply d e x y]
  by_cases h : d = e
  · subst e
    simp [Matrix.one_apply]
  · simp [h]

/-- The total coefficient obtained by summing diagonal matrix-unit selectors
for every final label.

Source: arXiv:1511.08090, the simultaneous inverse at lines 269--277. -/
private noncomputable def totalBlockSelector (ik : Fin p × Fin p) : ℂ :=
  ∑ d : Λ, Fus.supportFinalBlockSelector d ik

/-- Contracting the total selector with any labelled block letter gives the
identity matrix.

Source: arXiv:1511.08090, the simultaneous inverse at lines 269--277. -/
private theorem totalBlockSelector_sum (e : Λ) :
    (∑ i : Fin p, ∑ l : Fin p,
      Fus.totalBlockSelector (i, l) •
        (Fus.tensor e i l : Matrix (Fin (Fus.bondDim e))
          (Fin (Fus.bondDim e)) ℂ)) = 1 := by
  classical
  simp only [totalBlockSelector, Finset.sum_smul]
  calc
    (∑ i : Fin p, ∑ l : Fin p, ∑ d : Λ,
        Fus.supportFinalBlockSelector d (i, l) • Fus.tensor e i l) =
        ∑ i : Fin p, ∑ d : Λ, ∑ l : Fin p,
          Fus.supportFinalBlockSelector d (i, l) • Fus.tensor e i l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ d : Λ, ∑ i : Fin p, ∑ l : Fin p,
          Fus.supportFinalBlockSelector d (i, l) • Fus.tensor e i l :=
      Finset.sum_comm
    _ = ∑ d : Λ, if d = e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Fus.supportFinalBlockSelector_sum d e
    _ = 1 := by simp

/-- Contracting final-block letters with the total selector gives the identity
in the left-associated coordinate space. -/
private theorem totalBlockSelector_leftDirectSum (a b c : Λ) :
    (∑ i : Fin p, ∑ l : Fin p,
      Fus.totalBlockSelector (i, l) • Fus.leftTripleDirectSumLetter a b c i l) =
      1 := by
  classical
  funext ⟨d, m, x⟩ ⟨e, n, y⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  by_cases hde : d = e
  · subst e
    by_cases hmn : m = n
    · subst n
      simpa [leftTripleDirectSumLetter, Matrix.blockDiagonal'_apply_eq,
        Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using congrArg
          (fun M => M x y) (Fus.totalBlockSelector_sum d)
    · simp [leftTripleDirectSumLetter, Matrix.blockDiagonal'_apply_eq, hmn]
  · simp [leftTripleDirectSumLetter, Matrix.blockDiagonal'_apply_ne, hde]

/-- Contracting final-block letters with the total selector gives the identity
in the right-associated coordinate space. -/
private theorem totalBlockSelector_rightDirectSum (a b c : Λ) :
    (∑ i : Fin p, ∑ l : Fin p,
      Fus.totalBlockSelector (i, l) • Fus.rightTripleDirectSumLetter a b c i l) =
      1 := by
  classical
  funext ⟨d, m, x⟩ ⟨e, n, y⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  by_cases hde : d = e
  · subst e
    by_cases hmn : m = n
    · subst n
      simpa [rightTripleDirectSumLetter, Matrix.blockDiagonal'_apply_eq,
        Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using congrArg
          (fun M => M x y) (Fus.totalBlockSelector_sum d)
    · simp [rightTripleDirectSumLetter, Matrix.blockDiagonal'_apply_eq, hmn]
  · simp [rightTripleDirectSumLetter, Matrix.blockDiagonal'_apply_ne, hde]

/-- Every triple-product letter is reconstructed through the left-associated
fusion support.

Source: arXiv:1511.08090, equation `inversegaugeone` at lines 184--186,
applied to the two fusions in lines 238--243. -/
theorem tripleProductLetter_eq_left_reconstruction
    (a b c : Λ) (i l : Fin p) :
    Fus.tripleProductLetter a b c i l =
      Fus.leftTripleSynthesisFull a b c *
        Fus.leftTripleDirectSumLetter a b c i l *
          Fus.leftTripleAnalysisFull a b c := by
  classical
  have hFirst : Fus.tripleProductLetter a b c i l =
      Fus.leftFirstSynthesis a b c * Fus.leftIntermediateLetter a b c i l *
        Fus.leftFirstAnalysis a b c := by
    have hIntermediate : Fus.leftIntermediateLetter a b c i l =
        ∑ k : Fin p, (Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.tensor e i k) ⊗ₖ
              Fus.tensor c k l := by
      funext ⟨⟨e, μ, z⟩, x⟩ ⟨⟨e', μ', z'⟩, x'⟩
      by_cases he : e = e'
      · subst e'
        by_cases hμ : μ = μ'
        · subst μ'
          simp [leftIntermediateLetter, leftFirstStageEquiv,
            Matrix.blockDiagonal'_apply, Matrix.sum_apply]
        · simp [leftIntermediateLetter, leftFirstStageEquiv,
            Matrix.blockDiagonal'_apply, Matrix.sum_apply, hμ]
      · simp [leftIntermediateLetter, leftFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply, he]
    rw [tripleProductLetter, leftFirstSynthesis, leftFirstAnalysis, hIntermediate,
      Matrix.mul_sum]
    simp_rw [Matrix.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hTensor :
        (∑ j : Fin p,
          (Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ Fus.tensor c k l) =
          (∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor b j k) ⊗ₖ
            Fus.tensor c k l := by
      funext x y
      simp only [Matrix.sum_apply, kroneckerMap_apply]
      rw [Finset.sum_mul]
    rw [hTensor, Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis a b i k]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have hSecond : Fus.leftIntermediateLetter a b c i l =
      Fus.leftSecondSynthesis a b c * Fus.leftTripleDirectSumLetter a b c i l *
        Fus.leftSecondAnalysis a b c := by
    have hBlock :
        (Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ
              (∑ k : Fin p, Fus.tensor e i k ⊗ₖ Fus.tensor c k l)) =
        (Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionSynthesis e c) *
        Fus.leftNaturalDirectSumLetter a b c i l *
        (Matrix.blockDiagonal' fun e =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity a b e))
            (Fin (Fus.fusionMultiplicity a b e)) ℂ) ⊗ₖ Fus.fusionAnalysis e c) := by
      unfold leftNaturalDirectSumLetter
      rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
      congr 1
      funext e
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis e c i l,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hFinal : Fus.leftTripleDirectSumLetter a b c i l =
        (Fus.leftNaturalDirectSumLetter a b c i l).submatrix
          (Fus.leftFinalFlattenEquiv a b c).symm
          (Fus.leftFinalFlattenEquiv a b c).symm := by
      funext ⟨d, ⟨⟨e, μ, ν⟩, z⟩⟩ ⟨d', ⟨⟨e', μ', ν'⟩, z'⟩⟩
      by_cases hd : d = d'
      · subst d'
        by_cases he : e = e'
        · subst e'
          by_cases hμ : μ = μ'
          · subst μ'
            by_cases hν : ν = ν'
            · subst ν'
              simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
                leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply]
            · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
                leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hν]
          · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
              leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hμ]
        · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
            leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, he]
      · by_cases he : e = e'
        · subst e'
          simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
            leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd]
        · simp [leftTripleDirectSumLetter, leftNaturalDirectSumLetter,
            leftFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd, he]
    unfold leftIntermediateLetter leftSecondSynthesis leftSecondAnalysis
    rw [hFinal, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hBlock]
  rw [Fus.leftSynthesisFull_eq_stages, Fus.leftAnalysisFull_eq_stages,
    hFirst, hSecond]
  simp only [Matrix.mul_assoc]

/-- Every triple-product letter is reconstructed through the right-associated
fusion support.

Source: arXiv:1511.08090, equation `inversegaugeone` at lines 184--186,
applied to the two fusions in lines 244--247. -/
theorem tripleProductLetter_eq_right_reconstruction
    (a b c : Λ) (i l : Fin p) :
    Fus.tripleProductLetter a b c i l =
      Fus.rightTripleSynthesisFull a b c *
        Fus.rightTripleDirectSumLetter a b c i l *
          Fus.rightTripleAnalysisFull a b c := by
  classical
  have hFirst : Fus.tripleProductLetter a b c i l =
      Fus.rightFirstSynthesis a b c * Fus.rightIntermediateLetter a b c i l *
        Fus.rightFirstAnalysis a b c := by
    let P : Matrix
        (Fin (Fus.bondDim a) × (Fin (Fus.bondDim b) × Fin (Fus.bondDim c)))
        (Fin (Fus.bondDim a) × (Fin (Fus.bondDim b) × Fin (Fus.bondDim c))) ℂ :=
      ∑ j : Fin p, Fus.tensor a i j ⊗ₖ
        (∑ k : Fin p, Fus.tensor b j k ⊗ₖ Fus.tensor c k l)
    let E : Matrix (Fus.RightFirstStage a b c) (Fus.RightFirstStage a b c) ℂ :=
      ∑ j : Fin p, Fus.tensor a i j ⊗ₖ Matrix.blockDiagonal' (fun f =>
        (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
          (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.tensor f j l)
    have hP : Fus.tripleProductLetter a b c i l =
        P.submatrix (Fus.rightBondAssocEquiv a b c)
          (Fus.rightBondAssocEquiv a b c) := by
      funext ⟨⟨xa, xb⟩, xc⟩ ⟨⟨ya, yb⟩, yc⟩
      simp [P, tripleProductLetter, rightBondAssocEquiv, Matrix.sum_apply,
        Finset.mul_sum]
      ring_nf
    have hE : Fus.rightIntermediateLetter a b c i l = E := by
      funext ⟨x, ⟨f, m, z⟩⟩ ⟨x', ⟨f', m', z'⟩⟩
      by_cases hf : f = f'
      · subst f'
        by_cases hm : m = m'
        · subst m'
          simp [E, rightIntermediateLetter, rightFirstStageEquiv,
            Matrix.blockDiagonal'_apply, Matrix.sum_apply]
        · simp [E, rightIntermediateLetter, rightFirstStageEquiv,
            Matrix.blockDiagonal'_apply, Matrix.sum_apply, hm]
      · simp [E, rightIntermediateLetter, rightFirstStageEquiv,
          Matrix.blockDiagonal'_apply, Matrix.sum_apply, hf]
    have hCore : P =
        ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
          Fus.fusionSynthesis b c) * E *
        ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
          Fus.fusionAnalysis b c) := by
      dsimp only [P, E]
      rw [Matrix.mul_sum]
      simp_rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis b c j l,
        ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    unfold rightFirstSynthesis rightFirstAnalysis
    rw [hP, hE, hCore]
    symm
    change
      ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
            Fus.fusionSynthesis b c).submatrix (Fus.rightBondAssocEquiv a b c)
              (Equiv.refl _) *
          E.submatrix (Equiv.refl _) (Equiv.refl _) *
        ((1 : Matrix (Fin (Fus.bondDim a)) (Fin (Fus.bondDim a)) ℂ) ⊗ₖ
            Fus.fusionAnalysis b c).submatrix (Equiv.refl _)
              (Fus.rightBondAssocEquiv a b c) = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hSecond : Fus.rightIntermediateLetter a b c i l =
      Fus.rightSecondSynthesis a b c * Fus.rightTripleDirectSumLetter a b c i l *
        Fus.rightSecondAnalysis a b c := by
    have hBlock :
        (Matrix.blockDiagonal' fun f =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
            (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ
              (∑ j : Fin p, Fus.tensor a i j ⊗ₖ Fus.tensor f j l)) =
        (Matrix.blockDiagonal' fun f =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
            (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionSynthesis a f) *
        Fus.rightNaturalDirectSumLetter a b c i l *
        (Matrix.blockDiagonal' fun f =>
          (1 : Matrix (Fin (Fus.fusionMultiplicity b c f))
            (Fin (Fus.fusionMultiplicity b c f)) ℂ) ⊗ₖ Fus.fusionAnalysis a f) := by
      unfold rightNaturalDirectSumLetter
      rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
      congr 1
      funext f
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
        Fus.pairLetter_eq_synthesis_mul_directSum_mul_analysis a f i l,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hFinal : Fus.rightTripleDirectSumLetter a b c i l =
        (Fus.rightNaturalDirectSumLetter a b c i l).submatrix
          (Fus.rightFinalFlattenEquiv a b c).symm
          (Fus.rightFinalFlattenEquiv a b c).symm := by
      funext ⟨d, ⟨⟨f, m, n⟩, z⟩⟩ ⟨d', ⟨⟨f', m', n'⟩, z'⟩⟩
      by_cases hd : d = d'
      · subst d'
        by_cases hf : f = f'
        · subst f'
          by_cases hm : m = m'
          · subst m'
            by_cases hn : n = n'
            · subst n'
              simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
                rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply]
            · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
                rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hn]
          · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
              rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hm]
        · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
            rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hf]
      · by_cases hf : f = f'
        · subst f'
          simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
            rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd]
        · simp [rightTripleDirectSumLetter, rightNaturalDirectSumLetter,
            rightFinalFlattenEquiv, Matrix.blockDiagonal'_apply, hd, hf]
    unfold rightIntermediateLetter rightSecondSynthesis rightSecondAnalysis
    rw [hFinal, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hBlock]
  rw [Fus.rightSynthesisFull_eq_stages, Fus.rightAnalysisFull_eq_stages,
    hFirst, hSecond]
  simp only [Matrix.mul_assoc]

/-- The left- and right-associated triple-fusion maps have the same support
projector in the ambient triple-bond space.

The equality is derived by contracting the two triple-letter reconstructions
with the simultaneous inverse of the final block letters.

Source: arXiv:1511.08090, equation `inversegaugeone` at lines 184--186, the
associative decompositions at lines 238--247, and the simultaneous inverse at
lines 269--277. -/
theorem leftTripleSupport_eq_rightTripleSupport (a b c : Λ) :
    Fus.leftTripleSynthesisFull a b c * Fus.leftTripleAnalysisFull a b c =
      Fus.rightTripleSynthesisFull a b c * Fus.rightTripleAnalysisFull a b c := by
  classical
  let contracted := ∑ i : Fin p, ∑ l : Fin p,
    Fus.totalBlockSelector (i, l) • Fus.tripleProductLetter a b c i l
  have hLeft : contracted =
      Fus.leftTripleSynthesisFull a b c * Fus.leftTripleAnalysisFull a b c := by
    dsimp only [contracted]
    simp_rw [Fus.tripleProductLetter_eq_left_reconstruction]
    calc
      _ = Fus.leftTripleSynthesisFull a b c *
          (∑ i : Fin p, ∑ l : Fin p,
            Fus.totalBlockSelector (i, l) •
              Fus.leftTripleDirectSumLetter a b c i l) *
            Fus.leftTripleAnalysisFull a b c := by
        symm
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
        rw [Fus.totalBlockSelector_leftDirectSum, Matrix.mul_one]
  have hRight : contracted =
      Fus.rightTripleSynthesisFull a b c * Fus.rightTripleAnalysisFull a b c := by
    dsimp only [contracted]
    simp_rw [Fus.tripleProductLetter_eq_right_reconstruction]
    calc
      _ = Fus.rightTripleSynthesisFull a b c *
          (∑ i : Fin p, ∑ l : Fin p,
            Fus.totalBlockSelector (i, l) •
              Fus.rightTripleDirectSumLetter a b c i l) *
            Fus.rightTripleAnalysisFull a b c := by
        symm
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
        rw [Fus.totalBlockSelector_rightDirectSum, Matrix.mul_one]
  exact hLeft.symm.trans hRight

end CompleteZipperFusionFamily

end MPOTensor
