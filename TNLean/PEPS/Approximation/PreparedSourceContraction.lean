/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGateDensity
import QICLean.Analysis.SourceContraction

/-!
# Density contractions of actual prepared sources

The coefficient array is obtained from the actual remaining words by preparing
endpoint vectors. The resulting finite source contraction is exactly the mixed
ket–bra density operator. The endpoint families may have different dimensions
on the two sides, and the input matrix is arbitrary.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped ComplexConjugate Matrix TensorProduct
namespace TNLean.PEPS.PairEffect

/-- Pair the ket and bra coordinate assignments at each fixed source position.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–317. -/
private theorem sourceContraction_vecMulVec {I m n : Type} [Fintype I] [DecidableEq I]
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (c : ∀ i, A i → ℂ) (d : ∀ i, B i → ℂ)
    (coeff : (∀ i, A i) → (∀ i, B i) → Matrix m n ℂ) :
    Matrix.sourceContraction (fun x ↦ coeff (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ Matrix.vecMulVec (c i) (fun b ↦ conj (d i b))) =
      ∑ a, ∑ b, (∏ i, c i (a i) * conj (d i (b i))) • coeff a b := by
  classical
  rw [Matrix.sourceContraction_apply]
  let F : ((∀ i, A i) × (∀ i, B i)) → Matrix m n ℂ := fun ab ↦
    (∏ i, c i (ab.1 i) * conj (d i (ab.2 i))) • coeff ab.1 ab.2
  calc
    _ = ∑ ab, F ab :=
      Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B) _ F (fun _ ↦ rfl)
    _ = _ := Fintype.sum_prod_type F

/-- Finite endpoint expansions in the actual ket and bra sources are evaluated by
source contraction with their rank-one coordinate matrices. No spanning,
normalization, allowedness, or positivity hypothesis is needed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.sourceContraction_preparedDensityCoefficient {P m n : Type}
    [Fintype m] [Fintype n] (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B A' B' : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (uU : ∀ i, A i → U i) (uV : ∀ i, B i → V i)
    (uU' : ∀ i, A' i → U i) (uV' : ∀ i, B' i → V i)
    (c : ∀ i, A i × B i → ℂ) (d : ∀ i, A' i × B' i → ℂ)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) :
    Matrix.sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R U V uU uV uU' uV' ℓ v' bIn bOut ρ
          (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ Matrix.vecMulVec (c i) (fun b ↦ conj (d i b))) =
      v.preparedMatrix R U V
        (fun i ↦ ∑ a, c i a • (uU i a.1 ⊗ₜ[ℂ] uV i a.2)) ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V
          (fun i ↦ ∑ b, d i b • (uU' i b.1 ⊗ₜ[ℂ] uV' i b.2)) ℓ bIn bOut)ᴴ := by
  rw [sourceContraction_vecMulVec]
  exact (v.preparedMatrix_density_sum_smul R U V uU uV uU' uV' c d ℓ v'
    bIn bOut ρ).symm

/-- Actual source vectors in finite endpoint bases give the mixed prepared density
as a contraction of their rank-one coordinate matrices. Ket and bra bases may
be chosen independently, and the input matrix is arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.sourceContraction_preparedDensityCoefficient_basis {P m n : Type}
    [Fintype m] [Fintype n] (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B A' B' : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V i))
    (η ζ : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) :
    Matrix.sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
          (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ
          (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (η i))
          (fun b ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) b))) =
      v.preparedMatrix R U V η ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V ζ ℓ bIn bOut)ᴴ := by
  rw [sourceContraction_vecMulVec]
  exact (v.preparedMatrix_density_eq_sum_basis R U V bU bV bU' bV' η ζ ℓ v'
    bIn bOut ρ).symm

end TNLean.PEPS.PairEffect
