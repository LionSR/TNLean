/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FiniteSourceGate
import TNLean.PEPS.Approximation.SourcePreparationCoordinates
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fintype.Pi

/-!
# Density expansion of a gate with finite pair sources

Expanding the ket and bra source vectors separately expresses the output density
as a finite sum of terms formed from their coordinate coefficients and the
operators obtained by preparing endpoint basis vectors. The algebraic identity
holds for arbitrary input matrices and includes an empty list of source slots.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the density-source expansion following
`eq:compression-source-gate`, lines 279–317.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped ComplexConjugate Matrix TensorProduct

namespace TNLean.PEPS.PairEffect

/-- The matrix of an actual branch after preparing its pair sources, in prescribed
orthonormal bases of the input and output memories.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 279–317. -/
def Word.preparedMatrix {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    Matrix m n ℂ := by
  classical
  exact LinearMap.toMatrix bIn.toBasis bOut.toBasis
    (v.eval.comp (SourceInventory.prepareSlots R U V η ℓ).eval).toLinearMap

/-- Finite sums in the actual source slots give the corresponding finite sum of
prepared branch matrices, with one coefficient from each slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.preparedMatrix_sum_smul {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A : Fin R.length → Type} [∀ i, Fintype (A i)]
    (c : ∀ i, A i → ℂ) (η : ∀ i, A i → U i ⊗[ℂ] V i)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    v.preparedMatrix R U V (fun i ↦ ∑ a, c i a • η i a) ℓ bIn bOut =
      ∑ a : ∀ i, A i, (∏ i, c i (a i)) •
        v.preparedMatrix R U V (fun i ↦ η i (a i)) ℓ bIn bOut := by
  classical
  simp only [Word.preparedMatrix, SourceInventory.eval_prepareSlots_sum_smul,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul]

/-- The matrix of an actual prepared branch is the sum of its endpoint-basis
preparations, weighted by the product of the source coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.preparedMatrix_eq_sum_basis {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    v.preparedMatrix R U V η ℓ bIn bOut =
      ∑ a : ∀ i, A i × B i,
        (∏ i, ((bU i).tensorProduct (bV i)).repr (η i) (a i)) •
          v.preparedMatrix R U V (fun i ↦ bU i (a i).1 ⊗ₜ[ℂ] bV i (a i).2)
            ℓ bIn bOut := by
  classical
  simp only [Word.preparedMatrix,
    SourceInventory.eval_prepareSlots_eq_sum_basis R U V bU bV η ℓ,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul]

/-- The density coefficient obtained by preparing specified endpoint vectors in
the actual ket and bra branches. No spanning or orthonormality condition on these
families, or positivity assumption on the input matrix, is needed for this definition.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–317. -/
def Word.preparedDensityCoefficient {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B A' B' : Fin R.length → Type}
    (uU : ∀ i, A i → U i) (uV : ∀ i, B i → V i)
    (uU' : ∀ i, A' i → U i) (uV' : ∀ i, B' i → V i)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) (a : ∀ i, A i × B i) (b : ∀ i, A' i × B' i) : Matrix m m ℂ :=
  v.preparedMatrix R U V (fun i ↦ uU i (a i).1 ⊗ₜ[ℂ] uV i (a i).2) ℓ bIn bOut * ρ *
    (v'.preparedMatrix R U V (fun i ↦ uU' i (b i).1 ⊗ₜ[ℂ] uV' i (b i).2)
      ℓ bIn bOut)ᴴ

/-- A matrix expansion on each side gives the corresponding ket–bra sum.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–317. -/
private theorem sum_density_expansion {α β m n p : Type}
    [Fintype α] [Fintype β] [Fintype n]
    (c : α → ℂ) (d : β → ℂ) (K : α → Matrix m n ℂ)
    (K' : β → Matrix p n ℂ) (ρ : Matrix n n ℂ) :
    (∑ a, c a • K a) * ρ * (∑ b, d b • K' b)ᴴ =
      ∑ a, ∑ b, (c a * conj (d b)) • (K a * ρ * (K' b)ᴴ) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul,
    Complex.star_def]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Expanding both source vectors gives the ket–bra coefficient at each slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–317. -/
private theorem finite_source_density_expansion
    {I m n p : Type} [Fintype I] [DecidableEq I] [Fintype n]
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (η : ∀ i, A i → ℂ) (ζ : ∀ i, B i → ℂ)
    (K : (∀ i, A i) → Matrix m n ℂ) (K' : (∀ i, B i) → Matrix p n ℂ)
    (ρ : Matrix n n ℂ) :
    (∑ a, (∏ i, η i (a i)) • K a) * ρ *
        (∑ b, (∏ i, ζ i (b i)) • K' b)ᴴ =
      ∑ a, ∑ b, (∏ i, η i (a i) * conj (ζ i (b i))) • (K a * ρ * (K' b)ᴴ) := by
  simpa only [map_prod, Finset.prod_mul_distrib] using
    sum_density_expansion (fun a ↦ ∏ i, η i (a i)) (fun b ↦ ∏ i, ζ i (b i)) K K' ρ

/-- Finite endpoint expansions in the actual ket and bra sources give the density
coefficients. The endpoint families may span proper subspaces of the private spaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.preparedMatrix_density_sum_smul {P m n : Type}
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
    v.preparedMatrix R U V
        (fun i ↦ ∑ a, c i a • (uU i a.1 ⊗ₜ[ℂ] uV i a.2)) ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V
          (fun i ↦ ∑ b, d i b • (uU' i b.1 ⊗ₜ[ℂ] uV' i b.2)) ℓ bIn bOut)ᴴ =
      ∑ a : ∀ i, A i × B i, ∑ b : ∀ i, A' i × B' i,
        (∏ i, c i (a i) * conj (d i (b i))) •
          v.preparedDensityCoefficient R U V uU uV uU' uV' ℓ v' bIn bOut ρ a b := by
  rw [v.preparedMatrix_sum_smul R U V c _ ℓ bIn bOut,
    v'.preparedMatrix_sum_smul R U V d _ ℓ bIn bOut]
  exact finite_source_density_expansion _ _ _ _ ρ

/-- Expanding the actual ket and bra source preparations gives their density
coefficients. The two branches may use different endpoint coordinate bases.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem Word.preparedMatrix_density_eq_sum_basis {P m n : Type}
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
    v.preparedMatrix R U V η ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V ζ ℓ bIn bOut)ᴴ =
      ∑ a : ∀ i, A i × B i, ∑ b : ∀ i, A' i × B' i,
        (∏ i, ((bU i).tensorProduct (bV i)).repr (η i) (a i) *
          conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) (b i))) •
            v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
              (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ a b := by
  rw [v.preparedMatrix_eq_sum_basis R U V bU bV η ℓ bIn bOut,
    v'.preparedMatrix_eq_sum_basis R U V bU' bV' ζ ℓ bIn bOut]
  exact finite_source_density_expansion _ _ _ _ ρ

/-- The density of the weighted gate is the sum over both branches and their
endpoint coordinate assignments. Every original coefficient is retained, with
complex conjugation on the bra branch; the endpoint bases may depend on the branch.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 279–355. -/
theorem Word.preparedMatrix_gate_density_eq_sum_basis {P m n ι : Type}
    [Fintype m] [Fintype n] [Fintype ι]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : ι → Fin R.length → Type}
    [∀ ξ i, Fintype (A ξ i)] [∀ ξ i, Fintype (B ξ i)]
    (bU : ∀ ξ i, OrthonormalBasis (A ξ i) ℂ (U i))
    (bV : ∀ ξ i, OrthonormalBasis (B ξ i) ℂ (V i))
    (c : ι → ℂ) (η : ι → ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) {ℓ' : Layout P}
    (v : ι → Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) :
    (∑ ξ, c ξ • (v ξ).preparedMatrix R U V (η ξ) ℓ bIn bOut) * ρ *
        (∑ ξ, c ξ • (v ξ).preparedMatrix R U V (η ξ) ℓ bIn bOut)ᴴ =
      ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
        ∑ a : ∀ i, A ξ i × B ξ i, ∑ b : ∀ i, A ζ i × B ζ i,
          (∏ i, ((bU ξ i).tensorProduct (bV ξ i)).repr (η ξ i) (a i) *
            conj (((bU ζ i).tensorProduct (bV ζ i)).repr (η ζ i) (b i))) •
              (v ξ).preparedDensityCoefficient R U V
                (fun i ↦ bU ξ i) (fun i ↦ bV ξ i)
                (fun i ↦ bU ζ i) (fun i ↦ bV ζ i) ℓ (v ζ) bIn bOut ρ a b := by
  rw [sum_density_expansion]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [(v ξ).preparedMatrix_density_eq_sum_basis R U V
    (bU ξ) (bV ξ) (bU ζ) (bV ζ) (η ξ) (η ζ) ℓ (v ζ) bIn bOut ρ]

end TNLean.PEPS.PairEffect
