/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceContraction
import TNLean.Algebra.MultilinearSelectedSum

/-!
# Selected coordinates of prepared source contractions

The sources outside a fixed selected set remain their exact vectors. Expanding
only the selected endpoint coordinates gives the same density operator as the
full source contraction with arbitrary matrices at the selected positions.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 338–383.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped ComplexConjugate TensorProduct Matrix
namespace TNLean.PEPS.PairEffect

/-- Expand only the selected matrix arguments of a multilinear map in matrix units. -/
private theorem selected_matrix_expansion {I : Type} [DecidableEq I]
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    {M : Type} [AddCommMonoid M] [Module ℂ M]
    (F : MultilinearMap ℂ (fun i ↦ Matrix (A i) (B i) ℂ) M)
    (S : Finset I) (E X : ∀ i, Matrix (A i) (B i) ℂ) :
    F (S.piecewise E X) =
      ∑ z : ∀ i : S, A i × B i,
        (∏ i : S, E i (z i).1 (z i).2) •
          F (fun i ↦ if h : i ∈ S then Matrix.single (z ⟨i, h⟩).1 (z ⟨i, h⟩).2 1
            else X i) := by
  classical
  have hE (i : I) :
      (∑ z : A i × B i, E i z.1 z.2 • Matrix.single z.1 z.2 1) = E i := by
    rw [Fintype.sum_prod_type]
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      (Matrix.matrix_eq_sum_single (E i)).symm
  simpa only [hE] using F.map_piecewise_sum_smul S
    (fun (i : I) (z : A i × B i) ↦ E i z.1 z.2)
    (fun i (z : A i × B i) ↦ Matrix.single z.1 z.2 1) X

/-- A pair of endpoint basis vectors has one matrix-unit source coordinate. -/
private theorem rankOne_basis_coordinates {A B A' B' : Type}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    [DecidableEq (A × B)] [DecidableEq (A' × B')]
    (U V : HSpace) (bU : OrthonormalBasis A ℂ U) (bV : OrthonormalBasis B ℂ V)
    (bU' : OrthonormalBasis A' ℂ U) (bV' : OrthonormalBasis B' ℂ V)
    (a : A × B) (b : A' × B') :
    Matrix.vecMulVec ((bU.tensorProduct bV).repr (bU a.1 ⊗ₜ[ℂ] bV a.2))
      (fun j ↦ conj ((bU'.tensorProduct bV').repr (bU' b.1 ⊗ₜ[ℂ] bV' b.2) j)) =
      Matrix.single a b 1 := by
  classical
  rw [← OrthonormalBasis.tensorProduct_apply', ← OrthonormalBasis.tensorProduct_apply',
    OrthonormalBasis.repr_self, OrthonormalBasis.repr_self]
  ext i j
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [Matrix.vecMulVec, Matrix.single, ha, hb, eq_comm]

/-- Expanding only selected endpoint coordinates is exactly the full source contraction
with arbitrary matrices on those slots and the original rank-one sources elsewhere.
No normalization, allowedness, or positivity assumption is imposed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem Word.sourceContraction_preparedDensityCoefficient_selected {P m n : Type}
    [Fintype m] [Fintype n] (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B A' B' : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V i))
    (η ζ : ∀ i, U i ⊗[ℂ] V i) (S : Finset (Fin R.length))
    (E : ∀ i, Matrix (A i × B i) (A' i × B' i) ℂ)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) :
    Matrix.sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
          (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ
          (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ if i ∈ S then E i else
          Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (η i))
            (fun b ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) b))) =
      ∑ a : ∀ i : S, A i × B i, ∑ b : ∀ i : S, A' i × B' i,
        (∏ i : S, E i (a i) (b i)) •
          (v.preparedMatrix R U V
            (fun i ↦ if h : i ∈ S then bU i (a ⟨i, h⟩).1 ⊗ₜ[ℂ] bV i (a ⟨i, h⟩).2
              else η i) ℓ bIn bOut * ρ *
            (v'.preparedMatrix R U V
              (fun i ↦ if h : i ∈ S then bU' i (b ⟨i, h⟩).1 ⊗ₜ[ℂ] bV' i (b ⟨i, h⟩).2
                else ζ i) ℓ bIn bOut)ᴴ) := by
  classical
  let X : ∀ i, Matrix (A i × B i) (A' i × B' i) ℂ := fun i ↦
    Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (η i))
      (fun b ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) b))
  let F := Matrix.sourceContraction
    (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
      (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ
      (fun i ↦ (x i).1) (fun i ↦ (x i).2))
  change F (S.piecewise E X) = _
  rw [selected_matrix_expansion]
  let H : ((∀ i : S, A i × B i) × (∀ i : S, A' i × B' i)) → Matrix m m ℂ :=
    fun ab ↦ (∏ i : S, E i (ab.1 i) (ab.2 i)) •
      (v.preparedMatrix R U V
        (fun i ↦ if h : i ∈ S then bU i (ab.1 ⟨i, h⟩).1 ⊗ₜ[ℂ] bV i (ab.1 ⟨i, h⟩).2
          else η i) ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V
          (fun i ↦ if h : i ∈ S then bU' i (ab.2 ⟨i, h⟩).1 ⊗ₜ[ℂ] bV' i (ab.2 ⟨i, h⟩).2
            else ζ i) ℓ bIn bOut)ᴴ)
  calc
    _ = ∑ ab, H ab := by
      apply Fintype.sum_equiv
        (Equiv.arrowProdEquivProdArrow S (fun i ↦ A i × B i) (fun i ↦ A' i × B' i)) _ H
      intro z
      apply congrArg ((∏ i : S, E i (z i).1 (z i).2) • ·)
      let ηz : ∀ i, U i ⊗[ℂ] V i := fun i ↦ if h : i ∈ S then
        bU i (z ⟨i, h⟩).1.1 ⊗ₜ[ℂ] bV i (z ⟨i, h⟩).1.2 else η i
      let ζz : ∀ i, U i ⊗[ℂ] V i := fun i ↦ if h : i ∈ S then
        bU' i (z ⟨i, h⟩).2.1 ⊗ₜ[ℂ] bV' i (z ⟨i, h⟩).2.2 else ζ i
      have hcoords : (fun i ↦ if h : i ∈ S then
          Matrix.single (z ⟨i, h⟩).1 (z ⟨i, h⟩).2 1 else X i) =
          (fun i ↦ Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (ηz i))
            (fun b ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζz i) b))) := by
        funext i
        by_cases hi : i ∈ S
        · simp only [ηz, ζz, dite_eq_left hi]
          exact (rankOne_basis_coordinates (U i) (V i)
            (bU i) (bV i) (bU' i) (bV' i) (z ⟨i, hi⟩).1 (z ⟨i, hi⟩).2).symm
        · simp [hi, ηz, ζz, X]
      rw [hcoords]
      exact v.sourceContraction_preparedDensityCoefficient_basis R U V bU bV bU' bV'
        ηz ζz ℓ v' bIn bOut ρ
    _ = _ := Fintype.sum_prod_type H

end TNLean.PEPS.PairEffect
