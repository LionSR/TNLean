/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedSourceContraction
import QICLean.Probability.ComplexGaussian.SourceTransportExpansion
import TNLean.Algebra.MultilinearSelectedSum

/-!
# Source contractions in endpoint frames

Transporting a source matrix through endpoint frames is equivalent to summing
its coefficients against the actual vectors in those frames. Applying this
identity at selected original source positions leaves all other source vectors
unchanged. No orthonormality or spanning assumption is needed for this identity.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–338 and 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate Kronecker

namespace TNLean.PEPS.PairEffect

open QICLean.ComplexGaussian

/-- The selected source matrices may be expressed in arbitrary endpoint frames.
The resulting coefficients multiply the actual prepared ket and bra words.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem Word.sourceContraction_preparedDensityCoefficient_selected_frames {P m n : Type}
    [Fintype m] [Fintype n] (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B A' B' K K' : Fin R.length → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    [∀ i, Fintype (K i)] [∀ i, Fintype (K' i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V i))
    (uU : ∀ i, K i → U i) (uV : ∀ i, K i → V i)
    (uU' : ∀ i, K' i → U i) (uV' : ∀ i, K' i → V i)
    (η ζ : ∀ i, U i ⊗[ℂ] V i) (S : Finset (Fin R.length))
    (M : ∀ i, Matrix (K i × K i) (K' i × K' i) ℂ)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) :
    Matrix.sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
          (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ
          (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ if i ∈ S then
          sourceTransport (fun a j ↦ (bU i).repr (uU i j) a)
            (fun a j ↦ (bV i).repr (uV i j) a)
            (fun a j ↦ (bU' i).repr (uU' i j) a)
            (fun a j ↦ (bV' i).repr (uV' i j) a) (M i)
          else Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (η i))
            (fun j ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) j))) =
      ∑ a : ∀ i : S, K i × K i, ∑ b : ∀ i : S, K' i × K' i,
        (∏ i : S, M i (a i) (b i)) •
          (v.preparedMatrix R U V
            (fun i ↦ if h : i ∈ S then uU i (a ⟨i, h⟩).1 ⊗ₜ[ℂ] uV i (a ⟨i, h⟩).2
              else η i) ℓ bIn bOut * ρ *
            (v'.preparedMatrix R U V
              (fun i ↦ if h : i ∈ S then uU' i (b ⟨i, h⟩).1 ⊗ₜ[ℂ] uV' i (b ⟨i, h⟩).2
                else ζ i) ℓ bIn bOut)ᴴ) := by
  classical
  let X : ∀ i, Matrix (A i × B i) (A' i × B' i) ℂ := fun i ↦
    Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (η i))
      (fun j ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζ i) j))
  let Z (i : Fin R.length) (z : (K i × K i) × (K' i × K' i)) :=
    Matrix.vecMulVec
      (((bU i).tensorProduct (bV i)).repr (uU i z.1.1 ⊗ₜ[ℂ] uV i z.1.2))
      (fun j ↦ conj (((bU' i).tensorProduct (bV' i)).repr
        (uU' i z.2.1 ⊗ₜ[ℂ] uV' i z.2.2) j))
  have ht (i : Fin R.length) :
      sourceTransport (fun a j ↦ (bU i).repr (uU i j) a)
          (fun a j ↦ (bV i).repr (uV i j) a)
          (fun a j ↦ (bU' i).repr (uU' i j) a)
          (fun a j ↦ (bV' i).repr (uV' i j) a) (M i) =
        ∑ z, M i z.1 z.2 • Z i z := by
    erw [sourceTransport_eq_sum_rankOne]
    apply Finset.sum_congr rfl
    intro z _
    apply congrArg (M i z.1 z.2 • ·)
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Z, Matrix.vecMulVec_apply,
      OrthonormalBasis.tensorProduct_repr_tmul_apply, mul_comm]
  let F := Matrix.sourceContraction
    (fun x ↦ v.preparedDensityCoefficient R U V (fun i ↦ bU i) (fun i ↦ bV i)
      (fun i ↦ bU' i) (fun i ↦ bV' i) ℓ v' bIn bOut ρ
      (fun i ↦ (x i).1) (fun i ↦ (x i).2))
  simp_rw [ht]
  change F (S.piecewise (fun i ↦ ∑ z, M i z.1 z.2 • Z i z) X) = _
  rw [MultilinearMap.map_piecewise_sum_smul]
  let H : ((∀ i : S, K i × K i) × (∀ i : S, K' i × K' i)) → Matrix m m ℂ :=
    fun ab ↦ (∏ i : S, M i (ab.1 i) (ab.2 i)) •
      (v.preparedMatrix R U V
        (fun i ↦ if h : i ∈ S then uU i (ab.1 ⟨i, h⟩).1 ⊗ₜ[ℂ] uV i (ab.1 ⟨i, h⟩).2
          else η i) ℓ bIn bOut * ρ *
        (v'.preparedMatrix R U V
          (fun i ↦ if h : i ∈ S then uU' i (ab.2 ⟨i, h⟩).1 ⊗ₜ[ℂ] uV' i (ab.2 ⟨i, h⟩).2
            else ζ i) ℓ bIn bOut)ᴴ)
  calc
    _ = ∑ ab, H ab := by
      apply Fintype.sum_equiv
        (Equiv.arrowProdEquivProdArrow S (fun i ↦ K i × K i) (fun i ↦ K' i × K' i)) _ H
      intro z
      apply congrArg ((∏ i : S, M i (z i).1 (z i).2) • ·)
      let ηz : ∀ i, U i ⊗[ℂ] V i := fun i ↦ if h : i ∈ S then
        uU i (z ⟨i, h⟩).1.1 ⊗ₜ[ℂ] uV i (z ⟨i, h⟩).1.2 else η i
      let ζz : ∀ i, U i ⊗[ℂ] V i := fun i ↦ if h : i ∈ S then
        uU' i (z ⟨i, h⟩).2.1 ⊗ₜ[ℂ] uV' i (z ⟨i, h⟩).2.2 else ζ i
      have he : (fun i ↦ if h : i ∈ S then Z i (z ⟨i, h⟩) else X i) =
          (fun i ↦ Matrix.vecMulVec (((bU i).tensorProduct (bV i)).repr (ηz i))
            (fun j ↦ conj (((bU' i).tensorProduct (bV' i)).repr (ζz i) j))) := by
        funext i
        by_cases hi : i ∈ S <;> simp [hi, ηz, ζz, Z, X]
      rw [he]
      exact v.sourceContraction_preparedDensityCoefficient_basis R U V bU bV bU' bV'
        ηz ζz ℓ v' bIn bOut ρ
    _ = _ := Fintype.sum_prod_type H

end TNLean.PEPS.PairEffect
