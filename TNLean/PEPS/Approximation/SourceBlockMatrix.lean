/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedMatrixNorm
import TNLean.PEPS.Approximation.SourceSlotBasis

/-!
# Joint contraction of free source inputs

The columns associated with all source assignments form one matrix of the
remaining allowed word. Its operator norm is at most one, independently of the
number and dimensions of the sources. This bound applies to arbitrary
superpositions of source and physical inputs.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 383–468, in particular the free-input contractions
used to separate the corrected source coefficients.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-free-input-matrix-word.freesourcematrix
Downstream declaration: TNLean.PEPS.PairEffect.Word.freeSourceMatrix

Provenance-ID: 8769-free-input-matrix-word.freesourcematrix_apply
Downstream declaration: TNLean.PEPS.PairEffect.Word.freeSourceMatrix_apply

Provenance-ID: 8769-free-input-matrix-word.norm_freesourcematrix_le_one
Downstream declaration: TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_le_one

Provenance-ID: 8769-free-input-matrix-word.freesourcematrix_conjtranspose_mul_apply
Downstream declaration: TNLean.PEPS.PairEffect.Word.freeSourceMatrix_conjTranspose_mul_apply

Provenance-ID: 8769-free-input-matrix-word.norm_freesourcematrix_conjtranspose_mul_le_one
Downstream declaration: TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_conjTranspose_mul_le_one

Provenance-ID: 8769-free-input-matrix-word.trace_preparedmatrix_mul_conjtranspose_eq
Downstream declaration: TNLean.PEPS.PairEffect.Word.trace_preparedMatrix_mul_conjTranspose_eq

Provenance-ID: 8769-free-input-matrix-word.trace_prepareddensitycoefficient_eq_freesourcematrix
Downstream declaration:
TNLean.PEPS.PairEffect.Word.trace_preparedDensityCoefficient_eq_freeSourceMatrix
-/

noncomputable section

open scoped ComplexConjugate TensorProduct Matrix Matrix.Norms.L2Operator
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

variable {P m n : Type} [Fintype m] [Fintype n]
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    {A B : Fin R.length → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (bU : ∀ i, OrthonormalBasis (A i) ℂ (U i))
    (bV : ∀ i, OrthonormalBasis (B i) ℂ (V i))
    (ℓ : Layout P) {ℓ' : Layout P}

/-- The matrix of the remaining word with every source coordinate and every
physical input coordinate free. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 383–427. -/
def freeSourceMatrix (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    Matrix m ((∀ i, A i × B i) × n) ℂ := by
  classical
  exact LinearMap.toMatrix
    (SourceInventory.preparedInputBasis R U V bU bV ℓ bIn).toBasis
    bOut.toBasis v.eval.toLinearMap

/-- A block of the full matrix is the actual branch prepared with the corresponding
endpoint basis vectors. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–427. -/
theorem freeSourceMatrix_apply
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (a : ∀ i, A i × B i) (j : n) (k : m) :
    v.freeSourceMatrix R U V bU bV ℓ bIn bOut k (a, j) =
      v.preparedMatrix R U V (fun i ↦ bU i (a i).1 ⊗ₜ bV i (a i).2)
        ℓ bIn bOut k j := by
  classical
  simp only [freeSourceMatrix, preparedMatrix, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, SourceInventory.preparedInputBasis_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]

open Classical in
/-- The complete matrix is a contraction on arbitrary joint source/input vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem norm_freeSourceMatrix_le_one
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ') (hv : v.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    ‖v.freeSourceMatrix R U V bU bV ℓ bIn bOut‖ ≤ 1 := by
  classical
  rw [freeSourceMatrix, ContinuousLinearMap.norm_toMatrix_orthonormal]
  exact v.norm_eval_le_one hv

section BraKet

variable {n' : Type} [Fintype n']
    (R' : SourceInventory P) (U' V' : Fin R'.length → HSpace)
    {A' B' : Fin R'.length → Type} [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U' i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V' i))
    (ℓb : Layout P)

/-- The overlap of the complete bra and ket operators has exactly the overlaps
of the prepared coefficient operators as its blocks. The bra source assignment
is the row index. Their source and physical input spaces may differ.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem freeSourceMatrix_conjTranspose_mul_apply
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (v' : Word (SourceInventory.slotLayout R' U' V' ++ ℓb) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bBra : OrthonormalBasis n' ℂ (Mem ℓb))
    (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (a : ∀ i, A i × B i) (b : ∀ i, A' i × B' i) (i : n) (j : n') :
    ((v'.freeSourceMatrix R' U' V' bU' bV' ℓb bBra bOut)ᴴ *
      v.freeSourceMatrix R U V bU bV ℓ bIn bOut) (b, j) (a, i) =
    ((v'.preparedMatrix R' U' V' (fun e ↦ bU' e (b e).1 ⊗ₜ bV' e (b e).2)
        ℓb bBra bOut)ᴴ *
      v.preparedMatrix R U V (fun e ↦ bU e (a e).1 ⊗ₜ bV e (a e).2)
        ℓ bIn bOut) j i := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, freeSourceMatrix_apply]

open Classical in
/-- The actual bra-adjoint–ket product is a rectangular contraction, with no
factor depending on the number of source coordinates. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_freeSourceMatrix_conjTranspose_mul_le_one
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (v' : Word (SourceInventory.slotLayout R' U' V' ++ ℓb) ℓ')
    (hv : v.IsAllowed) (hv' : v'.IsAllowed)
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bBra : OrthonormalBasis n' ℂ (Mem ℓb))
    (bOut : OrthonormalBasis m ℂ (Mem ℓ')) :
    ‖(v'.freeSourceMatrix R' U' V' bU' bV' ℓb bBra bOut)ᴴ *
      v.freeSourceMatrix R U V bU bV ℓ bIn bOut‖ ≤ 1 := by
  classical
  apply (Matrix.l2_opNorm_mul _ _).trans
  rw [Matrix.l2_opNorm_conjTranspose]
  exact (mul_le_mul (norm_freeSourceMatrix_le_one R' U' V' bU' bV' ℓb v' hv' bBra bOut)
    (norm_freeSourceMatrix_le_one R U V bU bV ℓ v hv bIn bOut)
    (norm_nonneg _) zero_le_one).trans (by simp)

/-- A rectangular input coefficient pairs with the opposite-index block of the
actual bra-adjoint–ket operator after the common output is traced out.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–468. -/
theorem trace_preparedMatrix_mul_conjTranspose_eq
    (v : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (v' : Word (SourceInventory.slotLayout R' U' V' ++ ℓb) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bBra : OrthonormalBasis n' ℂ (Mem ℓb))
    (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n' ℂ) (a : ∀ i, A i × B i) (b : ∀ i, A' i × B' i) :
    Matrix.trace
      (v.preparedMatrix R U V (fun e ↦ bU e (a e).1 ⊗ₜ bV e (a e).2) ℓ bIn bOut *
        ρ * (v'.preparedMatrix R' U' V'
          (fun e ↦ bU' e (b e).1 ⊗ₜ bV' e (b e).2) ℓb bBra bOut)ᴴ) =
    ∑ i, ∑ j, ρ i j *
      ((v'.freeSourceMatrix R' U' V' bU' bV' ℓb bBra bOut)ᴴ *
        v.freeSourceMatrix R U V bU bV ℓ bIn bOut) (b, j) (a, i) := by
  classical
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp only [freeSourceMatrix_conjTranspose_mul_apply]
  rfl

end BraKet

variable {A' B' : Fin R.length → Type} [∀ i, Fintype (A' i)] [∀ i, Fintype (B' i)]
    (bU' : ∀ i, OrthonormalBasis (A' i) ℂ (U i))
    (bV' : ∀ i, OrthonormalBasis (B' i) ℂ (V i))

/-- Tracing an actual density coefficient pairs the input matrix with the
corresponding block of the complete bra-adjoint–ket contraction. The input
matrix need not be Hermitian or positive. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–468. -/
theorem trace_preparedDensityCoefficient_eq_freeSourceMatrix
    (v v' : Word (SourceInventory.slotLayout R U V ++ ℓ) ℓ')
    (bIn : OrthonormalBasis n ℂ (Mem ℓ)) (bOut : OrthonormalBasis m ℂ (Mem ℓ'))
    (ρ : Matrix n n ℂ) (a : ∀ i, A i × B i) (b : ∀ i, A' i × B' i) :
    Matrix.trace (v.preparedDensityCoefficient R U V
      (fun e ↦ bU e) (fun e ↦ bV e) (fun e ↦ bU' e) (fun e ↦ bV' e)
      ℓ v' bIn bOut ρ a b) =
    ∑ i, ∑ j, ρ i j *
      ((v'.freeSourceMatrix R U V bU' bV' ℓ bIn bOut)ᴴ *
        v.freeSourceMatrix R U V bU bV ℓ bIn bOut) (b, j) (a, i) := by
  classical
  exact trace_preparedMatrix_mul_conjTranspose_eq R U V bU bV ℓ
    R U V bU' bV' ℓ v v' bIn bIn bOut ρ a b

end TNLean.PEPS.PairEffect.Word
