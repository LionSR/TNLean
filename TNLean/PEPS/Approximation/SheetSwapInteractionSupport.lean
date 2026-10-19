/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapDoubledCancellation

/-!
# Restricting a sheet swap to an interaction support

For a tensor product of two operators supported on `S`, the sheet swap outside
`S` cancels from the conjugation. Thus only the swap on `D ∩ S` remains.
The doubled-interaction identity follows by adding its two replica terms.
The adjoint is kept on the left; unitarity suffices for these identities.

## Main results

* `sheetSwapOp_conj_kronecker_eq_inter`: restrict conjugation of a tensor product
  to the swap inside its common support.
* `sheetSwapOp_conj_doubledHamiltonian_eq_inter`: the doubled-interaction consequence.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  and `05-frames.tex`, lines 516–520, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.PEPS.EncodedFrame

/-- Conjugating a product of two operators supported on `S` depends only on
the partial swap inside `S`. Empty site types and zero local dimension are
included; no Hermiticity hypothesis is needed.

Source: polynomial-PEPS manuscript, `05-frames.tex`, lines 516–520, and
`02-information.tex`, lines 416–424 and 513–524. -/
theorem sheetSwapOp_conj_kronecker_eq_inter
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (D S : Finset ι) {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (S : Set ι))
    (hB : B ∈ supportedOperators q (S : Set ι)) :
    sheetSwapOp q D * (A ⊗ₖ B) * (sheetSwapOp q D)ᴴ =
      (sheetSwapOp q (D ∩ S))ᴴ * (A ⊗ₖ B) * sheetSwapOp q (D ∩ S) := by
  classical
  have hcomp : sheetSwapOp q (D ∩ S) * sheetSwapOp q D = sheetSwapOp q (D \ S) :=
    sheetSwapOp_mul_sheetSwapOp
      (fun x ↦ by rw [← Finset.mem_sdiff, Finset.sdiff_inter_self_left])
      Finset.inter_subset_left
  have hunit : (sheetSwapOp q (D ∩ S))ᴴ * sheetSwapOp q (D ∩ S) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (sheetSwap q (D ∩ S)).permMatrix_mem_unitaryGroup
  have hD : sheetSwapOp q D =
      (sheetSwapOp q (D ∩ S))ᴴ * sheetSwapOp q (D \ S) := by
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul] using
      congrArg (fun X ↦ (sheetSwapOp q (D ∩ S))ᴴ * X) hcomp
  have hcancel : sheetSwapOp q (D \ S) * (A ⊗ₖ B) *
      (sheetSwapOp q (D \ S))ᴴ = A ⊗ₖ B := by
    have hcomm := commute_sheetSwapOp_kronecker (S := D \ S)
      (Finset.disjoint_coe.mpr Finset.disjoint_sdiff) hA hB
    have hunitE : sheetSwapOp q (D \ S) * (sheetSwapOp q (D \ S))ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (sheetSwap q (D \ S)).permMatrix_mem_unitaryGroup
    rw [hcomm.eq, Matrix.mul_assoc, hunitE, Matrix.mul_one]
  simpa only [hD, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using
    congrArg (fun X ↦ (sheetSwapOp q (D ∩ S))ᴴ * X * sheetSwapOp q (D ∩ S)) hcancel

/-- Conjugation of a doubled supported interaction depends only on the sheet
swap inside its original support. No Hermiticity or dimension assumption is
needed.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem sheetSwapOp_conj_doubledHamiltonian_eq_inter
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (R S : Finset ι) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (S : Set ι)) :
    sheetSwapOp q R * doubledHamiltonian A * (sheetSwapOp q R)ᴴ =
      (sheetSwapOp q (R ∩ S))ᴴ * doubledHamiltonian A * sheetSwapOp q (R ∩ S) := by
  simpa only [doubledHamiltonian, Matrix.mul_add, Matrix.add_mul] using
    congrArg₂ (· + ·)
      (sheetSwapOp_conj_kronecker_eq_inter R S hA (one_mem_supportedOperators _))
      (sheetSwapOp_conj_kronecker_eq_inter R S (one_mem_supportedOperators _) hA)

end TNLean.PEPS.EncodedFrame
