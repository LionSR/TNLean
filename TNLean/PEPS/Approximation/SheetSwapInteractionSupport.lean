/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapDoubledCancellation

/-!
# Restricting a sheet swap to an interaction support

For an interaction supported on `S`, the sheet swap outside `S` cancels from
the conjugated doubled interaction. Thus only the swap on `R ∩ S` remains.
The adjoint is kept on the left; unitarity suffices for this identity.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit

namespace TNLean.PEPS.EncodedFrame

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
  classical
  have hcomp : sheetSwapOp q (R ∩ S) * sheetSwapOp q R = sheetSwapOp q (R \ S) :=
    sheetSwapOp_mul_sheetSwapOp
      (fun x ↦ by rw [← Finset.mem_sdiff, Finset.sdiff_inter_self_left])
      Finset.inter_subset_left
  have hunit : (sheetSwapOp q (R ∩ S))ᴴ * sheetSwapOp q (R ∩ S) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (sheetSwap q (R ∩ S)).permMatrix_mem_unitaryGroup
  have hR : sheetSwapOp q R =
      (sheetSwapOp q (R ∩ S))ᴴ * sheetSwapOp q (R \ S) := by
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul] using
      congrArg (fun X ↦ (sheetSwapOp q (R ∩ S))ᴴ * X) hcomp
  have hcancel : sheetSwapOp q (R \ S) * doubledHamiltonian A *
      (sheetSwapOp q (R \ S))ᴴ = doubledHamiltonian A :=
    sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators hA
      (Or.inr (Finset.disjoint_coe.mpr Finset.disjoint_sdiff))
  simpa only [hR, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using
    congrArg (fun X ↦ (sheetSwapOp q (R ∩ S))ᴴ * X * sheetSwapOp q (R ∩ S)) hcancel

end TNLean.PEPS.EncodedFrame
