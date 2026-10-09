/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.PEPS.Approximation.SheetSwapSupported
import QICLean.Analysis.DoubledSystemGap

/-!
# Cancellation of doubled interactions away from a regional boundary

Swapping two copies on a region leaves a doubled interaction unchanged whenever
its support lies entirely inside or entirely outside that region. This is the
cancellation that reduces the doubled Hamiltonian perturbation to crossing edges.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit

namespace TNLean.PEPS.EncodedFrame

/-- A doubled interaction supported entirely on one side of a regional boundary
is unchanged by conjugation with the actual sheet swap.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {R : Finset ι} {S : Set ι} {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q S)
    (hS : S ⊆ (R : Set ι) ∨ Disjoint S (R : Set ι)) :
    sheetSwapOp q R * doubledHamiltonian A * (sheetSwapOp q R)ᴴ =
      doubledHamiltonian A := by
  classical
  have hunit : sheetSwapOp q R * (sheetSwapOp q R)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (sheetSwap q R).permMatrix_mem_unitaryGroup
  suffices hcomm : Commute (sheetSwapOp q R) (doubledHamiltonian A) by
    rw [hcomm.eq, Matrix.mul_assoc, hunit, Matrix.mul_one]
  done

end TNLean.PEPS.EncodedFrame
