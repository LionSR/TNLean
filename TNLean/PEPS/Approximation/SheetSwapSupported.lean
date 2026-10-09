/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapCorrection

/-!
# Sheet swaps exchange supported operators

The swap of two copies on a region exchanges the two tensor factors of operators supported
on that region. The support decomposition supplies their regional factors.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a` of `openai/math`.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.PEPS.EncodedFrame

/-- A sheet swap exchanges two operators supported on its region.

This is the local exchange identity used to cancel the two identical replica terms inside
the swapped region in the polynomial-PEPS manuscript, `02-information.tex`, lines 416–424. -/
theorem sheetSwapOp_mul_kronecker_of_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {R : Finset ι}
    {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (R : Set ι))
    (hB : B ∈ supportedOperators q (R : Set ι)) :
    sheetSwapOp q R * (A ⊗ₖ B) = (B ⊗ₖ A) * sheetSwapOp q R := by
  obtain ⟨A', hA'⟩ := exists_kronecker_one_of_mem_supportedOperators hA
  obtain ⟨B', hB'⟩ := exists_kronecker_one_of_mem_supportedOperators hB
  rw [sheetSwapOp, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, sheetSwap_symm]
  ext ⟨y₁, y₂⟩ ⟨r₁, r₂⟩
  simp only [submatrix_apply, kroneckerMap_apply, id]
  done

end TNLean.PEPS.EncodedFrame
