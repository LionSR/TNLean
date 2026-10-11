/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapInteractionSupport
import TNLean.PEPS.Approximation.SheetSwapSiteSupport

/-!
# Support of a swapped doubled interaction

Pair the two physical values at each site. Conjugating a doubled interaction
by the actual regional sheet swap preserves its original finite support.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit

namespace TNLean.PEPS.EncodedFrame

/-- The actual swapped doubled interaction acts on its original support in
the paired-site coordinates. Empty regions and zero local dimension are
included; no Hermiticity hypothesis is needed.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (R S : Finset ι) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (S : Set ι)) :
    let p := sitePairConfigurationEquiv ι q q
    let F := Matrix.reindex p p (sheetSwapOp q R)
    F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ ∈
      supportedOperators (q * q) (S : Set ι) := by
  classical
  simp only [Matrix.conjTranspose_reindex, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  done

end TNLean.PEPS.EncodedFrame
