/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapInteractionSupport
import TNLean.PEPS.Approximation.SheetSwapSiteSupport

/-!
# Support of a swapped tensor product

Pair the two physical values at each site. Conjugating a tensor product of
operators with common support by the regional sheet swap preserves
that support. The doubled-interaction statement follows by addition of its
two replica terms.

## Main results

* `reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators`: support of an
  individual conjugated tensor product.
* `reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators`: the
  doubled-interaction consequence.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.PEPS.EncodedFrame

/-- A regional swap preserves the common support of an individual tensor
product after pairing the two local coordinates. Empty regions and zero local
dimension are included, with no Hermiticity hypothesis.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (D S : Finset ι) {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ supportedOperators q (S : Set ι))
    (hB : B ∈ supportedOperators q (S : Set ι)) :
    let p := sitePairConfigurationEquiv ι q q
    let F := Matrix.reindex p p (sheetSwapOp q D)
    F * Matrix.reindex p p (A ⊗ₖ B) * Fᴴ ∈
      supportedOperators (q * q) (S : Set ι) := by
  classical
  have hF :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q (D ∩ S)) ∈ supportedOperators (q * q) (S : Set ι) :=
    supportedOperators_mono
      (show (↑(D ∩ S) : Set ι) ⊆ (S : Set ι) from
        Finset.coe_subset.mpr Finset.inter_subset_right)
      (reindex_sheetSwapOp_mem_supportedOperators q (D ∩ S))
  have hT :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (A ⊗ₖ B) ∈ supportedOperators (q * q) (S : Set ι) := by
    simpa only [Set.union_self] using reindex_kronecker_mem_supportedOperators hA hB
  dsimp only
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    sheetSwapOp_conj_kronecker_eq_inter D S hA hB] using
    mul_mem_supportedOperators
      (mul_mem_supportedOperators (star_mem_supportedOperators hF) hT) hF

/-- The swapped doubled interaction acts on its original support in
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
  simpa only [doubledHamiltonian, Matrix.reindex_apply, Matrix.submatrix_add,
    Pi.add_apply, Matrix.mul_add, Matrix.add_mul] using
    (supportedOperators (q * q) (S : Set ι)).add_mem
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S hA
        (one_mem_supportedOperators _))
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S
        (one_mem_supportedOperators _) hA)

end TNLean.PEPS.EncodedFrame
