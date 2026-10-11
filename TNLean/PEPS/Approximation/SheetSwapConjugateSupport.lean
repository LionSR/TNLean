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
  -- The conjugated sheet swap in paired coordinates is supported on `R ∩ S`.
  have hF :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q (R ∩ S)) ∈ supportedOperators (q * q) (S : Set ι) :=
    supportedOperators_mono
      (show (↑(R ∩ S) : Set ι) ⊆ (S : Set ι) from
        Finset.coe_subset.mpr Finset.inter_subset_right)
      (reindex_sheetSwapOp_mem_supportedOperators q (R ∩ S))
  -- The doubled interaction stays supported on `S` after pairing.
  have hT :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (doubledHamiltonian A) ∈ supportedOperators (q * q) (S : Set ι) := by
    simpa only [Set.union_self, doubledHamiltonian] using
      (supportedOperators (q * q) ((S : Set ι) ∪ (S : Set ι))).add_mem
        (reindex_kronecker_mem_supportedOperators hA
          (one_mem_supportedOperators (d := q) (S : Set ι)))
        (reindex_kronecker_mem_supportedOperators
          (one_mem_supportedOperators (d := q) (S : Set ι)) hA)
  -- Rewrite the conjugation in paired coordinates to the restricted swap.
  have hconj :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q R)
        * Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (doubledHamiltonian A)
        * (Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q R))ᴴ
      = (Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q (R ∩ S)))ᴴ
        * Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (doubledHamiltonian A)
        * Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q (R ∩ S)) := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [sheetSwapOp_conj_doubledHamiltonian_eq_inter R S hA]
  show Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q R)
      * Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (doubledHamiltonian A)
      * (Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q R))ᴴ ∈ supportedOperators (q * q) (S : Set ι)
  rw [hconj]
  exact mul_mem_supportedOperators
    (mul_mem_supportedOperators (star_mem_supportedOperators hF) hT) hF

end TNLean.PEPS.EncodedFrame
