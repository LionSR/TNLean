/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.Circuit.Gates.Permutation
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.Lattice.RegionalSwap
import QICLean.Analysis.DoubledSystemGap

/-!
# Support of the regional swap and of swapped doubled interactions

Pairing the two local coordinates at each site identifies the two-copy space with a single
configuration space of local dimension `q * q`. In these coordinates the regional swap `F_R`
acts only on `R`. Conjugating a doubled interaction by `F_R` leaves it unchanged when its
support lies inside or outside `R`, depends only on the swap inside its support, and keeps its
support. Empty regions, empty site types and zero local dimension are included, and no
Hermiticity hypothesis is needed.

## Main results

* `TNLean.Lattice.reindex_sheetSwapOp_mem_supportedOperators`: `F_R` acts on `R` in paired
  site coordinates.
* `TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators`: a doubled
  interaction on one side of the boundary of `R` is unchanged by conjugation.
* `TNLean.Lattice.sheetSwapOp_conj_kronecker_eq_inter`,
  `TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_inter`: only the swap inside the
  common support of the operators remains.
* `TNLean.Lattice.reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators`,
  `TNLean.Lattice.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators`: the
  conjugated operators keep their support in paired site coordinates.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524, and `05-frames.tex`,
  lines 516–520, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.Lattice

/-- The actual sheet swap is supported on its original region after pairing
the two configuration values at every site. Empty regions, empty site types,
and zero local dimension are included.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) (R : Finset ι) :
    Matrix.reindex (sitePairConfigurationEquiv ι q q)
        (sitePairConfigurationEquiv ι q q) (sheetSwapOp q R) ∈
      supportedOperators (q * q) (R : Set ι) := by
  classical
  rw [Matrix.reindex_apply, sheetSwapOp, Matrix.toMatrix_toPEquiv_submatrix]
  apply IsLocalPerm.permMatrix_mem_supportedOperators
  constructor
  case right =>
    intro x y hxy i hi
    simp [sitePairConfigurationEquiv, sheetSwap, hxy i hi]
  case left =>
    intro x i hi
    change i ∉ R at hi
    suffices finProdFinEquiv ((x i).divNat, (x i).modNat) = x i by
      simpa [sitePairConfigurationEquiv, sheetSwap, hi] using this
    exact finProdFinEquiv.apply_symm_apply (x i)

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
  rcases hS with hinside | houtside
  · simpa only [Commute, SemiconjBy, doubledHamiltonian, Matrix.mul_add,
      Matrix.add_mul, add_comm] using
      congrArg₂ (· + ·)
        (sheetSwapOp_mul_kronecker_of_mem_supportedOperators
          (supportedOperators_mono hinside hA) (one_mem_supportedOperators _))
        (sheetSwapOp_mul_kronecker_of_mem_supportedOperators
          (one_mem_supportedOperators _) (supportedOperators_mono hinside hA))
  · exact (commute_sheetSwapOp_kronecker houtside hA
      (one_mem_supportedOperators _)).add_right
      (commute_sheetSwapOp_kronecker houtside (one_mem_supportedOperators _) hA)

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

end TNLean.Lattice
