/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PermutationMatrixUnitary
import TNLean.Circuit.SitePermutation
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.Circuit.RegionalSwap
import QICLean.Analysis.DoubledSystemGap

/-!
# Support of the regional swap and of swapped doubled interactions

Pairing the two local coordinates at each site identifies the two-copy space with a single
configuration space whose sites carry pairs of local values. In these coordinates the regional
swap `F_R` acts only on `R`. Conjugating a doubled interaction by `F_R` leaves it unchanged
when its support lies inside or outside `R`, depends only on the swap inside its support, and
keeps its support. Empty regions, empty site types and zero local dimension are included, and no
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
      ManyBody.supportedOperators (fun _ ↦ Fin q × Fin q) R := by
  classical
  let m : ι → Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ := fun i ↦
    Matrix.of fun a b ↦ if (if i ∈ R then a.swap else a) = b then 1 else 0
  have heq : Matrix.reindex (sitePairConfigurationEquiv ι q q)
      (sitePairConfigurationEquiv ι q q) (sheetSwapOp q R) = ManyBody.prodOp m := by
    ext x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, ManyBody.prodOp_apply, m,
      Matrix.of_apply, sheetSwapOp, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies]
    refine if_congr ?_ rfl rfl
    simp only [sitePairConfigurationEquiv, sheetSwap, Equiv.coe_fn_mk, Prod.ext_iff,
      funext_iff, Equiv.arrowProdEquivProdArrow]
    refine ⟨fun h i ↦ ?_, fun h ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩⟩
    · have h₁ := h.1 i
      have h₂ := h.2 i
      by_cases hi : i ∈ R <;> simp_all
    · have := h i
      by_cases hi : i ∈ R <;> simp_all
    · have := h i
      by_cases hi : i ∈ R <;> simp_all
  rw [heq]
  refine ManyBody.prodOp_mem_supportedOperators fun i hi ↦ ?_
  ext a b
  simp [m, hi, Matrix.one_apply]

/-- A doubled interaction supported entirely on one side of a regional boundary
is unchanged by conjugation with the actual sheet swap.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {R : Finset ι} {S : Finset ι} {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
    (hS : S ⊆ R ∨ Disjoint S R) :
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
          (ManyBody.supportedOperators_mono hinside hA) (one_mem (ManyBody.supportedOperators _ _)))
        (sheetSwapOp_mul_kronecker_of_mem_supportedOperators
          (one_mem (ManyBody.supportedOperators _ _)) (ManyBody.supportedOperators_mono hinside hA))
  · exact (commute_sheetSwapOp_kronecker houtside hA
      (one_mem (ManyBody.supportedOperators _ _))).add_right
      (commute_sheetSwapOp_kronecker houtside (one_mem (ManyBody.supportedOperators _ _)) hA)

/-- Conjugating a product of two operators supported on `S` depends only on
the partial swap inside `S`. Empty site types and zero local dimension are
included; no Hermiticity hypothesis is needed.

Source: polynomial-PEPS manuscript, `05-frames.tex`, lines 516–520, and
`02-information.tex`, lines 416–424 and 513–524. -/
theorem sheetSwapOp_conj_kronecker_eq_inter
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (D S : Finset ι) {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
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
      Finset.disjoint_sdiff hA hB
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
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
    sheetSwapOp q R * doubledHamiltonian A * (sheetSwapOp q R)ᴴ =
      (sheetSwapOp q (R ∩ S))ᴴ * doubledHamiltonian A * sheetSwapOp q (R ∩ S) := by
  simpa only [doubledHamiltonian, Matrix.mul_add, Matrix.add_mul] using
    congrArg₂ (· + ·)
      (sheetSwapOp_conj_kronecker_eq_inter R S hA (one_mem (ManyBody.supportedOperators _ _)))
      (sheetSwapOp_conj_kronecker_eq_inter R S (one_mem (ManyBody.supportedOperators _ _)) hA)

/-- A regional swap preserves the common support of an individual tensor
product after pairing the two local coordinates. Empty regions and zero local
dimension are included, with no Hermiticity hypothesis.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (D S : Finset ι) {A B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
    let p := sitePairConfigurationEquiv ι q q
    let F := Matrix.reindex p p (sheetSwapOp q D)
    F * Matrix.reindex p p (A ⊗ₖ B) * Fᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q × Fin q) S := by
  classical
  have hF :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q (D ∩ S)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q × Fin q) S :=
    ManyBody.supportedOperators_mono
      Finset.inter_subset_right
      (reindex_sheetSwapOp_mem_supportedOperators q (D ∩ S))
  have hT :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (A ⊗ₖ B) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q × Fin q) S := by
    simpa only [Finset.union_self] using reindex_kronecker_mem_supportedOperators hA hB
  dsimp only
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    sheetSwapOp_conj_kronecker_eq_inter D S hA hB] using
    mul_mem
      (mul_mem (star_mem hF) hT) hF

/-- The swapped doubled interaction acts on its original support in
the paired-site coordinates. Empty regions and zero local dimension are
included; no Hermiticity hypothesis is needed.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (R S : Finset ι) {A : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S) :
    let p := sitePairConfigurationEquiv ι q q
    let F := Matrix.reindex p p (sheetSwapOp q R)
    F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q × Fin q) S := by
  simpa only [doubledHamiltonian, Matrix.reindex_apply, Matrix.submatrix_add,
    Pi.add_apply, Matrix.mul_add, Matrix.add_mul] using
    add_mem
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S hA
        (one_mem (ManyBody.supportedOperators _ _)))
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S
        (one_mem (ManyBody.supportedOperators _ _)) hA)

end TNLean.Lattice
