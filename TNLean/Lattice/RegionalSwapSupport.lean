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
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Sites.PairSwap

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
* `TNLean.Lattice.reindex_sheetSwapOp_eq_reindex_pairSwapOp`: in paired site coordinates
  `F_R` is the exchange `ManyBody.pairSwapOp R` of the two copies on `R`.
* `TNLean.Lattice.hamiltonian_relabel_conj_pairSwapOp_doubled`: the doubled interaction
  conjugated by that exchange, in paired site coordinates, has Hamiltonian `F_R K F_Rᴴ`.

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
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) R := by
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
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
  classical
  have hF :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q (D ∩ S)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S :=
    ManyBody.supportedOperators_mono
      Finset.inter_subset_right
      (reindex_sheetSwapOp_mem_supportedOperators q (D ∩ S))
  have hT :
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (A ⊗ₖ B) ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    have h := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl ι)
      (X' := fun _ ↦ Fin (q * q)) (fun _ ↦ finProdFinEquiv) (fun _ ↦ Iff.rfl)
      (ManyBody.reindex_kronecker_mem_supportedOperators hA hB)
    rw [Finset.union_self] at h
    convert h using 1
    ext x y
    simp [sitePairConfigurationEquiv, ManyBody.siteConfigurationEquiv]
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
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
  simpa only [doubledHamiltonian, Matrix.reindex_apply, Matrix.submatrix_add,
    Pi.add_apply, Matrix.mul_add, Matrix.add_mul] using
    add_mem
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S hA
        (one_mem (ManyBody.supportedOperators _ _)))
      (reindex_sheetSwapOp_conj_kronecker_mem_supportedOperators R S
        (one_mem (ManyBody.supportedOperators _ _)) hA)

/-- **The sheet swap in paired coordinates is the exchange of the two copies.** After pairing
the two configuration values at every site, the sheet swap `F_R` is the exchange
`(a, b) ↦ (b, a)` of the two copies at the sites of `R`, relabelled along `finProdFinEquiv` at
every site.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424. -/
theorem reindex_sheetSwapOp_eq_reindex_pairSwapOp
    {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ) (R : Finset ι) :
    Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (sheetSwapOp q R) =
      Matrix.reindex
        (ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
          fun _ ↦ finProdFinEquiv)
        (ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
          fun _ ↦ finProdFinEquiv)
        (ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) R) := by
  ext x y
  let a : ι → Fin q × Fin q := fun i ↦ finProdFinEquiv.symm (x i)
  let b : ι → Fin q × Fin q := fun i ↦ finProdFinEquiv.symm (y i)
  have hsite (i : ι) :
      (if i ∈ R then Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin q) (Fin q))
        else (1 : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ)) (a i) (b i) =
        if b i = (if i ∈ R then (a i).swap else a i) then 1 else 0 := by
    by_cases hi : i ∈ R
    · simp [hi, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
    · simp only [hi, ↓reduceIte, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
  have hL : sheetSwapOp q R ((sitePairConfigurationEquiv ι q q).symm x)
      ((sitePairConfigurationEquiv ι q q).symm y) =
      if (sitePairConfigurationEquiv ι q q).symm y =
        sheetSwap q R ((sitePairConfigurationEquiv ι q q).symm x) then 1 else 0 := by
    simp only [sheetSwapOp, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  have hR : ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) R
      ((ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
        fun _ ↦ finProdFinEquiv).symm x)
      ((ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
        fun _ ↦ finProdFinEquiv).symm y) =
      ∏ i, if b i = (if i ∈ R then (a i).swap else a i) then 1 else 0 := by
    rw [ManyBody.pairSwapOp, ManyBody.prodOp_apply]
    exact Finset.prod_congr rfl fun i _ ↦ hsite i
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hL, hR, Fintype.prod_boole]
  refine if_congr ⟨fun h i ↦ ?_, fun h ↦ ?_⟩ rfl rfl
  · have h1 : (b i).1 = if i ∈ R then (a i).2 else (a i).1 :=
      congrFun (congrArg Prod.fst h) i
    have h2 : (b i).2 = if i ∈ R then (a i).1 else (a i).2 :=
      congrFun (congrArg Prod.snd h) i
    by_cases hi : i ∈ R
    · simp only [hi, ↓reduceIte] at h1 h2 ⊢
      exact Prod.ext h1 h2
    · simp only [hi, ↓reduceIte] at h1 h2 ⊢
      exact Prod.ext h1 h2
  · refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · change (b i).1 = if i ∈ R then (a i).2 else (a i).1
      have hi' := h i
      by_cases hi : i ∈ R
      · simp only [hi, ↓reduceIte] at hi' ⊢
        exact congrArg Prod.fst hi'
      · simp only [hi, ↓reduceIte] at hi' ⊢
        exact congrArg Prod.fst hi'
    · change (b i).2 = if i ∈ R then (a i).1 else (a i).2
      have hi' := h i
      by_cases hi : i ∈ R
      · simp only [hi, ↓reduceIte] at hi' ⊢
        exact congrArg Prod.snd hi'
      · simp only [hi, ↓reduceIte] at hi' ⊢
        exact congrArg Prod.snd hi'

/-- **The swapped doubled Hamiltonian.** For an interaction `Φ` of local dimension `q`, conjugate
the doubled interaction by the exchange of the two copies on `D` and pair the two copies of
every site into `Fin (q * q)` along `finProdFinEquiv`. Its Hamiltonian is `F_D K F_Dᴴ`, for the
doubled Hamiltonian `K` and the sheet swap `F_D` in paired coordinates.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424; TNLean
one-dimensional note, `part2a_mps_information.tex`, lines 355–363. -/
theorem hamiltonian_relabel_conj_pairSwapOp_doubled {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] {S : κ → Finset ι} {q : ℕ}
    (Φ : ManyBody.Interaction (fun _ : ι ↦ Fin q) S) (D : Finset ι)
    (hP : ∀ k, ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) D * Φ.doubled.term k *
        (ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) D)ᴴ ∈
      ManyBody.supportedOperators (fun _ : ι ↦ Fin q × Fin q) (S k)) :
    ((Φ.doubled.conj (ManyBody.pairSwapOp (X := fun _ : ι ↦ Fin q) D) hP).relabel
        (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι) (fun _ ↦ finProdFinEquiv) S
        fun _ _ ↦ Iff.rfl).hamiltonian =
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q D) *
        Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (doubledHamiltonian Φ.hamiltonian) *
        (Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
          (sheetSwapOp q D))ᴴ := by
  have hK : Matrix.reindex
      (ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
        fun _ ↦ finProdFinEquiv)
      (ManyBody.siteConfigurationEquiv (X' := fun _ : ι ↦ Fin (q * q)) (Equiv.refl ι)
        fun _ ↦ finProdFinEquiv) Φ.doubled.hamiltonian =
      Matrix.reindex (sitePairConfigurationEquiv ι q q) (sitePairConfigurationEquiv ι q q)
        (doubledHamiltonian Φ.hamiltonian) := by
    rw [ManyBody.Interaction.hamiltonian_doubled]
    ext x y
    simp [sitePairConfigurationEquiv, ManyBody.siteConfigurationEquiv]
  rw [ManyBody.Interaction.hamiltonian_relabel, ManyBody.Interaction.hamiltonian_conj,
    reindex_sheetSwapOp_eq_reindex_pairSwapOp, ← hK]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

end TNLean.Lattice
