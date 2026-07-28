/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.RecoveredConditionalAmbientBipartiteBlockForm
import TNLean.Channel.Stinespring

/-!
# Recovered conditional dilation block form

This file constructs the recovery dilation at equality in strong
subadditivity.  In the ambient direct-sum tensor coordinates of the middle
subsystem, the dilation unitary is block diagonal and acts trivially on every
conditional factor.  The physical unitary is the conjugate of that literal
block-coordinate unitary by the ambient middle-system change of basis.

Source: Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 6, equation (15), lines 547--560;
Appendix A, Theorem 10, Property 2, lines 791--800; the equivalence
2 iff 2', lines 808--823; and the operation-level proof of 2',
lines 853--882.

We construct one chosen pure-ancilla physical unitary.  Its recovery is
proved to agree with the Petz channel on
inputs supported by the minimum joint support and to satisfy the exact
recovery identity in equation (11).  No equality of the two channels is
asserted on the ambient complementary sector.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

/-- Fix the right output coordinate of a rectangular matrix. -/
private def rightOutputSlice
    {A B C : Type*} (R : Matrix (B × C) A ℂ) (c : C) :
    Matrix B A ℂ :=
  fun b a => R (b, c) a

@[simp]
private theorem ambientSupportEmbedding_apply
    {dB n : ℕ} (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (b : Fin dB) (s : Fin n) :
    ambientSupportEmbedding e₀ b s =
      if b = e₀ (Sum.inr s) then 1 else 0 := by
  simp [ambientSupportEmbedding, Matrix.one_apply]

@[simp]
private theorem mul_ambientSupportEmbedding_apply
    {A : Type*} {dB n : ℕ}
    (W : Matrix A (Fin dB) ℂ)
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB) (a : A) (s : Fin n) :
    (W * ambientSupportEmbedding e₀) a s = W a (e₀ (Sum.inr s)) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (e₀ (Sum.inr s))]
  · simp
  · intro b _ hne
    simp [ambientSupportEmbedding_apply, hne]
  · simp

@[simp]
private theorem ambientSupportEmbedding_mul_apply_support
    {dB n : ℕ} (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (A : Matrix (Fin n) (Fin n) ℂ) (s t : Fin n) :
    (ambientSupportEmbedding e₀ * A) (e₀ (Sum.inr s)) t = A s t := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs'
    have hne : e₀ (Sum.inr s) ≠ e₀ (Sum.inr s') := by
      intro h
      exact hs' (Sum.inr.inj (e₀.injective h.symm))
    simp [ambientSupportEmbedding_apply, hne]
  · simp

@[simp]
private theorem ambientSupportEmbedding_mul_apply_complement
    {dB n : ℕ} (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin (dB - n)) (t : Fin n) :
    (ambientSupportEmbedding e₀ * A) (e₀ (Sum.inl z)) t = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro s _
  have hne : e₀ (Sum.inl z) ≠ e₀ (Sum.inr s) := by
    intro h
    exact Sum.inl_ne_inr (e₀.injective h)
  simp [ambientSupportEmbedding_apply, hne]

/-- Tracing the right output of a rectangular Kraus map is the Kraus map of
all right-output slices. -/
private theorem partialTraceRight_rectangularKrausMap_eq_slices
    {κ A B C : Type*} [Fintype κ] [Fintype A] [Fintype C]
    (R : κ → Matrix (B × C) A ℂ) (X : Matrix A A ℂ) :
    partialTraceRight (rectangularKrausMap R X) =
      rectangularKrausMap
        (fun p : C × κ => rightOutputSlice (R p.2) p.1) X := by
  ext b b'
  simp only [partialTraceRight_apply, rectangularKrausMap,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, rightOutputSlice]

/-- A system-only left multiplication acts on every right-output slice. -/
private theorem rightOutputSlice_kronecker_one_mul
    {A B E : Type*} [Fintype B]
    [Fintype E] [DecidableEq E]
    (U : Matrix B B ℂ) (W : Matrix (B × E) A ℂ) (e₀ : E) :
    rightOutputSlice
        ((U ⊗ₖ (1 : Matrix E E ℂ)) * W) e₀ =
      U * rightOutputSlice W e₀ := by
  ext b a
  simp only [rightOutputSlice, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b' _
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

/-- A slice of the reassociated rectangular Stinespring matrix is the
corresponding right-output slice of its Kraus operator. -/
private theorem rightOutputSlice_reindex_stinespringV_mul
    {A B C N : Type*} {r : ℕ} [Fintype A]
    (R : Fin r → Matrix (B × C) A ℂ) (Z : Matrix A N ℂ)
    (c : C) (i : Fin r) :
    rightOutputSlice
        (Matrix.reindex (Equiv.prodAssoc B C (Fin r))
          (Equiv.refl N) (stinespringV R * Z)) (c, i) =
      rightOutputSlice (R i) c * Z := by
  ext b a
  simp [rightOutputSlice, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodAssoc, Matrix.mul_apply, stinespringV_apply]

/-- Insert a finite system into one fixed environment coordinate. -/
def fixedEnvEmbedding
    {S E : Type*} [DecidableEq S] [DecidableEq E] (e₀ : E) :
    Matrix (S × E) S ℂ :=
  fun se s => if se.2 = e₀ then (1 : Matrix S S ℂ) se.1 s else 0

/-- The fixed-environment insertion is an isometry. -/
private theorem fixedEnvEmbedding_conjTranspose_mul_self
    {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (e₀ : E) :
    (fixedEnvEmbedding (S := S) e₀)ᴴ * fixedEnvEmbedding (S := S) e₀ = 1 := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hst : s = t
  · subst t
    simp [fixedEnvEmbedding, Matrix.one_apply]
  · have hts : t ≠ s := fun h => hst h.symm
    simp [fixedEnvEmbedding, Matrix.one_apply, hst, hts]

@[simp]
private theorem mul_fixedEnvEmbedding_apply
    {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E]
    (U : Matrix (S × E) (S × E) ℂ) (e₀ : E)
    (se : S × E) (s : S) :
    (U * fixedEnvEmbedding (S := S) e₀) se s = U se (s, e₀) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (s, e₀)]
  · simp [fixedEnvEmbedding]
  · rintro ⟨s', e'⟩ _ hne
    by_cases h : e' = e₀
    · subst e'
      have hs : s' ≠ s := by
        intro hs
        exact hne (Prod.ext hs rfl)
      simp [fixedEnvEmbedding, hs]
    · simp [fixedEnvEmbedding, h]
  · simp

/-- Fixed-environment insertion is natural for a system matrix. -/
private theorem fixedEnvEmbedding_mul
    {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E]
    (e₀ : E) (A : Matrix S S ℂ) :
    fixedEnvEmbedding (S := S) e₀ * A =
      (A ⊗ₖ (1 : Matrix E E ℂ)) *
        fixedEnvEmbedding (S := S) e₀ := by
  ext se s
  rcases se with ⟨s', e⟩
  rw [mul_fixedEnvEmbedding_apply]
  by_cases he : e = e₀
  · subst e
    simp [fixedEnvEmbedding, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  · simp [fixedEnvEmbedding, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, he]

/-- Conjugating a block-coordinate dilation by a system unitary gives the
same supported isometry in physical coordinates. -/
private theorem physicalDilation_mul_fixedEnvEmbedding_mul_support
    {S E N : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E]
    (e₀ : E) (U_S : Matrix S S ℂ)
    (hU_S : U_S ∈ Matrix.unitaryGroup S ℂ)
    (Ublocks : Matrix (S × E) (S × E) ℂ)
    (J : Matrix S N ℂ) :
    let lift := U_S ⊗ₖ (1 : Matrix E E ℂ)
    let Uphysical := lift * Ublocks * star lift
    Uphysical * fixedEnvEmbedding (S := S) e₀ * (U_S * J) =
      lift * (Ublocks * fixedEnvEmbedding (S := S) e₀ * J) := by
  let lift := U_S ⊗ₖ (1 : Matrix E E ℂ)
  have hlift : lift ∈ Matrix.unitaryGroup (S × E) ℂ :=
    Matrix.kronecker_mem_unitary hU_S (Submonoid.one_mem _)
  have hlift_left : star lift * lift = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hlift
  dsimp only
  have hnatural := fixedEnvEmbedding_mul e₀ U_S
  calc
    ((U_S ⊗ₖ (1 : Matrix E E ℂ)) * Ublocks *
          star (U_S ⊗ₖ (1 : Matrix E E ℂ))) *
        fixedEnvEmbedding (S := S) e₀ * (U_S * J) =
      (U_S ⊗ₖ (1 : Matrix E E ℂ)) * Ublocks *
        (star (U_S ⊗ₖ (1 : Matrix E E ℂ)) *
          (fixedEnvEmbedding (S := S) e₀ * U_S)) * J := by
            simp only [Matrix.mul_assoc]
    _ = (U_S ⊗ₖ (1 : Matrix E E ℂ)) * Ublocks *
        (star (U_S ⊗ₖ (1 : Matrix E E ℂ)) *
          ((U_S ⊗ₖ (1 : Matrix E E ℂ)) *
            fixedEnvEmbedding (S := S) e₀)) * J := by rw [hnatural]
    _ = (U_S ⊗ₖ (1 : Matrix E E ℂ)) *
        (Ublocks * fixedEnvEmbedding (S := S) e₀ * J) := by
          change lift * Ublocks * (star lift * (lift *
            fixedEnvEmbedding (S := S) e₀)) * J =
            lift * (Ublocks * fixedEnvEmbedding (S := S) e₀ * J)
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star lift) lift]
          rw [hlift_left, Matrix.one_mul]

/-- Extend an isometry from a fixed pure environment input to a unitary on
the system and environment. -/
private theorem exists_unitary_mul_fixedEnvEmbedding_eq
    {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (e₀ : E) (V : Matrix (S × E) S ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix.unitaryGroup (S × E) ℂ,
      V = (U : Matrix (S × E) (S × E) ℂ) *
        fixedEnvEmbedding (S := S) e₀ := by
  apply Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
  rw [hV, fixedEnvEmbedding_conjTranspose_mul_self]

/-- A normalized rectangular Kraus family has a unitary Stinespring
extension from any fixed pure environment coordinate. -/
private theorem exists_unitary_stinespringV_mul_fixedEnvEmbedding_eq
    {S C : Type*} {r : ℕ}
    [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (c₀ : C) (k₀ : Fin r) (K : Fin r → Matrix (S × C) S ℂ)
    (hK : ∑ k, (K k)ᴴ * K k = (1 : Matrix S S ℂ)) :
    ∃ U : Matrix.unitaryGroup (S × (C × Fin r)) ℂ,
      Matrix.reindex (Equiv.prodAssoc S C (Fin r)) (Equiv.refl S)
          (stinespringV K) =
        (U : Matrix (S × (C × Fin r)) (S × (C × Fin r)) ℂ) *
          fixedEnvEmbedding (S := S) (c₀, k₀) := by
  let V : Matrix (S × (C × Fin r)) S ℂ :=
    Matrix.reindex (Equiv.prodAssoc S C (Fin r)) (Equiv.refl S)
      (stinespringV K)
  have hV : Vᴴ * V = 1 := by
    rw [show Vᴴ =
        Matrix.reindex (Equiv.refl S) (Equiv.prodAssoc S C (Fin r))
          (stinespringV K)ᴴ by
      exact Matrix.conjTranspose_reindex
        (Equiv.prodAssoc S C (Fin r)) (Equiv.refl S) (stinespringV K)]
    change
      (stinespringV K)ᴴ.submatrix id (Equiv.prodAssoc S C (Fin r)).symm *
          (stinespringV K).submatrix
            (Equiv.prodAssoc S C (Fin r)).symm id = 1
    rw [Matrix.submatrix_mul_equiv]
    exact (stinespringV_conjTranspose_mul K).trans hK
  exact exists_unitary_mul_fixedEnvEmbedding_eq (c₀, k₀) V hV

/-- Put a dependent direct sum of dilation sectors into ambient system and
environment coordinates. -/
def dilationBlockEquiv
    {I B E : Type*} {M D : I → Type*}
    (eB : ((i : I) × (M i × D i)) ≃ B) :
    ((i : I) × ((M i × E) × D i)) ≃ B × E :=
  (Equiv.sigmaCongrRight fun i =>
      ((Equiv.prodAssoc (M i) E (D i)).trans
        ((Equiv.refl (M i)).prodCongr (Equiv.prodComm E (D i)))).trans
          (Equiv.prodAssoc (M i) (D i) E).symm) |>.trans
    ((Equiv.sigmaProdDistrib (fun i => M i × D i) E).symm.trans
      (eB.prodCongr (Equiv.refl E)))

@[simp]
private theorem dilationBlockEquiv_apply
    {I B E : Type*} {M D : I → Type*}
    (eB : ((i : I) × (M i × D i)) ≃ B)
    (i : I) (m : M i) (e : E) (d : D i) :
    dilationBlockEquiv eB ⟨i, ((m, e), d)⟩ =
      (eB ⟨i, (m, d)⟩, e) := by
  rfl

/-- A dependent block diagonal of unitary matrices remains unitary after an
ambient reindexing. -/
private theorem reindex_blockDiagonal'_mem_unitary
    {I N : Type*} [Finite I] [DecidableEq I]
    {D : I → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    [Fintype N] [DecidableEq N]
    (e : ((i : I) × D i) ≃ N)
    (U : ∀ i, Matrix (D i) (D i) ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (D i) ℂ) :
    Matrix.reindex e e (Matrix.blockDiagonal' U) ∈
      Matrix.unitaryGroup N ℂ := by
  letI := Fintype.ofFinite I
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hstar :
      (Matrix.reindex e e (Matrix.blockDiagonal' U))ᴴ =
        Matrix.reindex e e (Matrix.blockDiagonal' U)ᴴ :=
    Matrix.conjTranspose_reindex e e (Matrix.blockDiagonal' U)
  rw [hstar]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.blockDiagonal' U) *
        (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.blockDiagonal' U)ᴴ = 1
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  have hblocks : (fun i => U i * (U i)ᴴ) = 1 := by
    funext i
    rw [show (U i)ᴴ = star (U i) from (Matrix.star_eq_conjTranspose _).symm]
    exact Matrix.mem_unitaryGroup_iff.mp (hU i)
  rw [hblocks, Matrix.blockDiagonal'_one]
  simp

/-- Transport a unitary from middle-system block coordinates to physical
middle-system coordinates. -/
private theorem physicalDilationUnitary_spec
    {B E : Type*} [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E]
    (U_B : Matrix B B ℂ)
    (hU_B : U_B ∈ Matrix.unitaryGroup B ℂ)
    (Ublocks : Matrix (B × E) (B × E) ℂ)
    (hUblocks : Ublocks ∈ Matrix.unitaryGroup (B × E) ℂ) :
    let lift := U_B ⊗ₖ (1 : Matrix E E ℂ)
    let Uphysical := lift * Ublocks * star lift
    Uphysical ∈ Matrix.unitaryGroup (B × E) ℂ ∧
      star lift * Uphysical * lift = Ublocks := by
  let lift := U_B ⊗ₖ (1 : Matrix E E ℂ)
  have hlift : lift ∈ Matrix.unitaryGroup (B × E) ℂ :=
    Matrix.kronecker_mem_unitary hU_B (Submonoid.one_mem _)
  have hlift_left : star lift * lift = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hlift
  have hlift_right : lift * star lift = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hlift
  have hstar : star lift ∈ Matrix.unitaryGroup (B × E) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [star_star] using hlift_left
  dsimp only
  constructor
  · exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ hlift hUblocks) hstar
  · change star lift * (lift * Ublocks * star lift) * lift = Ublocks
    calc
      star lift * (lift * Ublocks * star lift) * lift =
          (star lift * lift) * Ublocks * (star lift * lift) := by
            simp only [Matrix.mul_assoc]
      _ = Ublocks := by rw [hlift_left]; simp

/-- The Schrödinger isometry obtained by applying a system-environment
unitary to one fixed pure environment coordinate, with output regrouped as
`(system × recovered) × dilation`. -/
noncomputable def pureAncillaDilationIsometry
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ) :
    Matrix ((B × C) × R) B ℂ :=
  Matrix.reindex (Equiv.prodAssoc B C R).symm (Equiv.refl B)
    (U * fixedEnvEmbedding (S := B) (c₀, r₀))

/-- Recovery channel obtained from a physical unitary, a fixed pure
environment input, and a final trace over the dilation factor. -/
noncomputable def pureAncillaRecovery
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ) :
    Matrix B B ℂ →ₗ[ℂ] Matrix (B × C) (B × C) ℂ :=
  partialTraceRightLM ∘ₗ
    singleKrausMap (pureAncillaDilationIsometry c₀ r₀ U)

/-- A unitary pure-ancilla recovery is CPTP. -/
private theorem pureAncillaRecovery_isKrausCPTP
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (B × (C × R)) ℂ) :
    IsKrausCPTP (pureAncillaRecovery c₀ r₀ U) := by
  apply isKrausCPTP_comp
  · apply singleKrausMap_isKrausCPTP
    rw [pureAncillaDilationIsometry]
    have hUleft : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp hU
    have hJ := fixedEnvEmbedding_conjTranspose_mul_self
      (S := B) (c₀, r₀)
    rw [Matrix.conjTranspose_reindex]
    change
      (U * fixedEnvEmbedding (S := B) (c₀, r₀))ᴴ.submatrix
          id (Equiv.prodAssoc B C R) *
        (U * fixedEnvEmbedding (S := B) (c₀, r₀)).submatrix
          (Equiv.prodAssoc B C R) id = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
      Matrix.conjTranspose_mul]
    calc
      ((fixedEnvEmbedding (S := B) (c₀, r₀))ᴴ * Uᴴ) *
          (U * fixedEnvEmbedding (S := B) (c₀, r₀)) =
        (fixedEnvEmbedding (S := B) (c₀, r₀))ᴴ *
          ((Uᴴ * U) * fixedEnvEmbedding (S := B) (c₀, r₀)) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUleft, Matrix.one_mul, hJ]
  · exact partialTraceRightLM_isKrausCPTP

/-- Equality of dilation isometries after a support inclusion implies
agreement of their recovery channels on every supported input. -/
private theorem pureAncillaRecovery_eq_rectangularKrausMap_on_support
    {B C R S : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    [Fintype S]
    (c₀ : C) (r₀ : R)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ)
    (K : R → Matrix (B × C) B ℂ)
    (Z : Matrix B S ℂ)
    (hV : pureAncillaDilationIsometry c₀ r₀ U * Z =
      stinespringVGen K * Z) :
    ∀ X : Matrix S S ℂ,
      pureAncillaRecovery c₀ r₀ U (Z * X * Zᴴ) =
        rectangularKrausMap K (Z * X * Zᴴ) := by
  intro X
  rw [pureAncillaRecovery, LinearMap.comp_apply,
    singleKrausMap_apply]
  apply Matrix.ext
  intro bc bc'
  simp only [partialTraceRightLM, LinearMap.coe_mk, AddHom.coe_mk,
    partialTraceRight_apply, rectangularKrausMap, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hsandwich :
      pureAncillaDilationIsometry c₀ r₀ U *
          (Z * X * Zᴴ) *
            (pureAncillaDilationIsometry c₀ r₀ U)ᴴ =
        stinespringVGen K * (Z * X * Zᴴ) * (stinespringVGen K)ᴴ := by
    calc
      pureAncillaDilationIsometry c₀ r₀ U * (Z * X * Zᴴ) *
            (pureAncillaDilationIsometry c₀ r₀ U)ᴴ =
          (pureAncillaDilationIsometry c₀ r₀ U * Z) * X *
            (pureAncillaDilationIsometry c₀ r₀ U * Z)ᴴ := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (stinespringVGen K * Z) * X * (stinespringVGen K * Z)ᴴ := by
        rw [hV]
      _ = stinespringVGen K * (Z * X * Zᴴ) *
            (stinespringVGen K)ᴴ := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hentry := congrFun (congrFun hsandwich (bc, k)) (bc', k)
  simpa only [Matrix.mul_apply, stinespringVGen_apply,
    Matrix.conjTranspose_apply] using hentry

/-- Taking a bipartite block commutes with a rectangular sandwich on the
second tensor factor. -/
private theorem bipartiteBlock_right_rectangular_sandwich
    {A B N : Type*} [Fintype A] [DecidableEq A]
    [Fintype N]
    (X : Matrix (A × N) (A × N) ℂ) (Z : Matrix B N ℂ)
    (a a' : A) :
    bipartiteBlock
        (((1 : Matrix A A ℂ) ⊗ₖ Z) * X *
          ((1 : Matrix A A ℂ) ⊗ₖ Z)ᴴ) a a' =
      Z * bipartiteBlock X a a' * Zᴴ := by
  ext b b'
  simp only [bipartiteBlock_apply, Matrix.mul_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp

/-- Maps agreeing on every matrix supported by an isometry have equal
identity extensions on a bipartite matrix reconstructed from that support. -/
private theorem idTensorMap_eq_of_isometry_reconstruction
    {A B C N : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [Fintype N]
    (T₁ T₂ : Matrix B B ℂ →ₗ[ℂ] Matrix C C ℂ)
    (ρ : Matrix (A × B) (A × B) ℂ) (Z : Matrix B N ℂ)
    (hreconstruct :
      let W := (1 : Matrix A A ℂ) ⊗ₖ Z
      W * (Wᴴ * ρ * W) * Wᴴ = ρ)
    (hagree : ∀ X : Matrix N N ℂ,
      T₁ (Z * X * Zᴴ) = T₂ (Z * X * Zᴴ)) :
    idTensorMapLM (δ := A) T₁ ρ =
      idTensorMapLM (δ := A) T₂ ρ := by
  let W := (1 : Matrix A A ℂ) ⊗ₖ Z
  let ρsupport := Wᴴ * ρ * W
  have hblock : ∀ a a',
      bipartiteBlock ρ a a' =
        Z * bipartiteBlock ρsupport a a' * Zᴴ := by
    intro a a'
    rw [← hreconstruct]
    exact bipartiteBlock_right_rectangular_sandwich
      ρsupport Z a a'
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [idTensorMapLM_apply, idTensorMap_apply]
  rw [hblock]
  exact congrFun (congrFun
    (hagree (bipartiteBlock ρsupport a a')) c) c'

/-- A unitary change of coordinates on the support leg preserves the
ambient reconstruction identity. -/
private theorem supportReconstruction_mul_unitary
    {A B N : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [Fintype N] [DecidableEq N]
    (ρ : Matrix (A × B) (A × B) ℂ)
    (V : Matrix B N ℂ) (U : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ)
    (hV :
      let W := (1 : Matrix A A ℂ) ⊗ₖ V
      W * (Wᴴ * ρ * W) * Wᴴ = ρ) :
    let Z := V * U
    let W := (1 : Matrix A A ℂ) ⊗ₖ Z
    W * (Wᴴ * ρ * W) * Wᴴ = ρ := by
  let WV := (1 : Matrix A A ℂ) ⊗ₖ V
  let WU := (1 : Matrix A A ℂ) ⊗ₖ U
  let Z := V * U
  let WZ := (1 : Matrix A A ℂ) ⊗ₖ Z
  have hWZ : WZ = WV * WU := by
    simp only [WZ, WV, WU, Z, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  have hWUright : WU * WUᴴ = 1 := by
    have hUright : U * Uᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp hU
    simp only [WU, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hUright]
    exact Matrix.one_kronecker_one
  dsimp only
  rw [show (1 : Matrix A A ℂ) ⊗ₖ (V * U) = WZ by rfl, hWZ]
  simp only [Matrix.conjTranspose_mul]
  calc
    (WV * WU) * (WUᴴ * WVᴴ * ρ * (WV * WU)) *
          (WUᴴ * WVᴴ) =
        WV * (WU * WUᴴ) * (WVᴴ * ρ * WV) *
          (WU * WUᴴ) * WVᴴ := by
            simp only [Matrix.mul_assoc]
    _ = WV * (WVᴴ * ρ * WV) * WVᴴ := by
      rw [hWUright]
      simp
    _ = ρ := hV

/-- Entrywise supported-sector action of a dependent block dilation on a
fixed pure environment input. -/
private theorem blockDilation_fixedEnv_apply_support
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (L : Fin r → ∀ j : Fin K,
      Matrix (Fin (m j) × Fin dC) (Fin (m j)) ℂ)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (hUlocal : ∀ j,
      Matrix.reindex (Equiv.prodAssoc (Fin (m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (m j))) (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding (S := Fin (m j)) (c₀, k₀)) :
    let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
    let Ublocks := Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix (Fin (ambientRecoveredConditionalDim d s))
            (Fin (ambientRecoveredConditionalDim d s)) ℂ))
    ∀ (j : Fin K) (u : Fin (m j)) (v : Fin (d j))
      (c : Fin dC) (i : Fin r) (u' : Fin (m j)) (v' : Fin (d j)),
      (Ublocks * fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
          (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
          (eB ⟨Sum.inr j, (u', v')⟩) =
        L i j (u, c) u' *
          (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v v' := by
  classical
  dsimp only
  intro j u v c i u' v'
  rw [mul_fixedEnvEmbedding_apply]
  let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
  have hout :
      (eB ⟨Sum.inr j, (u, v)⟩, (c, i)) =
        eD ⟨Sum.inr j, ((u, (c, i)), v)⟩ := by rfl
  have hin :
      (eB ⟨Sum.inr j, (u', v')⟩, (c₀, k₀)) =
        eD ⟨Sum.inr j, ((u', (c₀, k₀)), v')⟩ := by rfl
  rw [hout, hin]
  dsimp only [eD]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  change
    Ulocal (Sum.inr j) (u, (c, i)) (u', (c₀, k₀)) *
        (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v v' =
      L i j (u, c) u' *
        (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v v'
  have hentry := congrFun (congrFun (hUlocal j) (u, (c, i)))
    u'
  have hlocal :
      Ulocal (Sum.inr j) (u, (c, i)) (u', (c₀, k₀)) =
        L i j (u, c) u' := by
    let Uj : Matrix (Fin (m j) × (Fin dC × Fin r))
        (Fin (m j) × (Fin dC × Fin r)) ℂ := by
      exact Ulocal (Sum.inr j)
    change Uj (u, (c, i)) (u', (c₀, k₀)) = L i j (u, c) u'
    rw [← mul_fixedEnvEmbedding_apply Uj (c₀, k₀) (u, (c, i)) u']
    simpa [Uj, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodAssoc, stinespringV_apply] using hentry.symm
  rw [hlocal]

/-- Different supported sectors do not mix under the dependent block
dilation. -/
private theorem blockDilation_fixedEnv_apply_support_ne
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    {j j' : Fin K} (hjj' : j ≠ j')
    (u : Fin (m j)) (v : Fin (d j)) (c : Fin dC) (i : Fin r)
    (u' : Fin (m j')) (v' : Fin (d j')) :
    let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
    let Ublocks := Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix (Fin (ambientRecoveredConditionalDim d s))
            (Fin (ambientRecoveredConditionalDim d s)) ℂ))
    (Ublocks * fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
        (eB ⟨Sum.inr j', (u', v')⟩) = 0 := by
  classical
  dsimp only
  rw [mul_fixedEnvEmbedding_apply]
  let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
  have hout :
      (eB ⟨Sum.inr j, (u, v)⟩, (c, i)) =
        eD ⟨Sum.inr j, ((u, (c, i)), v)⟩ := by rfl
  have hin :
      (eB ⟨Sum.inr j', (u', v')⟩, (c₀, k₀)) =
        eD ⟨Sum.inr j', ((u', (c₀, k₀)), v')⟩ := by rfl
  have houtinv :
      (dilationBlockEquiv (E := Fin dC × Fin r) eB).symm
          (eB ⟨Sum.inr j, (u, v)⟩, (c, i)) =
        ⟨Sum.inr j, ((u, (c, i)), v)⟩ := by
    rw [hout]
    exact Equiv.symm_apply_apply _ _
  have hininv :
      (dilationBlockEquiv (E := Fin dC × Fin r) eB).symm
          (eB ⟨Sum.inr j', (u', v')⟩, (c₀, k₀)) =
        ⟨Sum.inr j', ((u', (c₀, k₀)), v')⟩ := by
    rw [hin]
    exact Equiv.symm_apply_apply _ _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, houtinv, hininv]
  exact Matrix.blockDiagonal'_apply_ne _ _ _
    (fun h ↦ hjj' (Sum.inr.inj h))

/-- Complement rows do not receive a supported input under the dependent
block dilation. -/
private theorem blockDilation_fixedEnv_apply_complement_support
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (z₀ : Fin z)
    (u : Fin (ambientRecoveredCommonDim m (Sum.inl z₀)))
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inl z₀)))
    (c : Fin dC) (i : Fin r)
    (j : Fin K) (u' : Fin (m j)) (v' : Fin (d j)) :
    let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
    let Ublocks := Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix (Fin (ambientRecoveredConditionalDim d s))
            (Fin (ambientRecoveredConditionalDim d s)) ℂ))
    (Ublocks * fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inl z₀, (u, v)⟩, (c, i))
        (eB ⟨Sum.inr j, (u', v')⟩) = 0 := by
  classical
  dsimp only
  rw [mul_fixedEnvEmbedding_apply]
  let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
  have hout :
      (eB ⟨Sum.inl z₀, (u, v)⟩, (c, i)) =
        eD ⟨Sum.inl z₀, ((u, (c, i)), v)⟩ := by rfl
  have hin :
      (eB ⟨Sum.inr j, (u', v')⟩, (c₀, k₀)) =
        eD ⟨Sum.inr j, ((u', (c₀, k₀)), v')⟩ := by rfl
  have houtinv :
      (dilationBlockEquiv (E := Fin dC × Fin r) eB).symm
          (eB ⟨Sum.inl z₀, (u, v)⟩, (c, i)) =
        ⟨Sum.inl z₀, ((u, (c, i)), v)⟩ := by
    rw [hout]
    exact Equiv.symm_apply_apply _ _
  have hininv :
      (dilationBlockEquiv (E := Fin dC × Fin r) eB).symm
          (eB ⟨Sum.inr j, (u', v')⟩, (c₀, k₀)) =
        ⟨Sum.inr j, ((u', (c₀, k₀)), v')⟩ := by
    rw [hin]
    exact Equiv.symm_apply_apply _ _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, houtinv, hininv]
  exact Matrix.blockDiagonal'_apply_ne _ _ _ Sum.inl_ne_inr

/-- Each environment slice of the block dilation on the joint-support
inclusion is the corresponding adapted block Kraus operator. -/
private theorem blockDilation_slice_support
    {dB n K dC r : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (c₀ : Fin dC) (k₀ : Fin r)
    (C : Fin (dC * r) → ∀ j : Fin K,
      Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (L : Fin r → ∀ j : Fin K,
      Matrix (Fin (m j) × Fin dC) (Fin (m j)) ℂ)
    (hL : ∀ i j u c u', L i j (u, c) u' =
      C (finProdFinEquiv (c, i)) j u u')
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex (dB - n) K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (hUlocal : ∀ j,
      Matrix.reindex (Equiv.prodAssoc (Fin (m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (m j))) (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding (S := Fin (m j)) (c₀, k₀)) :
    let eB := recoveredAmbientMiddleBlockEquiv e₀ e
    let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
    let Ublocks := Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix (Fin (ambientRecoveredConditionalDim d s))
            (Fin (ambientRecoveredConditionalDim d s)) ℂ))
    ∀ c i,
      rightOutputSlice
          ((Ublocks * fixedEnvEmbedding (S := Fin dB) (c₀, k₀)) *
            ambientSupportEmbedding e₀) (c, i) =
        ambientSupportEmbedding e₀ *
          Matrix.reindex e e
            (Matrix.blockDiagonal' fun j ↦
              C (finProdFinEquiv (c, i)) j ⊗ₖ
                (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) := by
  classical
  dsimp only
  intro c i
  ext b x
  simp only [rightOutputSlice]
  rw [← (recoveredAmbientMiddleBlockEquiv e₀ e).apply_symm_apply b,
    ← e.apply_symm_apply x]
  generalize (recoveredAmbientMiddleBlockEquiv e₀ e).symm b = sb
  generalize e.symm x = sx
  rcases sb with ⟨s, u, v⟩
  rcases sx with ⟨j', u', v'⟩
  rcases s with z | j
  · have hcol :
        e₀ (Sum.inr (e ⟨j', (u', v')⟩)) =
          recoveredAmbientMiddleBlockEquiv e₀ e
            ⟨Sum.inr j', (u', v')⟩ := rfl
    have hrow :
        recoveredAmbientMiddleBlockEquiv e₀ e
            ⟨Sum.inl z, (u, v)⟩ = e₀ (Sum.inl z) := by
      change Fin 1 at u v
      fin_cases u
      fin_cases v
      rfl
    rw [mul_ambientSupportEmbedding_apply]
    rw [hcol]
    rw [blockDilation_fixedEnv_apply_complement_support
      (recoveredAmbientMiddleBlockEquiv e₀ e) c₀ k₀ Ulocal
      z u v c i j' u' v']
    rw [hrow]
    exact (ambientSupportEmbedding_mul_apply_complement e₀ _ z _).symm
  · change Fin (m j) at u
    change Fin (d j) at v
    by_cases hj : j = j'
    · subst j'
      rw [mul_ambientSupportEmbedding_apply]
      have hcol :
          e₀ (Sum.inr (e ⟨j, (u', v')⟩)) =
            recoveredAmbientMiddleBlockEquiv e₀ e
              ⟨Sum.inr j, (u', v')⟩ := rfl
      rw [hcol]
      rw [blockDilation_fixedEnv_apply_support
        (recoveredAmbientMiddleBlockEquiv e₀ e) c₀ k₀ L Ulocal hUlocal
        j u v c i u' v']
      have hrow :
          recoveredAmbientMiddleBlockEquiv e₀ e
              ⟨Sum.inr j, (u, v)⟩ =
            e₀ (Sum.inr (e ⟨j, (u, v)⟩)) := rfl
      rw [hrow, ambientSupportEmbedding_mul_apply_support]
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq,
        Matrix.kroneckerMap_apply]
      rw [hL]
    · rw [mul_ambientSupportEmbedding_apply]
      have hcol :
          e₀ (Sum.inr (e ⟨j', (u', v')⟩)) =
            recoveredAmbientMiddleBlockEquiv e₀ e
              ⟨Sum.inr j', (u', v')⟩ := rfl
      rw [hcol]
      rw [blockDilation_fixedEnv_apply_support_ne
        (recoveredAmbientMiddleBlockEquiv e₀ e) c₀ k₀ Ulocal
        hj u v c i u' v']
      have hrow :
          recoveredAmbientMiddleBlockEquiv e₀ e
              ⟨Sum.inr j, (u, v)⟩ =
            e₀ (Sum.inr (e ⟨j, (u, v)⟩)) := rfl
      rw [hrow, ambientSupportEmbedding_mul_apply_support]
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply]
      exact (Matrix.blockDiagonal'_apply_ne
        (fun j ↦ C (finProdFinEquiv (c, i)) j ⊗ₖ
          (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))
        (u, v) (u', v') hj).symm

end Matrix

open Matrix

namespace Matrix

variable {dA dB dC : ℕ}

/-- Source-specific square slices and local rectangular Kraus blocks for the
HJPW recovery operation. -/
private theorem exists_recoveredSliceSectorBlocks
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    ∃ (r : ℕ)
      (R : Fin r → Matrix (Fin dB × Fin dC) (Fin dB) ℂ)
      (S : Fin (dC * r) → Matrix (Fin dB) (Fin dB) ℂ)
      (C : Fin (dC * r) → ∀ j : Fin F.jointSupport.K,
        Matrix (Fin (F.jointSupport.m j)) (Fin (F.jointSupport.m j)) ℂ)
      (L : Fin r → ∀ j : Fin F.jointSupport.K,
        Matrix (Fin (F.jointSupport.m j) × Fin dC)
          (Fin (F.jointSupport.m j)) ℂ),
      (∀ X, partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1) X =
        rectangularKrausMap R X) ∧
      (∑ i, (R i)ᴴ * R i = (1 : Matrix (Fin dB) (Fin dB) ℂ)) ∧
      (∀ k, S k = rightOutputSlice
        (R (finProdFinEquiv.symm k).2) (finProdFinEquiv.symm k).1) ∧
      (∀ X, Kraus.map S X = recoveredMiddleChannel ρ_ABC hρ_dm.1 X) ∧
      (∀ k, S k * F.jointSupport.V =
        F.jointSupport.V *
          (Kraus.supportCompressedKraus F.jointSupport.V S) k) ∧
      (∀ k,
        Matrix.reindex F.jointSupport.e.symm F.jointSupport.e.symm
            (star F.jointSupport.U *
              (Kraus.supportCompressedKraus F.jointSupport.V S) k *
                F.jointSupport.U) =
          Matrix.blockDiagonal' fun j ↦
            C k j ⊗ₖ
              (1 : Matrix (Fin (F.jointSupport.d j))
                (Fin (F.jointSupport.d j)) ℂ)) ∧
      (∀ k, S k * (F.jointSupport.V * F.jointSupport.U) =
        (F.jointSupport.V * F.jointSupport.U) *
          Matrix.reindex F.jointSupport.e F.jointSupport.e
            (Matrix.blockDiagonal' fun j ↦
              C k j ⊗ₖ
                (1 : Matrix (Fin (F.jointSupport.d j))
                  (Fin (F.jointSupport.d j)) ℂ))) ∧
      (∀ j, Kraus.IsTP (fun k ↦ C k j)) ∧
      (∀ i j u c u', L i j (u, c) u' =
        C (finProdFinEquiv (c, i)) j u u') ∧
      (∀ j, ∑ i, (L i j)ᴴ * L i j =
        (1 : Matrix (Fin (F.jointSupport.m j))
          (Fin (F.jointSupport.m j)) ℂ)) ∧
      ∀ j,
        partialTraceRight
            (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
          F.jointSupport.σ j := by
  classical
  obtain ⟨r, R, hRmap, hRtp⟩ :=
    partialTraceRightPetzChannel_traceA_ABC_isKrausCPTP ρ_ABC hρ_dm
  let S : Fin (dC * r) → Matrix (Fin dB) (Fin dB) ℂ :=
    fun k ↦ rightOutputSlice
      (R (finProdFinEquiv.symm k).2) (finProdFinEquiv.symm k).1
  have hSmap :
      ∀ X, Kraus.map S X = recoveredMiddleChannel ρ_ABC hρ_dm.1 X := by
    intro X
    rw [recoveredMiddleChannel, LinearMap.comp_apply]
    calc
      rectangularKrausMap S X =
          rectangularKrausMap
            (fun p : Fin dC × Fin r ↦ rightOutputSlice (R p.2) p.1) X :=
        DFunLike.congr_fun
          (rectangularKrausMap_equiv finProdFinEquiv
            (fun p : Fin dC × Fin r ↦ rightOutputSlice (R p.2) p.1)) X
      _ = partialTraceRight (rectangularKrausMap R X) :=
        (partialTraceRight_rectangularKrausMap_eq_slices R X).symm
      _ = partialTraceRight
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1) X) :=
        congrArg partialTraceRight (hRmap X).symm
  have hStp : Kraus.IsTP S := by
    apply kraus_sum_conjTranspose_mul_of_tp S
      (recoveredMiddleChannel ρ_ABC hρ_dm.1)
    · exact fun X ↦ (hSmap X).symm
    · exact
        (recoveredMiddleChannel_isKrausCPTP ρ_ABC hρ_dm).trace_map
  let G : Kraus.PreservingKrausFamily
      (recoveredConditionalState (traceC_ABC ρ_ABC)) :=
    { numKraus := dC * r
      Kfam := S
      isPreserving := ⟨hStp, fun x ↦ by
        rw [hSmap]
        exact recoveredMiddleChannel_recoveredConditionalState
          ρ_ABC hρ_dm hSSA x⟩ }
  have hSsupport : ∀ k, S k * F.jointSupport.V =
      F.jointSupport.V *
        (Kraus.supportCompressedKraus F.jointSupport.V S) k := by
    let μ := recoveredConditionalState (traceC_ABC ρ_ABC)
    let hμbar := Kraus.commonAverage_posSemidef μ
      (recoveredConditionalState_posSemidef
        (SSAPosDef.traceC_ABC_posSemidef hρ_dm.1))
    have hInv : ∀ k,
        (1 - hμbar.supportProj) * S k * hμbar.supportProj = 0 := by
      simpa only [Kraus.stationaryProj] using
        (Kraus.lowerZero_of_posSemidef_fixedPoint S
          (Kraus.commonAverage μ) hμbar G.map_commonAverage).2
    have hQV : hμbar.supportProj * F.jointSupport.V =
        F.jointSupport.V := by
      rw [← F.jointSupport.V_range]
      simp [Matrix.mul_assoc, F.jointSupport.V_isometry]
    intro k
    have hQKV : hμbar.supportProj * S k * F.jointSupport.V =
        S k * F.jointSupport.V := by
      have h := hInv k
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
      calc
        hμbar.supportProj * S k * F.jointSupport.V =
            hμbar.supportProj * S k *
              (hμbar.supportProj * F.jointSupport.V) := by rw [hQV]
        _ = (hμbar.supportProj * S k * hμbar.supportProj) *
              F.jointSupport.V := by simp only [Matrix.mul_assoc]
        _ = (S k * hμbar.supportProj) * F.jointSupport.V := by rw [← h]
        _ = S k * F.jointSupport.V := by rw [Matrix.mul_assoc, hQV]
    rw [← hQKV, ← F.jointSupport.V_range]
    simp only [Kraus.supportCompressedKraus, Matrix.mul_assoc]
  obtain ⟨hGsupport, _⟩ :=
    F.jointSupport.preserving_support_action G
  let Gsupport : Kraus.PreservingKrausFamily
      (Kraus.supportCompressedFamily F.jointSupport.V
        (recoveredConditionalState (traceC_ABC ρ_ABC))) :=
    { numKraus := dC * r
      Kfam := Kraus.supportCompressedKraus F.jointSupport.V S
      isPreserving := hGsupport }
  obtain ⟨C, hCblock, hCtp, hCfix, _⟩ :=
    F.jointSupport.preserving_block_action Gsupport
  have hSblock : ∀ k, S k * (F.jointSupport.V * F.jointSupport.U) =
      (F.jointSupport.V * F.jointSupport.U) *
        Matrix.reindex F.jointSupport.e F.jointSupport.e
          (Matrix.blockDiagonal' fun j ↦
            C k j ⊗ₖ
              (1 : Matrix (Fin (F.jointSupport.d j))
                (Fin (F.jointSupport.d j)) ℂ)) := by
    intro k
    let Bk := Matrix.reindex F.jointSupport.e F.jointSupport.e
      (Matrix.blockDiagonal' fun j ↦
        C k j ⊗ₖ
          (1 : Matrix (Fin (F.jointSupport.d j))
            (Fin (F.jointSupport.d j)) ℂ))
    have hcoord :
        star F.jointSupport.U *
            (Kraus.supportCompressedKraus F.jointSupport.V S) k *
              F.jointSupport.U = Bk := by
      have h := congrArg
        (Matrix.reindex F.jointSupport.e F.jointSupport.e) (hCblock k)
      simpa [Bk] using h
    have hUright : F.jointSupport.U * star F.jointSupport.U = 1 :=
      Matrix.mem_unitaryGroup_iff.mp F.jointSupport.U_unitary
    calc
      S k * (F.jointSupport.V * F.jointSupport.U) =
          (S k * F.jointSupport.V) * F.jointSupport.U := by
            simp only [Matrix.mul_assoc]
      _ = (F.jointSupport.V *
            (Kraus.supportCompressedKraus F.jointSupport.V S) k) *
            F.jointSupport.U := by rw [hSsupport k]
      _ = F.jointSupport.V *
          (F.jointSupport.U * Bk) := by
            rw [← hcoord]
            simp only [Matrix.mul_assoc]
            apply congrArg (fun X ↦ F.jointSupport.V * X)
            calc
              (Kraus.supportCompressedKraus F.jointSupport.V S) k *
                    F.jointSupport.U =
                  (F.jointSupport.U * star F.jointSupport.U) *
                    ((Kraus.supportCompressedKraus
                      F.jointSupport.V S) k * F.jointSupport.U) := by
                        rw [hUright, Matrix.one_mul]
              _ = F.jointSupport.U *
                  (star F.jointSupport.U *
                    ((Kraus.supportCompressedKraus
                      F.jointSupport.V S) k * F.jointSupport.U)) := by
                        simp only [Matrix.mul_assoc]
      _ = (F.jointSupport.V * F.jointSupport.U) * Bk := by
        simp only [Matrix.mul_assoc]
  let L : Fin r → ∀ j : Fin F.jointSupport.K,
      Matrix (Fin (F.jointSupport.m j) × Fin dC)
        (Fin (F.jointSupport.m j)) ℂ :=
    fun i j uc u' ↦ C (finProdFinEquiv (uc.2, i)) j uc.1 u'
  have hLtp : ∀ j, ∑ i, (L i j)ᴴ * L i j =
      (1 : Matrix (Fin (F.jointSupport.m j))
        (Fin (F.jointSupport.m j)) ℂ) := by
    intro j
    have hCtpj := hCtp j
    unfold Kraus.IsTP at hCtpj
    ext u u'
    have hentry := congrFun (congrFun hCtpj u) u'
    simp only [Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply] at hentry ⊢
    rw [← hentry]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Fintype.sum_prod_type, L]
    calc
      (∑ i : Fin r, ∑ v : Fin (F.jointSupport.m j), ∑ c : Fin dC,
          star (C (finProdFinEquiv (c, i)) j v u) *
            C (finProdFinEquiv (c, i)) j v u') =
          ∑ i : Fin r, ∑ c : Fin dC, ∑ v : Fin (F.jointSupport.m j),
            star (C (finProdFinEquiv (c, i)) j v u) *
              C (finProdFinEquiv (c, i)) j v u' := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ c : Fin dC, ∑ i : Fin r, ∑ v : Fin (F.jointSupport.m j),
            star (C (finProdFinEquiv (c, i)) j v u) *
              C (finProdFinEquiv (c, i)) j v u' :=
        Finset.sum_comm
  have hLfix : ∀ j,
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
        F.jointSupport.σ j := by
    intro j
    let A : Fin dC × Fin r →
        Matrix (Fin (F.jointSupport.m j))
          (Fin (F.jointSupport.m j)) ℂ :=
      fun p ↦ C (finProdFinEquiv p) j
    have hrel :
        (fun k ↦ A (finProdFinEquiv.symm k)) = (fun k ↦ C k j) := by
      funext k
      simp only [A, Equiv.apply_symm_apply]
    have hslices :
        (fun p : Fin dC × Fin r ↦ rightOutputSlice (L p.2 j) p.1) = A := by
      funext p
      ext u u'
      rfl
    calc
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
          rectangularKrausMap
              (fun p : Fin dC × Fin r ↦
                rightOutputSlice (L p.2 j) p.1)
              (F.jointSupport.σ j) :=
        partialTraceRight_rectangularKrausMap_eq_slices
          (fun i ↦ L i j) (F.jointSupport.σ j)
      _ = rectangularKrausMap A (F.jointSupport.σ j) := by
        rw [hslices]
      _ = rectangularKrausMap
          (fun k ↦ A (finProdFinEquiv.symm k))
          (F.jointSupport.σ j) := by
        exact DFunLike.congr_fun
          (rectangularKrausMap_equiv finProdFinEquiv A).symm
          (F.jointSupport.σ j)
      _ = Kraus.map (fun k ↦ C k j) (F.jointSupport.σ j) := by
        rw [hrel]
        rfl
      _ = F.jointSupport.σ j := hCfix j
  refine ⟨r, R, S, C, L, hRmap, hRtp, ?_, hSmap, hSsupport,
    ?_, hSblock, hCtp, ?_, hLtp, hLfix⟩
  · intro k
    rfl
  · intro k
    exact hCblock k
  · intro i j u c u'
    rfl

/-- Ambient block-coordinate and physical-unitary data for the HJPW recovery
dilation.

`U_BCE_blocks` is the literal direct-sum unitary in the ambient tensor
coordinates.  `U_BCE_physical` is its conjugate in the original middle-system
coordinates.  The chosen pure-ancilla recovery agrees with the Petz channel
on inputs supported by `jointSupport.V * jointSupport.U` and satisfies the
exact recovery identity, but no equality is asserted on the complementary
ambient sector.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560; Appendix A, Theorem 10, Property 2, lines 791--800;
the equivalence 2 iff 2', lines 808--823; and the operation-level proof
of 2', lines 853--882.  This structure records one chosen pure-ancilla
unitary, not every unitary associated with the operation. -/
structure RecoveredConditionalDilationBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) where
  r : ℕ
  c₀ : Fin dC
  k₀ : Fin r
  R : Fin r → Matrix (Fin dB × Fin dC) (Fin dB) ℂ
  L : Fin r → ∀ j : Fin F.jointSupport.K,
    Matrix (Fin (F.jointSupport.m j) × Fin dC)
      (Fin (F.jointSupport.m j)) ℂ
  Ulocal : ∀ s : AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K,
    Matrix
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r))
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ
  U_BCE_blocks : Matrix (Fin dB × (Fin dC × Fin r))
    (Fin dB × (Fin dC × Fin r)) ℂ
  U_BCE_physical : Matrix (Fin dB × (Fin dC × Fin r))
    (Fin dB × (Fin dC × Fin r)) ℂ
  petz_kraus :
    ∀ X, partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
        (traceLeftA_posSemidef hρ_dm.1) X =
      rectangularKrausMap R X
  sector_tp :
    ∀ j, ∑ i, (L i j)ᴴ * L i j =
      (1 : Matrix (Fin (F.jointSupport.m j))
        (Fin (F.jointSupport.m j)) ℂ)
  sector_state_fixed :
    ∀ j,
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
        F.jointSupport.σ j
  complement_local_identity :
    ∀ z : Fin (dB - F.jointSupport.n), Ulocal (Sum.inl z) = 1
  sector_pure_ancilla_extension :
    ∀ j,
      Matrix.reindex
          (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (F.jointSupport.m j)))
          (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding
            (S := Fin (F.jointSupport.m j)) (c₀, k₀)
  local_unitary :
    ∀ s, Ulocal s ∈ Matrix.unitaryGroup
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ
  block_coordinate_unitary_eq :
    U_BCE_blocks =
      Matrix.reindex
        (dilationBlockEquiv
          (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e))
        (dilationBlockEquiv
          (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e))
        (Matrix.blockDiagonal' fun s ↦
          Ulocal s ⊗ₖ
            (1 : Matrix
              (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
              (Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ))
  block_coordinate_unitary :
    U_BCE_blocks ∈ Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ
  physical_unitary_eq :
    U_BCE_physical =
      (F.U_B ⊗ₖ (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) *
        U_BCE_blocks *
        star (F.U_B ⊗ₖ
          (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ))
  physical_unitary :
    U_BCE_physical ∈ Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ
  inverse_coordinate_eq :
    star (F.U_B ⊗ₖ
        (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) *
        U_BCE_physical *
        (F.U_B ⊗ₖ
          (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) =
      U_BCE_blocks
  dilation_isometry_support :
    pureAncillaDilationIsometry c₀ k₀ U_BCE_physical *
        (F.jointSupport.V * F.jointSupport.U) =
      stinespringV R * (F.jointSupport.V * F.jointSupport.U)
  chosen_recovery_cptp :
    IsKrausCPTP (pureAncillaRecovery c₀ k₀ U_BCE_physical)
  recovery_agrees_on_support :
    ∀ X : Matrix (Fin F.jointSupport.n) (Fin F.jointSupport.n) ℂ,
      pureAncillaRecovery c₀ k₀ U_BCE_physical
          ((F.jointSupport.V * F.jointSupport.U) * X *
            (F.jointSupport.V * F.jointSupport.U)ᴴ) =
        partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1)
          ((F.jointSupport.V * F.jointSupport.U) * X *
            (F.jointSupport.V * F.jointSupport.U)ᴴ)
  recovery_eq11 :
    idTensorMapLM (δ := Fin dA)
        (pureAncillaRecovery c₀ k₀ U_BCE_physical)
        (traceC_ABC ρ_ABC) =
      ρ_ABC

/-- The recovered state on one supported common-factor sector together with
the output subsystem.

Its common-factor, or first-factor, marginal is the original common-factor
state; no state is assigned to an ambient complementary sector.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
noncomputable def RecoveredConditionalDilationBlockForm.recoveredSectorState
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    Matrix (Fin (F.jointSupport.m j) × Fin dC)
      (Fin (F.jointSupport.m j) × Fin dC) ℂ :=
  rectangularKrausMap (fun i ↦ D.L i j) (F.jointSupport.σ j)

/-- A recovered supported-sector state is positive semidefinite.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem RecoveredConditionalDilationBlockForm.recoveredSectorState_posSemidef
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    (D.recoveredSectorState j).PosSemidef := by
  exact (rectangularKrausMap_isKrausCPTP
    (fun i ↦ D.L i j) (D.sector_tp j)).map_posSemidef
      (F.jointSupport.σ_pos j)

/-- A recovered supported-sector state has trace one.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem RecoveredConditionalDilationBlockForm.recoveredSectorState_trace
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    (D.recoveredSectorState j).trace = 1 := by
  rw [RecoveredConditionalDilationBlockForm.recoveredSectorState,
    (rectangularKrausMap_isKrausCPTP
      (fun i ↦ D.L i j) (D.sector_tp j)).trace_map,
    F.jointSupport.σ_trace]

/-- The common-factor, or first-factor, marginal of a recovered supported-sector
state is the original common-factor state.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem
    RecoveredConditionalDilationBlockForm.partialTraceRight_recoveredSectorState
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    partialTraceRight (D.recoveredSectorState j) =
      F.jointSupport.σ j :=
  D.sector_state_fixed j

/-- At equality in strong subadditivity, the HJPW recovery has a
block-coordinate dilation of equation (15), with a corresponding physical
unitary and an exact realization of equation (11).

The literal block-coordinate unitary and its physical conjugate are recorded
separately.  Agreement with the Petz channel is asserted exactly on supported
inputs, with no complementary-sector equality claim.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560; Appendix A, Theorem 10, Property 2, lines 791--800;
the equivalence 2 iff 2', lines 808--823; and the operation-level proof
of 2', lines 853--882.  The theorem constructs one chosen pure-ancilla
unitary, not every associated unitary. -/
theorem exists_recoveredDilationBlockUnitary
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    Nonempty (RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) := by
  classical
  obtain ⟨r, R, S, C, L, hRmap, hRtp, hS, hSmap, hSsupport, hCblock,
      hSblock, hCtp, hL, hLtp, hLfix⟩ :=
    exists_recoveredSliceSectorBlocks ρ_ABC hρ_dm hSSA F
  have hBne : NeZero dB := by
    refine ⟨fun h ↦ ?_⟩
    subst dB
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρ_dm
    exact zero_ne_one hρ_dm.2
  have hCne : NeZero dC := by
    refine ⟨fun h ↦ ?_⟩
    subst dC
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρ_dm
    exact zero_ne_one hρ_dm.2
  have hrne : NeZero r := by
    refine ⟨fun hr ↦ ?_⟩
    subst r
    have b : Fin dB := ⟨0, Nat.pos_of_ne_zero (NeZero.ne dB)⟩
    have hentry := congrFun (congrFun hRtp b) b
    simp at hentry
  let c₀ : Fin dC := ⟨0, Nat.pos_of_ne_zero (NeZero.ne dC)⟩
  let k₀ : Fin r := ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
  have hUsector : ∀ j : Fin F.jointSupport.K,
      ∃ U : Matrix.unitaryGroup
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ,
        Matrix.reindex
            (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
            (Equiv.refl (Fin (F.jointSupport.m j)))
            (stinespringV (fun i ↦ L i j)) =
          (U : Matrix
            (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
            (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ) *
            fixedEnvEmbedding
              (S := Fin (F.jointSupport.m j)) (c₀, k₀) := by
    intro j
    exact exists_unitary_stinespringV_mul_fixedEnvEmbedding_eq
      c₀ k₀ (fun i ↦ L i j) (hLtp j)
  choose Us hUs using hUsector
  let Ulocal : ∀ s : AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K,
      Matrix
        (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
          (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
          (Fin dC × Fin r)) ℂ
    | Sum.inl _ => 1
    | Sum.inr j => by
        change Matrix
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ
        exact (Us j : Matrix
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ)
  have hUlocal : ∀ s, Ulocal s ∈ Matrix.unitaryGroup
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ := by
    intro s
    rcases s with z | j
    · exact Submonoid.one_mem _
    · convert (Us j).property using 1 <;> rfl
  let eD := dilationBlockEquiv
    (E := Fin dC × Fin r)
    (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e)
  let U_BCE : Matrix (Fin dB × (Fin dC × Fin r))
      (Fin dB × (Fin dC × Fin r)) ℂ :=
    Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix
            (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
            (Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ))
  have hUblocks : ∀ s,
      Ulocal s ⊗ₖ
          (1 : Matrix
            (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
            (Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ) ∈
        Matrix.unitaryGroup
          ((Fin (ambientRecoveredCommonDim F.jointSupport.m s) ×
              (Fin dC × Fin r)) ×
            Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ := by
    intro s
    exact Matrix.kronecker_mem_unitary (hUlocal s) (Submonoid.one_mem _)
  have hUBCE : U_BCE ∈
      Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ :=
    reindex_blockDiagonal'_mem_unitary eD _ hUblocks
  let lift := F.U_B ⊗ₖ
    (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)
  let U_BCE_physical : Matrix (Fin dB × (Fin dC × Fin r))
      (Fin dB × (Fin dC × Fin r)) ℂ :=
    lift * U_BCE * star lift
  obtain ⟨hUBCEphysical, hUBCEinverse⟩ :=
    physicalDilationUnitary_spec F.U_B F.U_B_unitary U_BCE hUBCE
  have hUlocalStinespring : ∀ j,
      Matrix.reindex
          (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (F.jointSupport.m j)))
          (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding
            (S := Fin (F.jointSupport.m j)) (c₀, k₀) := by
    intro j
    simpa [Ulocal, ambientRecoveredCommonDim] using hUs j
  let J := ambientSupportEmbedding F.e₀
  let Z := F.jointSupport.V * F.jointSupport.U
  have hblockSlices := blockDilation_slice_support F.e₀ F.jointSupport.e
    c₀ k₀ C L hL Ulocal hUlocalStinespring
  have hcoordinate :
      lift * (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J) =
        Matrix.reindex
          (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
          (Equiv.refl (Fin F.jointSupport.n))
          (stinespringV R * Z) := by
    apply Matrix.ext
    rintro ⟨b, ⟨c, i⟩⟩ x
    let Bk := Matrix.reindex F.jointSupport.e F.jointSupport.e
      (Matrix.blockDiagonal' fun j ↦
        C (finProdFinEquiv (c, i)) j ⊗ₖ
          (1 : Matrix (Fin (F.jointSupport.d j))
            (Fin (F.jointSupport.d j)) ℂ))
    have hslices :
        rightOutputSlice
            (lift *
              (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J))
            (c, i) =
          rightOutputSlice
            (Matrix.reindex
              (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
              (Equiv.refl (Fin F.jointSupport.n))
              (stinespringV R * Z)) (c, i) := by
      calc
        rightOutputSlice
            (lift *
              (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J))
            (c, i) =
          F.U_B * rightOutputSlice
            (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J)
            (c, i) := by
              exact rightOutputSlice_kronecker_one_mul F.U_B _ (c, i)
        _ = F.U_B * (J * Bk) := by
          apply congrArg (fun X ↦ F.U_B * X)
          simpa [U_BCE, eD, J, Bk] using hblockSlices c i
        _ = (F.U_B * J) * Bk := by simp only [Matrix.mul_assoc]
        _ = Z * Bk := by
          rw [show Z = F.U_B * J by
            simpa [Z, J] using
              F.ambient_support_isometry]
        _ = S (finProdFinEquiv (c, i)) * Z :=
          (hSblock (finProdFinEquiv (c, i))).symm
        _ = rightOutputSlice (R i) c * Z := by
          rw [hS (finProdFinEquiv (c, i))]
          simp only [Equiv.symm_apply_apply]
        _ = rightOutputSlice
            (Matrix.reindex
              (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
              (Equiv.refl (Fin F.jointSupport.n))
              (stinespringV R * Z)) (c, i) :=
          (rightOutputSlice_reindex_stinespringV_mul R Z c i).symm
    exact congrFun (congrFun hslices b) x
  have hphysicalCoordinate :
      U_BCE_physical * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * Z =
        Matrix.reindex
          (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
          (Equiv.refl (Fin F.jointSupport.n))
          (stinespringV R * Z) := by
    calc
      U_BCE_physical * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * Z =
          lift * (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J) := by
        rw [show Z = F.U_B * J by
          simpa [Z, J] using
            F.ambient_support_isometry]
        exact physicalDilation_mul_fixedEnvEmbedding_mul_support
          (c₀, k₀) F.U_B F.U_B_unitary U_BCE J
      _ = _ := hcoordinate
  have hIsometry :
      pureAncillaDilationIsometry c₀ k₀ U_BCE_physical * Z =
        stinespringV R * Z := by
    ext ⟨⟨b, c⟩, i⟩ x
    have hentry := congrFun (congrFun hphysicalCoordinate (b, (c, i))) x
    simpa [pureAncillaDilationIsometry, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.prodAssoc, Matrix.mul_apply] using hentry
  have hAgree :
      ∀ X : Matrix (Fin F.jointSupport.n) (Fin F.jointSupport.n) ℂ,
        pureAncillaRecovery c₀ k₀ U_BCE_physical (Z * X * Zᴴ) =
          partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1) (Z * X * Zᴴ) := by
    intro X
    exact (pureAncillaRecovery_eq_rectangularKrausMap_on_support
      c₀ k₀ U_BCE_physical R Z hIsometry X).trans
        (hRmap (Z * X * Zᴴ)).symm
  have hReconstruct :
      let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z
      W * (Wᴴ * traceC_ABC ρ_ABC * W) * Wᴴ =
        traceC_ABC ρ_ABC := by
    simpa only [Z] using supportReconstruction_mul_unitary
      (traceC_ABC ρ_ABC) F.jointSupport.V F.jointSupport.U
        F.jointSupport.U_unitary F.jointSupport.ambient_reconstruction
  have hChosenEqPetz :
      idTensorMapLM (δ := Fin dA)
          (pureAncillaRecovery c₀ k₀ U_BCE_physical)
          (traceC_ABC ρ_ABC) =
        idTensorMapLM (δ := Fin dA)
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1))
          (traceC_ABC ρ_ABC) :=
    idTensorMap_eq_of_isometry_reconstruction
      (pureAncillaRecovery c₀ k₀ U_BCE_physical)
      (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
        (traceLeftA_posSemidef hρ_dm.1))
      (traceC_ABC ρ_ABC) Z hReconstruct hAgree
  have hEq11 :
      idTensorMapLM (δ := Fin dA)
          (pureAncillaRecovery c₀ k₀ U_BCE_physical)
          (traceC_ABC ρ_ABC) =
        ρ_ABC := by
    calc
      _ = idTensorMapLM (δ := Fin dA)
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1))
          (traceC_ABC ρ_ABC) := hChosenEqPetz
      _ = ρ_ABC :=
        idTensor_partialTraceRightPetzChannel_traceC_ABC_eq_of_isSSAEquality
          ρ_ABC hρ_dm hSSA
  refine ⟨{
    r := r
    c₀ := c₀
    k₀ := k₀
    R := R
    L := L
    Ulocal := Ulocal
    U_BCE_blocks := U_BCE
    U_BCE_physical := U_BCE_physical
    petz_kraus := hRmap
    sector_tp := hLtp
    sector_state_fixed := hLfix
    complement_local_identity := ?_
    sector_pure_ancilla_extension := hUlocalStinespring
    local_unitary := hUlocal
    block_coordinate_unitary_eq := rfl
    block_coordinate_unitary := hUBCE
    physical_unitary_eq := rfl
    physical_unitary := hUBCEphysical
    inverse_coordinate_eq := hUBCEinverse
    dilation_isometry_support := hIsometry
    chosen_recovery_cptp :=
      pureAncillaRecovery_isKrausCPTP
        c₀ k₀ U_BCE_physical hUBCEphysical
    recovery_agrees_on_support := ?_
    recovery_eq11 := hEq11 }⟩
  · intro z
    rfl
  · simpa only [Z] using hAgree

end Matrix
