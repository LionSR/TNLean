/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixGramUnitary
import TNLean.Channel.KoashiImoto.RecoveredConditionalBipartiteBlockForm

/-!
# Ambient recovered bipartite block coordinates

This file extends the recovered bipartite block form from the minimum joint
support to the whole middle subsystem.  Each basis direction in the orthogonal
complement is represented by a one-dimensional tensor sector with zero
unnormalized conditional factor.

This is the ambient decomposition and bipartite marginal identity in HJPW,
arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(14), lines 493--502.

**Convention (factor order):** TNLean orders each middle-system summand as
the common density factor followed by the conditional-state-dependent factor,
opposite to HJPW.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

variable {dA dB dC n K : ℕ}

/-- The ambient sector index consists of one sector for each complementary
basis direction, followed by the joint-support sectors.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (13),
lines 493--496. -/
abbrev AmbientRecoveredBlockIndex (z K : ℕ) := Fin z ⊕ Fin K

/-- The common-factor dimension of an ambient recovered block. -/
def ambientRecoveredCommonDim {z K : ℕ} (m : Fin K → ℕ) :
    AmbientRecoveredBlockIndex z K → ℕ
  | Sum.inl _ => 1
  | Sum.inr j => m j

/-- The conditional-factor dimension of an ambient recovered block. -/
def ambientRecoveredConditionalDim {z K : ℕ} (d : Fin K → ℕ) :
    AmbientRecoveredBlockIndex z K → ℕ
  | Sum.inl _ => 1
  | Sum.inr j => d j

/-- The common density factor on an ambient recovered block.

Complementary one-dimensional sectors carry the unique density matrix.
Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(14),
lines 493--502. -/
def ambientRecoveredCommonState {z K : ℕ} {m : Fin K → ℕ}
    (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ) :
    (j : AmbientRecoveredBlockIndex z K) →
      Matrix (Fin (ambientRecoveredCommonDim m j))
        (Fin (ambientRecoveredCommonDim m j)) ℂ
  | Sum.inl _ => 1
  | Sum.inr j => σ j

/-- The unnormalized conditional factor on an ambient recovered block.

Complementary one-dimensional sectors have zero weight.  This is a zero
unnormalized factor, not an additional normalized physical state.
Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (14),
lines 499--502. -/
def ambientRecoveredConditionalState {z K dA : ℕ} {d : Fin K → ℕ}
    (ω : ∀ j, Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ) :
    (_j : AmbientRecoveredBlockIndex z K) →
      Matrix (Fin dA × Fin (ambientRecoveredConditionalDim d _j))
        (Fin dA × Fin (ambientRecoveredConditionalDim d _j)) ℂ
  | Sum.inl _ => 0
  | Sum.inr j => ω j

/-- Collapse the dependent sum of one-dimensional complementary sectors to
its complement index. -/
def ambientRecoveredComplementEquiv (z : ℕ) :
    ((_ : Fin z) × (Fin 1 × Fin 1)) ≃ Fin z where
  toFun x := x.1
  invFun j := ⟨j, (0, 0)⟩
  left_inv x := by
    rcases x with ⟨j, a, b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a
    subst b
    rfl
  right_inv _ := rfl

/-- Extend the joint-support tensor coordinates by one-dimensional
zero-weight sectors on the ambient complement.

This is the direct-sum tensor equivalence for the ambient middle subsystem in
HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (13), lines 493--496. -/
def recoveredAmbientMiddleBlockEquiv
    {dB n K : ℕ} {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n) :
    ((j : AmbientRecoveredBlockIndex (dB - n) K) ×
      (Fin (ambientRecoveredCommonDim m j) ×
        Fin (ambientRecoveredConditionalDim d j))) ≃ Fin dB :=
  (Equiv.sumSigmaDistrib fun j : AmbientRecoveredBlockIndex (dB - n) K ↦
      Fin (ambientRecoveredCommonDim m j) ×
        Fin (ambientRecoveredConditionalDim d j))
    |>.trans (Equiv.sumCongr (ambientRecoveredComplementEquiv (dB - n)) e)
    |>.trans e₀

@[simp]
private theorem recoveredAmbientMiddleBlockEquiv_apply_complement
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (j : Fin (dB - n))
    (u : Fin (ambientRecoveredCommonDim m (Sum.inl j)))
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inl j))) :
    recoveredAmbientMiddleBlockEquiv e₀ e ⟨Sum.inl j, (u, v)⟩ =
      e₀ (Sum.inl j) := by
  change Fin 1 at u v
  fin_cases u
  fin_cases v
  rfl

@[simp]
private theorem recoveredAmbientMiddleBlockEquiv_apply_support
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (j : Fin K) (u : Fin (m j)) (v : Fin (d j)) :
    recoveredAmbientMiddleBlockEquiv e₀ e ⟨Sum.inr j, (u, v)⟩ =
      e₀ (Sum.inr (e ⟨j, (u, v)⟩)) := rfl

/-- Reassociate subsystem `A` with the complement/support split of subsystem
`B`. -/
private def recoveredBipartiteComplementEquiv
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB) :
    ((Fin dA × Fin (dB - n)) ⊕ (Fin dA × Fin n)) ≃
      Fin dA × Fin dB :=
  (Equiv.prodSumDistrib (Fin dA) (Fin (dB - n)) (Fin n)).symm
    |>.trans ((Equiv.refl (Fin dA)).prodCongr e₀)

@[simp]
private theorem recoveredBipartiteComplementEquiv_symm_apply_complement
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (a : Fin dA) (j : Fin (dB - n)) :
    (recoveredBipartiteComplementEquiv (dA := dA) e₀).symm
        (a, e₀ (Sum.inl j)) =
      Sum.inl (a, j) := by
  simp [recoveredBipartiteComplementEquiv]

@[simp]
private theorem recoveredBipartiteComplementEquiv_symm_apply_support
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (a : Fin dA) (j : Fin n) :
    (recoveredBipartiteComplementEquiv (dA := dA) e₀).symm
        (a, e₀ (Sum.inr j)) =
      Sum.inr (a, j) := by
  simp [recoveredBipartiteComplementEquiv]

@[simp]
private theorem recoveredAmbientBipartiteBlockEquiv_apply_complement
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (j : Fin (dB - n))
    (u : Fin (ambientRecoveredCommonDim m (Sum.inl j)))
    (a : Fin dA)
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inl j))) :
    recoveredBipartiteBlockEquiv
        (recoveredAmbientMiddleBlockEquiv e₀ e)
        ⟨Sum.inl j, (u, (a, v))⟩ =
      (a, e₀ (Sum.inl j)) := by
  change
    (a, recoveredAmbientMiddleBlockEquiv e₀ e ⟨Sum.inl j, (u, v)⟩) =
      (a, e₀ (Sum.inl j))
  rw [recoveredAmbientMiddleBlockEquiv_apply_complement]

@[simp]
private theorem recoveredAmbientBipartiteBlockEquiv_apply_support
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (j : Fin K) (u : Fin (m j)) (a : Fin dA) (v : Fin (d j)) :
    recoveredBipartiteBlockEquiv
        (recoveredAmbientMiddleBlockEquiv e₀ e)
        ⟨Sum.inr j, (u, (a, v))⟩ =
      (a, e₀ (Sum.inr (e ⟨j, (u, v)⟩))) := by
  change
    (a, recoveredAmbientMiddleBlockEquiv e₀ e ⟨Sum.inr j, (u, v)⟩) =
      (a, e₀ (Sum.inr (e ⟨j, (u, v)⟩)))
  rw [recoveredAmbientMiddleBlockEquiv_apply_support]

@[simp]
private theorem recoveredAmbientBipartiteBlockEquiv_symm_apply_complement
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (a : Fin dA) (j : Fin (dB - n)) :
    (recoveredBipartiteBlockEquiv
        (recoveredAmbientMiddleBlockEquiv e₀ e)).symm
        (a, e₀ (Sum.inl j)) =
      ⟨Sum.inl j, ((0 : Fin 1), (a, (0 : Fin 1)))⟩ := by
  exact recoveredBipartiteBlockEquiv_symm_apply
    (recoveredAmbientMiddleBlockEquiv e₀ e) a
      ⟨Sum.inl j, ((0 : Fin 1), (0 : Fin 1))⟩

@[simp]
private theorem recoveredAmbientBipartiteBlockEquiv_symm_apply_support
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (a : Fin dA) (j : Fin K) (u : Fin (m j)) (v : Fin (d j)) :
    (recoveredBipartiteBlockEquiv
        (recoveredAmbientMiddleBlockEquiv e₀ e)).symm
        (a, e₀ (Sum.inr (e ⟨j, (u, v)⟩))) =
      ⟨Sum.inr j, (u, (a, v))⟩ := by
  exact recoveredBipartiteBlockEquiv_symm_apply
    (recoveredAmbientMiddleBlockEquiv e₀ e) a
      ⟨Sum.inr j, (u, v)⟩

/-- Applying a conjugation to the second matrix factor is conjugation by the
identity-tensored rectangular matrix. -/
private theorem idTensorMap_conjugation
    {δ : Type*} [Fintype δ] [DecidableEq δ]
    {α β : Type*} [Fintype α]
    (Z : Matrix β α ℂ)
    (R : Matrix (δ × α) (δ × α) ℂ) :
    let T : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
      { toFun := fun X ↦ Z * X * Zᴴ
        map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
    idTensorMapLM T R =
      ((1 : Matrix δ δ ℂ) ⊗ₖ Z) * R *
        ((1 : Matrix δ δ ℂ) ⊗ₖ Z)ᴴ := by
  dsimp only
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [idTensorMapLM_apply, idTensorMap_apply,
    Matrix.mul_apply, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp
  rfl

/-- Applying the complementary zero embedding on the second factor produces
the corresponding complementary zero block on the bipartite space. -/
private theorem idTensorMap_zero_extension
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (R : Matrix (Fin dA × Fin n) (Fin dA × Fin n) ℂ) :
    let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
        Matrix (Fin dB) (Fin dB) ℂ :=
      { toFun := fun X ↦
          Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 X)
        map_add' := by
          intro X Y
          ext i j
          rw [← e₀.apply_symm_apply i, ← e₀.apply_symm_apply j]
          generalize e₀.symm i = i'
          generalize e₀.symm j = j'
          rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp
        map_smul' := by
          intro c X
          ext i j
          rw [← e₀.apply_symm_apply i, ← e₀.apply_symm_apply j]
          generalize e₀.symm i = i'
          generalize e₀.symm j = j'
          rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp }
    idTensorMapLM E R =
      Matrix.reindex (recoveredBipartiteComplementEquiv e₀)
        (recoveredBipartiteComplementEquiv e₀)
        (Matrix.fromBlocks 0 0 0 R) := by
  dsimp only
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [← e₀.apply_symm_apply b, ← e₀.apply_symm_apply b']
  generalize e₀.symm b = i
  generalize e₀.symm b' = i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [idTensorMapLM_apply, idTensorMap_apply,
      recoveredBipartiteComplementEquiv]

/-- Unitary zero extension on subsystem `B` lifts through a spectator
subsystem `A`. -/
private theorem one_kronecker_zero_extension_eq
    (Z : Matrix (Fin dB) (Fin n) ℂ)
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (U_B : Matrix (Fin dB) (Fin dB) ℂ)
    (hU_B : U_B ∈ Matrix.unitaryGroup (Fin dB) ℂ)
    (hzero : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      Z * A * Zᴴ =
        U_B * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U_B)
    (R : Matrix (Fin dA × Fin n) (Fin dA × Fin n) ℂ) :
    star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
        (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z) * R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z)ᴴ) *
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) =
      Matrix.reindex (recoveredBipartiteComplementEquiv e₀)
        (recoveredBipartiteComplementEquiv e₀)
        (Matrix.fromBlocks 0 0 0 R) := by
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X ↦
        Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 X)
      map_add' := by
        intro X Y
        ext i j
        rw [← e₀.apply_symm_apply i, ← e₀.apply_symm_apply j]
        generalize e₀.symm i = i'
        generalize e₀.symm j = j'
        rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp
      map_smul' := by
        intro c X
        ext i j
        rw [← e₀.apply_symm_apply i, ← e₀.apply_symm_apply j]
        generalize e₀.symm i = i'
        generalize e₀.symm j = j'
        rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp }
  let T_Z : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X ↦ Z * X * Zᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
  let T_U : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X ↦ U_B * X * U_Bᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  have hmaps : T_Z = T_U.comp E := by
    ext A i j
    exact congrFun (congrFun (hzero A) i) j
  have hconjZ :
      idTensorMapLM T_Z R =
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z) * R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z)ᴴ := by
    simpa only [T_Z] using idTensorMap_conjugation Z R
  have hconjU :
      idTensorMapLM T_U (idTensorMapLM E R) =
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          idTensorMapLM E R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)ᴴ := by
    simpa only [T_U] using idTensorMap_conjugation U_B (idTensorMapLM E R)
  have htensorComp :
      idTensorMapLM (T_U.comp E) R =
        idTensorMapLM T_U (idTensorMapLM E R) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    rfl
  have hlift :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z) * R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z)ᴴ =
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          idTensorMapLM E R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)ᴴ := by
    rw [← hconjZ, hmaps, htensorComp, hconjU]
  have hUleft : star U_B * U_B = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hU_B
  have hUleft' : U_Bᴴ * U_B = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hUleft
  have hUliftLeft :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hUleft',
      Matrix.one_mul]
    exact Matrix.one_kronecker_one
  rw [hlift]
  have hUliftLeft' :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)ᴴ *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hUliftLeft
  calc
    star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
            idTensorMapLM E R *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)ᴴ) *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) =
        (star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)) *
          idTensorMapLM E R *
          (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)ᴴ *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)) := by
          simp only [Matrix.mul_assoc]
    _ = idTensorMapLM E R := by rw [hUliftLeft, hUliftLeft']; simp
    _ = _ := idTensorMap_zero_extension e₀ R

/-- The complementary zero block and the supported tensor blocks form one
ambient direct sum of tensor sectors. -/
private theorem reindex_fromBlocks_support_eq_ambientBlockForm
    {d m : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (ω : ∀ j,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ) :
    Matrix.reindex (recoveredBipartiteComplementEquiv e₀)
        (recoveredBipartiteComplementEquiv e₀)
        (Matrix.fromBlocks 0 0 0
          (Matrix.reindex (recoveredBipartiteBlockEquiv e)
            (recoveredBipartiteBlockEquiv e)
            (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j))) =
      Matrix.reindex
        (recoveredBipartiteBlockEquiv
          (recoveredAmbientMiddleBlockEquiv e₀ e))
        (recoveredBipartiteBlockEquiv
          (recoveredAmbientMiddleBlockEquiv e₀ e))
        (Matrix.blockDiagonal' fun j ↦
          ambientRecoveredCommonState σ j ⊗ₖ
            ambientRecoveredConditionalState ω j) := by
  classical
  let g := recoveredBipartiteBlockEquiv (dA := dA)
    (recoveredAmbientMiddleBlockEquiv e₀ e)
  ext x y
  rw [← g.apply_symm_apply x, ← g.apply_symm_apply y]
  generalize g.symm x = x'
  generalize g.symm y = y'
  rcases x' with ⟨j, u, a, v⟩
  rcases y' with ⟨j', u', a', v'⟩
  rcases j with j | j <;> rcases j' with j' | j'
  · change Fin 1 at u v u' v'
    fin_cases u
    fin_cases v
    fin_cases u'
    fin_cases v'
    simp [g, ambientRecoveredCommonState,
      ambientRecoveredConditionalState, Matrix.blockDiagonal'_apply]
  · change Fin 1 at u v
    change Fin (m j') at u'
    change Fin (d j') at v'
    fin_cases u
    fin_cases v
    simp [g, ambientRecoveredCommonState,
      ambientRecoveredConditionalState, Matrix.blockDiagonal'_apply]
  · change Fin (m j) at u
    change Fin (d j) at v
    change Fin 1 at u' v'
    fin_cases u'
    fin_cases v'
    simp [g, ambientRecoveredCommonState,
      ambientRecoveredConditionalState, Matrix.blockDiagonal'_apply]
  · change Fin (m j) at u
    change Fin (d j) at v
    change Fin (m j') at u'
    change Fin (d j') at v'
    simp [g, ambientRecoveredCommonState,
      ambientRecoveredConditionalState, Matrix.blockDiagonal'_apply]
    rfl

/-- The exact recovered conditional-family witnesses together with ambient
direct-sum tensor coordinates for the middle subsystem.

Every complementary basis direction is a one-dimensional tensor sector.  Its
common factor is the unique density matrix and its unnormalized conditional
factor is zero.  Thus all sectors have positive factor dimensions, while the
supported factors, positivity assertions, and trace identities are retained
exactly.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(14),
lines 493--502.  TNLean writes the tensor factors in the reverse order from
HJPW. -/
structure RecoveredConditionalAmbientBipartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))] where
  jointSupport : RecoveredConditionalBipartiteBlockForm ρ_ABC hρ_dm
  e₀ : (Fin (dB - jointSupport.n) ⊕ Fin jointSupport.n) ≃ Fin dB
  U_B : Matrix (Fin dB) (Fin dB) ℂ
  U_B_unitary : U_B ∈ Matrix.unitaryGroup (Fin dB) ℂ
  /-- The ambient unitary extends the support coordinates: every matrix on the
  minimum joint support becomes its complementary zero extension.

  Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (13),
  lines 493--496. -/
  ambient_support_extension :
    ∀ A : Matrix (Fin jointSupport.n) (Fin jointSupport.n) ℂ,
      (jointSupport.V * jointSupport.U) * A *
          (jointSupport.V * jointSupport.U)ᴴ =
        U_B * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U_B
  ambient_d_pos :
    ∀ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      0 < ambientRecoveredConditionalDim jointSupport.d j
  ambient_m_pos :
    ∀ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      0 < ambientRecoveredCommonDim jointSupport.m j
  ambient_σ_pos :
    ∀ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      (ambientRecoveredCommonState jointSupport.σ j).PosSemidef
  ambient_σ_trace :
    ∀ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      (ambientRecoveredCommonState jointSupport.σ j).trace = 1
  ambient_ω_pos :
    ∀ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      (ambientRecoveredConditionalState jointSupport.ω j).PosSemidef
  ambient_ω_trace_sum :
    ∑ j : AmbientRecoveredBlockIndex (dB - jointSupport.n) jointSupport.K,
      (ambientRecoveredConditionalState jointSupport.ω j).trace = 1
  ambient_bipartite_block_form :
    let eB := recoveredAmbientMiddleBlockEquiv e₀ jointSupport.e
    star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
        traceC_ABC ρ_ABC *
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) =
      Matrix.reindex (recoveredBipartiteBlockEquiv eB)
        (recoveredBipartiteBlockEquiv eB)
        (Matrix.blockDiagonal' fun j ↦
          ambientRecoveredCommonState jointSupport.σ j ⊗ₖ
            ambientRecoveredConditionalState jointSupport.ω j)

/-- **Ambient recovered bipartite block form.**

At equality in strong subadditivity, subsystem `B` admits an ambient
direct-sum tensor decomposition.  In the corresponding unitary coordinates,
the bipartite marginal is a direct sum
`\bigoplus_j σ_j \otimes ω_j`, with positive common density factors,
positive unnormalized conditional factors, and total conditional trace one.
Complementary directions outside the minimum joint support occur as
one-dimensional zero-weight sectors.

This is the ambient middle-system decomposition and equation (14) in HJPW,
arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(14), lines 493--502.
TNLean writes the tensor factors in the reverse order from HJPW.  No statement
about the recovery-dilation action in equation (15) is made here. -/
theorem exists_recoveredConditionalAmbientBipartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    letI : Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC)) :=
      recoveredEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
        rw [← trace_eq_trace_traceC_ABC]
        exact hρ_dm.2)
    Nonempty
      (RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) := by
  classical
  letI : Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC)) :=
    recoveredEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2)
  obtain ⟨support⟩ :=
    exists_recoveredConditionalBipartiteBlockForm_jointSupport
      ρ_ABC hρ_dm hSSA
  let Z : Matrix (Fin dB) (Fin support.n) ℂ := support.V * support.U
  have hUleft : star support.U * support.U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp support.U_unitary
  have hZstar : Zᴴ = star support.U * support.Vᴴ := by
    simp only [Z, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  have hZ : Zᴴ * Z = 1 := by
    rw [hZstar]
    dsimp only [Z]
    calc
      star support.U * support.Vᴴ * (support.V * support.U) =
          star support.U * (support.Vᴴ * support.V) * support.U := by
            simp only [Matrix.mul_assoc]
      _ = star support.U * support.U := by
        rw [support.V_isometry]
        simp
      _ = 1 := hUleft
  obtain ⟨e₀, U_B_group, hzero⟩ :=
    Matrix.exists_unitary_zero_extension_eq Z hZ
  let U_B : Matrix (Fin dB) (Fin dB) ℂ := U_B_group
  have hambientSupportExtension :
      ∀ A : Matrix (Fin support.n) (Fin support.n) ℂ,
        (support.V * support.U) * A * (support.V * support.U)ᴴ =
          U_B * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U_B := by
    simpa only [Z, U_B] using hzero
  let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ support.V
  let L := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ support.U
  let R := Lᴴ * (Wᴴ * traceC_ABC ρ_ABC * W) * L
  have hUright : support.U * star support.U = 1 :=
    Matrix.mem_unitaryGroup_iff.mp support.U_unitary
  have hLright : L * Lᴴ = 1 := by
    dsimp only [L]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul]
    change (1 * 1) ⊗ₖ (support.U * star support.U) = 1
    rw [Matrix.one_mul, hUright]
    exact Matrix.one_kronecker_one
  have hcompress : L * R * Lᴴ = Wᴴ * traceC_ABC ρ_ABC * W := by
    dsimp only [R]
    calc
      L * (Lᴴ * (Wᴴ * traceC_ABC ρ_ABC * W) * L) * Lᴴ =
          (L * Lᴴ) * (Wᴴ * traceC_ABC ρ_ABC * W) * (L * Lᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = Wᴴ * traceC_ABC ρ_ABC * W := by rw [hLright]; simp
  have hWL :
      W * L = (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z := by
    dsimp only [W, L, Z]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hρZ :
      traceC_ABC ρ_ABC =
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z) * R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z)ᴴ := by
    calc
      traceC_ABC ρ_ABC = W * (Wᴴ * traceC_ABC ρ_ABC * W) * Wᴴ :=
        support.ambient_reconstruction.symm
      _ = W * (L * R * Lᴴ) * Wᴴ := by rw [hcompress]
      _ = (W * L) * R * (W * L)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z) * R *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z)ᴴ := by
        rw [hWL]
  have hnested :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          traceC_ABC ρ_ABC *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) =
        Matrix.reindex (recoveredBipartiteComplementEquiv e₀)
          (recoveredBipartiteComplementEquiv e₀)
          (Matrix.fromBlocks 0 0 0 R) := by
    exact (congrArg (fun X ↦
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) * X *
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B)) hρZ).trans
          (one_kronecker_zero_extension_eq Z e₀ U_B
            U_B_group.property (by
              simpa only [Z] using hambientSupportExtension) R)
  have hR :
      R = Matrix.reindex (recoveredBipartiteBlockEquiv support.e)
          (recoveredBipartiteBlockEquiv support.e)
          (Matrix.blockDiagonal' fun j ↦ support.σ j ⊗ₖ support.ω j) :=
    support.bipartite_block_form
  have hambient :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) *
          traceC_ABC ρ_ABC *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U_B) =
        Matrix.reindex
          (recoveredBipartiteBlockEquiv
            (recoveredAmbientMiddleBlockEquiv e₀ support.e))
          (recoveredBipartiteBlockEquiv
            (recoveredAmbientMiddleBlockEquiv e₀ support.e))
          (Matrix.blockDiagonal' fun j ↦
            ambientRecoveredCommonState support.σ j ⊗ₖ
              ambientRecoveredConditionalState support.ω j) := by
    rw [hnested, hR]
    exact reindex_fromBlocks_support_eq_ambientBlockForm
      e₀ support.e support.σ support.ω
  refine ⟨{
    jointSupport := support
    e₀ := e₀
    U_B := U_B
    U_B_unitary := U_B_group.property
    ambient_support_extension := hambientSupportExtension
    ambient_d_pos := ?_
    ambient_m_pos := ?_
    ambient_σ_pos := ?_
    ambient_σ_trace := ?_
    ambient_ω_pos := ?_
    ambient_ω_trace_sum := ?_
    ambient_bipartite_block_form := hambient }⟩
  · intro j
    rcases j with j | j
    · exact Nat.zero_lt_one
    · exact support.d_pos j
  · intro j
    rcases j with j | j
    · exact Nat.zero_lt_one
    · exact support.m_pos j
  · intro j
    rcases j with j | j
    · exact Matrix.PosSemidef.one
    · exact support.σ_pos j
  · intro j
    rcases j with j | j
    · change (1 : Matrix (Fin 1) (Fin 1) ℂ).trace = 1
      simp
    · exact support.σ_trace j
  · intro j
    rcases j with j | j
    · exact Matrix.PosSemidef.zero
    · exact support.ω_pos j
  · rw [Fintype.sum_sum_type]
    change
      (∑ _ : Fin (dB - support.n),
          (0 : Matrix (Fin dA × Fin 1) (Fin dA × Fin 1) ℂ).trace) +
        ∑ j, (support.ω j).trace = 1
    rw [show
      (∑ _ : Fin (dB - support.n),
        (0 : Matrix (Fin dA × Fin 1) (Fin dA × Fin 1) ℂ).trace) = 0 by
          simp, zero_add]
    exact support.ω_trace_sum

end Matrix
