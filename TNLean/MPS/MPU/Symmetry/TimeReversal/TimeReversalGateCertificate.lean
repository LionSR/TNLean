/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.StandardForm.FundamentalTheoremGates
import TNLean.MPS.MPU.StandardForm.SourceFactorChoiceGates
import TNLean.MPS.MPU.StandardForm.StandardFormDoubling
import TNLean.MPS.Operator.DensityOperator.AreaLaw
import TNLean.MPS.Operator.Unitary.StaircaseGates

/-!
# The local certificate for time reversal, without canonical form

Proposition `PropChiral` of arXiv:1703.09188 (lines 1201--1252) characterizes time reversal by a
local sign equation on the gates of a standard form. Its sufficiency proof, `UUdaggertrick` and
`eq:dagger-sym-cond` (lines 1214--1236), uses only two facts about the standard-form circuit:

* its adjoint is the circuit of the gates `(v†, u†)`, translated by one site
  (`MPOTensor.twoSiteCircuit_conjTranspose`);
* the periodic operator of a two-site block is invariant under that translation
  (`MPOTensor.mpo_blockTwo_submatrix_shifted`).

The local equation `A = σ (x ⊗ x†) B†` relates `(B†, A†)` to `(A, B)` by a gate gauge, so the
operator equals its adjoint. No canonical form or source factors of the tensor are used.

## Main results

* `MPOTensor.TwoSiteStandardFormData.mpo_blockTwo_eq_conjTranspose_of_local_sign`: the
  certificate for any standard form of a two-site block.
* `MPOTensor.mpo_even_eq_conjTranspose_of_blockTwo`: the passage to even rings of the original
  tensor.
* `MPOTensor.doubledU_eq_reindex_staircase`, `MPOTensor.doubledV_eq_reindex_staircase`: the
  doubled gates are the four-spin gates of `eq:dagger-sym-cond`.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d ℓ r N : ℕ}

/-- The local sign equation `A = σ (x ⊗ x†) B†` gives unitaries `X, Y` with
`B† = (X ⊗ Y) A` and `A† = B (Y† ⊗ X†)`: the gate gauges relating the standard
form `(A, B)` to the adjoint standard form `(B†, A†)`. Source: CPSV17,
`PropChiral`, `UUdaggertrick` and `eq:dagger-sym-cond`, lines 1214–1236. -/
theorem adjoint_gate_gauges_of_local_sign
    {q : ℕ} {P : Type*} (A : Matrix (Fin q × Fin q) P ℂ)
    (B : Matrix P (Fin q × Fin q) ℂ)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = σ • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (x : Matrix (Fin q) (Fin q) ℂ)ᴴ) * Bᴴ) :
    ∃ X Y : Matrix.unitaryGroup (Fin q) ℂ,
      Bᴴ = ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
        (Y : Matrix (Fin q) (Fin q) ℂ)) * A ∧
      Aᴴ = B * ((Y : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
        (X : Matrix (Fin q) (Fin q) ℂ)ᴴ) := by
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσstar : star σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hxx : (x : Matrix (Fin q) (Fin q) ℂ)ᴴ *
      (x : Matrix (Fin q) (Fin q) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp x.property
  let X := star x
  let Y : Matrix.unitaryGroup (Fin q) ℂ := ⟨σ • (x : Matrix (Fin q) (Fin q) ℂ), by
    rw [← Matrix.isUnitaryBetween_iff_mem_unitaryGroup]
    constructor
    · change (σ • (x : Matrix (Fin q) (Fin q) ℂ))ᴴ *
        (σ • (x : Matrix (Fin q) (Fin q) ℂ)) = 1
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hσstar, one_smul, hxx]
    · change (σ • (x : Matrix (Fin q) (Fin q) ℂ)) *
        (σ • (x : Matrix (Fin q) (Fin q) ℂ))ᴴ = 1
      have hσstar' : σ * star σ = 1 := by rw [mul_comm, hσstar]
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hσstar', one_smul]
      exact ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr x.property).2⟩
  let K := (x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᴴ
  have hK : Kᴴ * K = 1 :=
    ((Matrix.isUnitaryBetween_coe_unitaryGroup x).kronecker _ _
      (Matrix.isUnitaryBetween_star_coe_unitaryGroup x)).1
  have hXY : ((X : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ
      (Y : Matrix (Fin q) (Fin q) ℂ)) = σ • Kᴴ := by
    change (x : Matrix (Fin q) (Fin q) ℂ)ᴴ ⊗ₖ
      (σ • (x : Matrix (Fin q) (Fin q) ℂ)) = _
    rw [Matrix.kronecker_smul]
    simp only [K, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  refine ⟨X, Y, ?_, ?_⟩
  · rw [hXY, hlocal]
    change Bᴴ = (σ • Kᴴ) * ((σ • K) * Bᴴ)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσsq, one_smul]
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  · have h := congrArg Matrix.conjTranspose hlocal
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose] at h
    simpa only [X, Y, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_kronecker] using h

/-- **The adjoint of a standard-form circuit.** The adjoint of the circuit with unshifted gate `u`
and shifted gate `v` is the circuit with unshifted gate `v†` and shifted gate `u†`, read on the
pair configuration translated by one site. Source: arXiv:1703.09188, `UUdaggertrick`,
lines 1214--1226. -/
theorem twoSiteCircuit_conjTranspose [NeZero N]
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    (twoSiteShiftedLayer (N := N) v * twoSiteUnshiftedLayer (N := N) u)ᴴ =
      (twoSiteShiftedLayer (N := N) uᴴ * twoSiteUnshiftedLayer (N := N) vᴴ).submatrix
        (twoSiteShiftedPairEquiv (ℓ := d) (r := d))
        (twoSiteShiftedPairEquiv (ℓ := d) (r := d)) := by
  ext a b
  simp only [conjTranspose_apply, mul_apply, star_sum, star_mul', submatrix_apply]
  rw [← (twoSiteShiftedPairEquiv (N := N) (ℓ := ℓ) (r := r)).symm.sum_comp]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [mul_comm]
  congr 1
  · simp only [twoSiteShiftedLayer, twoSiteUnshiftedLayer, conjTranspose_apply, star_prod]
    refine (Fintype.prod_equiv (Equiv.addRight 1) _ _ fun x ↦ ?_).symm
    simp [twoSiteShiftedPairEquiv]
  · simp only [twoSiteShiftedLayer, twoSiteUnshiftedLayer, conjTranspose_apply, star_prod]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    simp [twoSiteShiftedPairEquiv]

/-- The `2N` spins of a configuration of `N` physical pairs, in chain order. -/
def pairConfigFlat (a : Fin N → Fin d × Fin d) : Fin (N * 2) → Fin d := fun k ↦
  if (finProdFinEquiv.symm k).2 = 0 then (a (finProdFinEquiv.symm k).1).1
  else (a (finProdFinEquiv.symm k).1).2

private theorem evalWord_blockTwo_ofFn {D : ℕ} (V : MPOTensor d D) (a b : Fin N → Fin d × Fin d) :
    evalWord (blockTwo V) (List.ofFn fun x ↦ finProdFinEquiv (a x))
        (List.ofFn fun x ↦ finProdFinEquiv (b x)) =
      evalWord V (List.ofFn (pairConfigFlat a)) (List.ofFn (pairConfigFlat b)) := by
  rw [evalWord_ofFn, evalWord_ofFn, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr (funext fun x ↦ ?_)
  have h0 : (⟨x * 2, by omega⟩ : Fin (N * 2)) = finProdFinEquiv (x, 0) := by
    ext; simp [finProdFinEquiv_apply_val]; ring
  have h1 : (⟨x * 2 + 1, by omega⟩ : Fin (N * 2)) = finProdFinEquiv (x, 1) := by
    ext; simp [finProdFinEquiv_apply_val]; ring
  simp [List.ofFn_succ, blockTwo_apply, pairConfigFlat, h0, h1]

private theorem ofFn_pairConfigFlat_shifted [NeZero N] (a : Fin N → Fin d × Fin d) :
    List.ofFn (pairConfigFlat (twoSiteShiftedPairEquiv (ℓ := d) (r := d) a)) =
      (List.ofFn (pairConfigFlat a)).rotate 1 := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ ↦ ?_
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_rotate, List.getElem_ofFn, List.getElem_ofFn]
  simp only [List.length_ofFn]
  obtain ⟨⟨x, j⟩, hk⟩ := finProdFinEquiv.surjective (⟨k, h₁⟩ : Fin (N * 2))
  have hkv : k = j + 2 * x := by
    have := congrArg Fin.val hk
    simpa [finProdFinEquiv_apply_val] using this.symm
  rw [show (⟨k, h₁⟩ : Fin (N * 2)) = finProdFinEquiv (x, j) from hk.symm]
  fin_cases j
  · have hidx : (⟨(k + 1) % (N * 2), Nat.mod_lt _ (by omega)⟩ : Fin (N * 2)) =
        finProdFinEquiv (x, 1) := by
      ext
      simp only [finProdFinEquiv_apply_val, Fin.val_one]
      rw [Nat.mod_eq_of_lt (by simp at hkv; omega)]
      simp at hkv
      omega
    rw [hidx]
    simp [pairConfigFlat, twoSiteShiftedPairEquiv]
  · have hidx : (⟨(k + 1) % (N * 2), Nat.mod_lt _ (by omega)⟩ : Fin (N * 2)) =
        finProdFinEquiv (x + 1, 0) := by
      ext
      simp only [finProdFinEquiv_apply_val, Fin.val_zero, zero_add, Fin.val_add]
      simp only at hkv
      rw [hkv, show 1 + 2 * (x : ℕ) + 1 = 2 * ((x : ℕ) + 1) by ring, mul_comm N 2,
        Nat.mul_mod_mul_left]
      congr 1
      rw [Fin.val_one', Nat.add_mod_mod]
    rw [hidx]
    simp [pairConfigFlat, twoSiteShiftedPairEquiv]

/-- The periodic operator of a two-site block, read in pair coordinates, is invariant under the
translation of the chain by one site of the original tensor. -/
theorem mpo_blockTwo_submatrix_shifted [NeZero N] {D : ℕ} (V : MPOTensor d D) :
    (Matrix.reindex (twoSitePairConfigEquiv d N).symm (twoSitePairConfigEquiv d N).symm
        (mpo (blockTwo V) N)).submatrix (twoSiteShiftedPairEquiv (ℓ := d) (r := d))
        (twoSiteShiftedPairEquiv (ℓ := d) (r := d)) =
      Matrix.reindex (twoSitePairConfigEquiv d N).symm (twoSitePairConfigEquiv d N).symm
        (mpo (blockTwo V) N) := by
  ext a b
  simp only [submatrix_apply, reindex_apply, Equiv.symm_symm, mpo_apply, mpoMatrixEntry]
  change trace (evalWord (blockTwo V)
      (List.ofFn fun x ↦ finProdFinEquiv (twoSiteShiftedPairEquiv (ℓ := d) (r := d) a x))
      (List.ofFn fun x ↦ finProdFinEquiv (twoSiteShiftedPairEquiv (ℓ := d) (r := d) b x))) =
    trace (evalWord (blockTwo V) (List.ofFn fun x ↦ finProdFinEquiv (a x))
      (List.ofFn fun x ↦ finProdFinEquiv (b x)))
  rw [evalWord_blockTwo_ofFn, evalWord_blockTwo_ofFn, ofFn_pairConfigFlat_shifted,
    ofFn_pairConfigFlat_shifted, trace_evalWord_rotate_one V _ _ (by simp)]

/-- **Local certificate for time reversal.** Let the two-site block of `V` have a standard form
with gates `A, B` of equal ranks, satisfying the local sign equation `A = σ (x ⊗ x†) B†`. Then
the periodic operator of the two-site block is self-adjoint on every ring.

The adjoint of the standard-form circuit is the circuit of the gates `(B†, A†)` translated by one
site; the local equation relates these gates to `(A, B)` by a gate gauge, and the operator of a
two-site block is invariant under that translation.

Source: arXiv:1703.09188, `PropChiral`, the implication proved by `UUdaggertrick` and
`eq:dagger-sym-cond`, lines 1214--1236. -/
theorem TwoSiteStandardFormData.mpo_blockTwo_eq_conjTranspose_of_local_sign {D q : ℕ}
    {V : MPOTensor d D} {A : Matrix (Fin q × Fin q) (Fin d × Fin d) ℂ}
    {B : Matrix (Fin d × Fin d) (Fin q × Fin q) ℂ} (S : TwoSiteStandardFormData (blockTwo V) A B)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (x : Matrix.unitaryGroup (Fin q) ℂ)
    (hlocal : A = σ • ((x : Matrix (Fin q) (Fin q) ℂ) ⊗ₖ (x : Matrix (Fin q) (Fin q) ℂ)ᴴ) * Bᴴ)
    (N : ℕ) [NeZero N] :
    mpo (blockTwo V) N = (mpo (blockTwo V) N)ᴴ := by
  have hS := S.mpo_eq_shifted_mul_unshifted (N := N) _ A B
  obtain ⟨X, Y, h₁, h₂⟩ := adjoint_gate_gauges_of_local_sign A B σ hσ x hlocal
  have hC : (twoSiteShiftedLayer (N := N) B * twoSiteUnshiftedLayer (N := N) A)ᴴ =
      twoSiteShiftedLayer (N := N) B * twoSiteUnshiftedLayer (N := N) A := by
    rw [twoSiteCircuit_conjTranspose, h₁, h₂, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, twoSiteCircuit_eq_of_gate_gauges, ← hS,
      mpo_blockTwo_submatrix_shifted]
  apply (Matrix.reindex (twoSitePairConfigEquiv d N).symm
    (twoSitePairConfigEquiv d N).symm).injective
  rw [← conjTranspose_reindex, hS, hC]

/-- Self-adjointness of the two-site block's operator on `m` sites is self-adjointness of the
original operator on `2m` sites. -/
theorem mpo_even_eq_conjTranspose_of_blockTwo {D : ℕ} {V : MPOTensor d D}
    {m : ℕ} (h : mpo (blockTwo V) m = (mpo (blockTwo V) m)ᴴ) :
    mpo V (m + m) = (mpo V (m + m))ᴴ := by
  rw [mpo_blockTwo_eq_reindex_blockTensor, conjTranspose_reindex] at h
  have h' := (Matrix.reindex _ _).injective h
  rw [mpo_blockTensor_eq_reindex, conjTranspose_reindex] at h'
  have h'' := (Matrix.reindex _ _).injective h'
  rwa [Nat.mul_two] at h''

/-- For square gates, the doubled unshifted gate is the four-spin gate `v₂₃ u₁₂ u₃₄` of
`eq:dagger-sym-cond`, read through `ℂ^d ⊗ ℂ^d ≅ ℂ^{d²}` on each pair. -/
theorem doubledU_eq_reindex_staircase (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledU u v = Matrix.reindex (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
      (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨k₁, k₂⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨l₁, l₂⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [doubledU_apply]
  simp [staircaseMiddle, mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    Finset.sum_ite_eq]

/-- For square gates, the doubled shifted gate is the middle gate `v₂₃`. -/
theorem doubledV_eq_reindex_staircase (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledV v = Matrix.reindex (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
      (staircaseMiddle (A := Fin d) (E := Fin d) v) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨k₁, k₂⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨l₁, l₂⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [doubledV_apply]
  simp [staircaseMiddle, kroneckerMap_apply, one_apply]

end MPOTensor
