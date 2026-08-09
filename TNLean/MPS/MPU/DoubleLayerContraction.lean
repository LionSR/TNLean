/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import TNLean.Algebra.ListProduct
import TNLean.Algebra.MatrixTracePairing
import TNLean.Algebra.RankOneSandwich
import TNLean.Algebra.ShiftedZeroTraceNilpotent
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.Simple
import TNLean.MPS.MPU.TransferStabilization

/-!
# Double-layer blocking and mixed physical contractions

This file formalizes the first algebraic part of the blocking argument in
arXiv:1703.09188, Proposition `blockingsimple`, lines 390--409.

-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Physical blocking commutes with the physical adjoint. The equality is
literal: both operations preserve the order of the virtual word.

Source: arXiv:1703.09188, lines 390--405. -/
theorem physicalAdjointTensor_blockTensor (U : MPOTensor d D) (L : ℕ) :
    physicalAdjointTensor (blockTensor U L) =
      blockTensor (physicalAdjointTensor U) L := by
  funext I K
  ext β α
  rw [blockTensor_apply]
  have h := evalWord_physicalAdjointTensor U
    (MPSTensor.wordOfBlock d L I) (MPSTensor.wordOfBlock d L K) (by simp)
  rw [h]
  rfl

/-- Physical blocking commutes with formation of the physical-adjoint double
layer. This is the local compatibility used when applying `WIsom` after
blocking.

Source: arXiv:1703.09188, lines 390--405. -/
theorem doubleLayerTensor_blockTensor (U : MPOTensor d D) (L : ℕ) :
    doubleLayerTensor (blockTensor U L) = blockTensor (doubleLayerTensor U) L := by
  rw [doubleLayerTensor, doubleLayerTensor, blockTensor_mulTensor,
    physicalAdjointTensor_blockTensor]

/-- Contract the two physical legs of an MPO letter against a physical matrix.
The transpose in the coefficient makes `contractPhysical W (single j i 1) = W i j`.

Source: arXiv:1703.09188, equation `WIsom`, lines 390--395. -/
noncomputable def contractPhysical (W : MPOTensor d D)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d, ∑ j : Fin d, (X j i) • W i j

@[simp] theorem contractPhysical_single (W : MPOTensor d D) (i j : Fin d) :
    contractPhysical W (Matrix.single j i 1) = W i j := by
  classical
  simp only [contractPhysical]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Matrix.single, Ne.symm hb]
    · simp
  · intro a _ ha
    simp [Matrix.single, Ne.symm ha]
  · simp

/-- Physical contraction is linear in the physical matrix. -/
noncomputable def contractPhysicalLinear (W : MPOTensor d D) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun := contractPhysical W
  map_add' X Y := by simp [contractPhysical, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [contractPhysical, smul_smul, Finset.smul_sum]

@[simp] theorem contractPhysicalLinear_apply (W : MPOTensor d D)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    contractPhysicalLinear W X = contractPhysical W X := rfl

/-- The normalized physical diagonal of an MPO tensor. -/
noncomputable def normalizedDiagonal (W : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ :=
  (d : ℂ)⁻¹ • contractPhysical W 1

/-- The normalized diagonal turns physical blocking into matrix powers. The
blocked physical index is reindexed explicitly through `decodeBlockEquiv`.
-/
theorem normalizedDiagonal_blockTensor [NeZero d] (L : ℕ)
    (W : MPOTensor d D) :
    normalizedDiagonal (blockTensor W L) = normalizedDiagonal W ^ L := by
  classical
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdim : (MPSTensor.blockPhysDim d L : ℂ)⁻¹ = ((d : ℂ)⁻¹) ^ L := by
    rw [MPSTensor.blockPhysDim_eq_pow, Nat.cast_pow, inv_pow]
  simp only [normalizedDiagonal, contractPhysical, Matrix.one_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    blockTensor_apply, hdim]
  have hsum := (MPSTensor.decodeBlockEquiv d L).sum_comp
    (fun σ ↦ evalWord W (List.ofFn σ) (List.ofFn σ))
  simp only [MPSTensor.decodeBlockEquiv_apply] at hsum
  change ((d : ℂ)⁻¹) ^ L •
      (∑ x, evalWord W (List.ofFn (MPSTensor.decodeBlock d L x))
        (List.ofFn (MPSTensor.decodeBlock d L x))) = _
  rw [hsum]
  simp only [evalWord_ofFn]
  have hprod := List.prod_ofFn_sum (fun _ : Fin L ↦ fun i : Fin d ↦ W i i)
  rw [← hprod]
  rw [smul_pow]
  congr 1
  simp [List.ofFn_const]

/-- The normalized diagonal of the physical-adjoint double layer is the
normalized transfer matrix, with the row and column pair indices explicitly
encoded by `finProdFinEquiv`.

Source: arXiv:1703.09188, equations `eq:transfer-op` and `WIsom`, lines
336--340 and 390--395. -/
theorem normalizedDiagonal_doubleLayerTensor [NeZero d] (U : MPOTensor d D) :
    normalizedDiagonal (doubleLayerTensor U) =
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  classical
  have hd : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hnorm : ((Real.sqrt d : ℂ)⁻¹) * ((Real.sqrt d : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.le]
    simp
  ext p q
  rcases finProdFinEquiv.surjective p with ⟨⟨p₁, p₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective q with ⟨⟨q₁, q₂⟩, rfl⟩
  simp only [normalizedDiagonal, contractPhysical, doubleLayerTensor_apply,
    normalizedFlattening, MPSTensor.transferMap_apply, transferMatrix,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply,
    physicalAdjointTensor_apply, Matrix.kronecker_apply,
    Equiv.symm_apply_apply, Matrix.one_apply, smul_eq_mul,
    MPOTensor.toMPSTensor]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    Matrix.of_apply, ite_and, Finset.mul_sum, Finset.sum_mul]
  simp only [RCLike.star_def, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Matrix.smul_apply, smul_eq_mul, mul_one,
    star_mul', star_inv₀, Complex.conj_ofReal, Finset.sum_ite_eq]
  let g : Fin d × Fin d → ℂ := fun x ↦
    ((Real.sqrt d : ℂ)⁻¹) * U x.1 x.2 p₂ q₂ *
      (((Real.sqrt d : ℂ)⁻¹) * (starRingEnd ℂ) (U x.1 x.2 p₁ q₁))
  let f : Fin (d * d) → ℂ := fun x ↦
    ((Real.sqrt d : ℂ)⁻¹) * U x.divNat x.modNat p₂ q₂ *
      (((Real.sqrt d : ℂ)⁻¹) * (starRingEnd ℂ) (U x.divNat x.modNat p₁ q₁))
  calc
    (∑ i : Fin d, ∑ j : Fin d,
        (d : ℂ)⁻¹ * ((starRingEnd ℂ) (U j i p₁ q₁) * U j i p₂ q₂)) =
        ∑ x : Fin d × Fin d, g x := by
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [g]
      rw [← hnorm]
      ring
    _ = ∑ x : Fin (d * d), f x := by
      exact Fintype.sum_equiv finProdFinEquiv g f (by
        intro x
        have hx := finProdFinEquiv.symm_apply_apply x
        have hx₁ := congrArg Prod.fst hx
        have hx₂ := congrArg Prod.snd hx
        change (finProdFinEquiv x).divNat = x.1 at hx₁
        change (finProdFinEquiv x).modNat = x.2 at hx₂
        simp only [g, f]
        rw [hx₁, hx₂])
    _ = _ := rfl

/-- The exact normalized diagonal after blocking is the corresponding power of
the normalized transfer matrix. Both sides use the explicit encoding
`Fin D × Fin D ≃ Fin (D * D)` in the same orientation.

Source: arXiv:1703.09188, lines 397--405. -/
theorem normalizedDiagonal_doubleLayerTensor_blockTensor [NeZero d]
    (U : MPOTensor d D) (L : ℕ) :
    normalizedDiagonal (doubleLayerTensor (blockTensor U L)) =
      (transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ L).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor L,
    normalizedDiagonal_doubleLayerTensor]
  let E := transferMatrix (MPSTensor.transferMap U.normalizedFlattening)
  change (E.submatrix finProdFinEquiv.symm finProdFinEquiv.symm) ^ L =
    (E ^ L).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  induction L with
  | zero =>
      simp [Matrix.submatrix_one_equiv]
  | succ L ih =>
      rw [pow_succ, pow_succ, ih]
      exact Matrix.submatrix_mul_equiv (E ^ L) E
        finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm


/-- At the MPU stabilization exponent, the normalized blocked double-layer
diagonal is the explicitly reindexed rank-one transfer projector.

Source: arXiv:1703.09188, lines 397--405. -/
theorem IsMPU.normalizedDiagonal_doubleLayerTensor_blockTensor_eq_vecMulVec
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U) (hD : 1 < D) :
    normalizedDiagonal
        (doubleLayerTensor (MPOTensor.blockTensor U
          (hU.normalizedTransferStabilization hD).exponent)) =
      (Matrix.vecMulVec
        (hU.normalizedTransferStabilization hD).right
        (hU.normalizedTransferStabilization hD).left).submatrix
          finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [normalizedDiagonal_doubleLayerTensor_blockTensor]
  rw [(hU.normalizedTransferStabilization hD).power_eq]


/-- A residual physical slice: subtract the identity coefficient from a physical
contraction. This is the basis-free form of the residual matrices `S_α` in
`WIsom`.

Source: arXiv:1703.09188, equation `WIsom`, lines 390--395. -/
noncomputable def residualSlice (W : MPOTensor d D)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  contractPhysical W X - Matrix.trace X • normalizedDiagonal W

@[simp] theorem residualSlice_one [NeZero d] (W : MPOTensor d D) :
    residualSlice W 1 = 0 := by
  simp [residualSlice, normalizedDiagonal, Matrix.trace_one, Fintype.card_fin,
    NeZero.ne d]

/-- Residual slices are exactly contractions against traceless physical matrices. -/
theorem residualSlice_eq_contractPhysical_tracelessPart [NeZero d]
    (W : MPOTensor d D) (X : Matrix (Fin d) (Fin d) ℂ) :
    residualSlice W X = contractPhysical W (Matrix.tracelessPart X) := by
  change contractPhysical W X - Matrix.trace X • ((d : ℂ)⁻¹ • contractPhysical W 1) =
    contractPhysicalLinear W (X - (((d : ℂ)⁻¹ * Matrix.trace X) • 1))
  rw [map_sub, map_smul]
  simp only [contractPhysicalLinear_apply, smul_smul]
  congr 1
  ring

/-- Source-facing `WIsom` decomposition. There is a physical basis `σ` with a
distinguished identity vector and traceless remaining vectors, and virtual
coefficients `S`, such that every double-layer letter is the identity term
plus the residual basis terms. The coefficients are constructed by contracting
against the trace-dual basis.

Source: arXiv:1703.09188, equation `WIsom`, lines 390--395. -/
theorem exists_identity_add_traceless_decomposition [NeZero d]
    (W : MPOTensor d D) :
    ∃ (σ : Module.Basis (Fin (d * d)) ℂ (Matrix (Fin d) (Fin d) ℂ))
      (e : Fin (d * d)) (S : Fin (d * d) → Matrix (Fin D) (Fin D) ℂ),
      σ e = 1 ∧
      (∀ a, a ≠ e → Matrix.trace (σ a) = 0) ∧
      S e = normalizedDiagonal W ∧
      ∀ i j, W i j =
        (if i = j then normalizedDiagonal W else 0) +
          ∑ a ∈ (Finset.univ.erase e), (σ a i j) • S a := by
  obtain ⟨σ, e, he, htr⟩ := Matrix.exists_identity_traceless_basis (d := d)
  let B := Matrix.traceBilinForm (Fin d)
  have hB : B.Nondegenerate := Matrix.traceBilinForm_nondegenerate
  let τ := B.dualBasis hB σ
  let S : Fin (d * d) → Matrix (Fin D) (Fin D) ℂ := fun a ↦ contractPhysical W (τ a)
  have hτe : τ e = ((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    apply τ.ext_elem
    intro a
    rw [τ.repr_self, Finsupp.single_apply]
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    simp only [B, Matrix.traceBilinForm_apply, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.one_mul, smul_eq_mul]
    by_cases hae : a = e
    · subst a
      rw [he, Matrix.trace_one, Fintype.card_fin, if_pos rfl]
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]
    · rw [htr a hae, mul_zero, if_neg (Ne.symm hae)]
  have hSe : S e = normalizedDiagonal W := by
    simp only [S, hτe, normalizedDiagonal]
    change contractPhysicalLinear W (((d : ℂ)⁻¹) • 1) = _
    rw [map_smul]
    rfl
  have hfull (i j : Fin d) : W i j = ∑ a : Fin (d * d), (σ a i j) • S a := by
    have hexpand := τ.sum_repr (Matrix.single j i (1 : ℂ))
    calc
      W i j = contractPhysicalLinear W (Matrix.single j i (1 : ℂ)) := by simp
      _ = contractPhysicalLinear W
          (∑ a : Fin (d * d), (τ.repr (Matrix.single j i (1 : ℂ)) a) • τ a) := by
            rw [hexpand]
      _ = ∑ a : Fin (d * d), (σ a i j) • S a := by
            simp only [map_sum, map_smul, contractPhysicalLinear_apply, S]
            apply Finset.sum_congr rfl
            intro a _
            congr 1
            rw [LinearMap.BilinForm.dualBasis_repr_apply]
            simp [B, Matrix.traceBilinForm_apply, Matrix.trace_single_mul]
  refine ⟨σ, e, S, he, htr, hSe, ?_⟩
  intro i j
  rw [hfull i j, ← Finset.add_sum_erase _ _ (Finset.mem_univ e), hSe]
  simp [he, Matrix.one_apply]

/-- Multilinear extraction from a closed MPO identity. Contracting every physical
site against `X k` turns the closed virtual product into the product of the
physical traces.

The assumption `1 < N` matches the lengths controlled by `IsMPU`; the algebraic
statement itself only needs the displayed closed-chain equality.

Source: arXiv:1703.09188, lines 405--410. -/
theorem trace_prod_contractPhysical_of_mpo_eq_one
    (W : MPOTensor d D) {N : ℕ}
    (hW : mpo W N = (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ))
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (List.ofFn (fun k ↦ contractPhysical W (X k))).prod =
      ∏ k, Matrix.trace (X k) := by
  classical
  change Matrix.trace
      (List.ofFn (fun k ↦ ∑ i : Fin d, ∑ j : Fin d, ((X k) j i) • W i j)).prod = _
  rw [List.prod_ofFn_sum]
  simp_rw [List.prod_ofFn_sum]
  change Matrix.trace
      (∑ σ : Fin N → Fin d, ∑ τ : Fin N → Fin d,
        (List.ofFn (fun k ↦ ((X k) (τ k) (σ k)) • W (σ k) (τ k))).prod) = _
  rw [Finset.sum_comm]
  have hdistrib :
      Matrix.trace
          (∑ τ : Fin N → Fin d, ∑ σ : Fin N → Fin d,
            (List.ofFn (fun k ↦ ((X k) (τ k) (σ k)) • W (σ k) (τ k))).prod) =
        ∑ τ : Fin N → Fin d, ∑ σ : Fin N → Fin d,
          (∏ k, (X k) (τ k) (σ k)) *
            Matrix.trace (List.ofFn (fun k ↦ W (σ k) (τ k))).prod := by
    rw [Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [List.prod_ofFn_smul, Matrix.trace_smul]
    rfl
  rw [hdistrib]
  have hentry (σ τ : Fin N → Fin d) :
      Matrix.trace (List.ofFn (fun k ↦ W (σ k) (τ k))).prod =
        if σ = τ then 1 else 0 := by
    have h := congrArg (fun M ↦ M σ τ) hW
    simpa [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Matrix.one_apply] using h
  simp_rw [hentry]
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.trace, Matrix.diag]
  exact (Fintype.prod_sum (fun k i ↦ (X k) i i)).symm

/-- The multilinear contraction identity for the double layer of an MPU. -/
theorem IsMPU.trace_prod_contractPhysical_doubleLayerTensor
    {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace
        (List.ofFn (fun k ↦ contractPhysical (doubleLayerTensor U) (X k))).prod =
      ∏ k, Matrix.trace (X k) := by
  apply trace_prod_contractPhysical_of_mpo_eq_one
  rw [mpo_doubleLayerTensor, hU.conjTranspose_mpo_mul_mpo hN]

/-- A family of physical contractions has zero closed virtual trace as soon as
one physical factor is traceless. -/
theorem IsMPU.trace_prod_contractPhysical_doubleLayerTensor_eq_zero_of_exists_trace_eq_zero
    {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∃ k, Matrix.trace (X k) = 0) :
    Matrix.trace
        (List.ofFn (fun k ↦ contractPhysical (doubleLayerTensor U) (X k))).prod = 0 := by
  rw [hU.trace_prod_contractPhysical_doubleLayerTensor hN]
  obtain ⟨k, hk⟩ := hX
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

/-- Every closed word of residual slices has zero trace at lengths greater
than one. This is the direct closed-chain consequence of MPU unitarity.

Source: arXiv:1703.09188, lines 405--410. -/
theorem IsMPU.trace_prod_residualSlice_doubleLayerTensor_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace
        (List.ofFn (fun k ↦ residualSlice (doubleLayerTensor U) (X k))).prod = 0 := by
  simp_rw [residualSlice_eq_contractPhysical_tracelessPart]
  apply hU.trace_prod_contractPhysical_doubleLayerTensor_eq_zero_of_exists_trace_eq_zero hN
  let k : Fin N := ⟨0, by omega⟩
  exact ⟨k, Matrix.trace_tracelessPart (X k)⟩

/-- Every individual residual slice of the double layer of an MPU is traceless.
The proof recovers the missing one-letter moment from the moments at all lengths
greater than one by nilpotence.

Source: arXiv:1703.09188, lines 405--410. -/
theorem IsMPU.trace_residualSlice_doubleLayerTensor_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (residualSlice (doubleLayerTensor U) X) = 0 := by
  classical
  let A := residualSlice (doubleLayerTensor U) X
  have hpow : ∀ N : ℕ, 1 < N → Matrix.trace (A ^ N) = 0 := by
    intro N hN
    have h := hU.trace_prod_residualSlice_doubleLayerTensor_eq_zero
      hN (fun _ : Fin N ↦ X)
    simpa [A, List.ofFn_const, List.prod_replicate] using h
  have hnil := Matrix.isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt A hpow
  exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

/-- A site is either the normalized identity coefficient or a residual slice. -/
noncomputable def mixedResidualFactor (W : MPOTensor d D)
    (isResidual : Bool) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  if isResidual then residualSlice W X else normalizedDiagonal W

/-- Every mixed closed word of length greater than one containing at least
one residual factor has zero trace. This is the direct closed-chain proof of the
basis-free residual-slice form of the mixed `S'_α` trace identity.

Source: arXiv:1703.09188, lines 405--410. -/
theorem IsMPU.trace_prod_mixedResidualFactor_doubleLayerTensor_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N)
    (isResidual : Fin N → Bool)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hmixed : ∃ k, isResidual k = true) :
    Matrix.trace
        (List.ofFn (fun k ↦ mixedResidualFactor (doubleLayerTensor U)
          (isResidual k) (X k))).prod = 0 := by
  let Y : Fin N → Matrix (Fin d) (Fin d) ℂ := fun k ↦
    if isResidual k then Matrix.tracelessPart (X k) else ((d : ℂ)⁻¹) • 1
  have hfactor (k : Fin N) :
      mixedResidualFactor (doubleLayerTensor U) (isResidual k) (X k) =
        contractPhysical (doubleLayerTensor U) (Y k) := by
    simp only [mixedResidualFactor, Y]
    by_cases hk : isResidual k = true
    · simp only [hk, ↓reduceIte,
        residualSlice_eq_contractPhysical_tracelessPart]
    · have hk' : isResidual k = false := Bool.eq_false_of_not_eq_true hk
      simp only [hk', Bool.false_eq, normalizedDiagonal]
      change ((d : ℂ)⁻¹) • contractPhysical (doubleLayerTensor U) 1 =
        contractPhysicalLinear (doubleLayerTensor U) (((d : ℂ)⁻¹) • 1)
      rw [map_smul]
      rfl
  simp_rw [hfactor]
  apply hU.trace_prod_contractPhysical_doubleLayerTensor_eq_zero_of_exists_trace_eq_zero hN
  obtain ⟨k, hk⟩ := hmixed
  refine ⟨k, ?_⟩
  simp [Y, hk]

/-- Every positive-length mixed closed word containing at least one residual
factor has zero trace, including a single residual letter.

Source: arXiv:1703.09188, lines 405--410. -/
theorem IsMPU.trace_prod_mixedResidualFactor_doubleLayerTensor_eq_zero_of_pos
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 0 < N)
    (isResidual : Fin N → Bool)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hmixed : ∃ k, isResidual k = true) :
    Matrix.trace
        (List.ofFn (fun k ↦ mixedResidualFactor (doubleLayerTensor U)
          (isResidual k) (X k))).prod = 0 := by
  by_cases hN' : 1 < N
  · exact hU.trace_prod_mixedResidualFactor_doubleLayerTensor_eq_zero
      hN' isResidual X hmixed
  · have hN_one : N = 1 := by omega
    subst N
    obtain ⟨k, hk⟩ := hmixed
    have hk0 : isResidual 0 = true := by
      simpa only [Subsingleton.elim k 0] using hk
    simpa [List.ofFn_succ, mixedResidualFactor, hk0] using
      hU.trace_residualSlice_doubleLayerTensor_eq_zero (X 0)

/-- A nonempty residual word is annihilated when sandwiched by a rank-one
normalized diagonal. The trace premise is derived by adjoining the normalized
diagonal as one extra closed-chain factor.

Source: arXiv:1703.09188, equation `ESE=0`, lines 405--409. -/
theorem IsMPU.normalizedDiagonal_mul_prod_residualSlice_mul_normalizedDiagonal_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U)
    {m : ℕ} (hm : 0 < m) (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (ρ Φ : Fin (D * D) → ℂ)
    (hE : normalizedDiagonal (doubleLayerTensor U) = Matrix.vecMulVec ρ Φ) :
    normalizedDiagonal (doubleLayerTensor U) *
        (List.ofFn (fun k ↦ residualSlice (doubleLayerTensor U) (X k))).prod *
      normalizedDiagonal (doubleLayerTensor U) = 0 := by
  let isResidual : Fin (m + 1) → Bool := Fin.cases false (fun _ ↦ true)
  let X' : Fin (m + 1) → Matrix (Fin d) (Fin d) ℂ := Fin.cases 0 X
  have hmixed : ∃ k, isResidual k = true := by
    let k : Fin m := ⟨0, hm⟩
    exact ⟨k.succ, rfl⟩
  have hclosed := hU.trace_prod_mixedResidualFactor_doubleLayerTensor_eq_zero
    (N := m + 1) (by omega) isResidual X' hmixed
  have htrace : Matrix.trace
      ((List.ofFn (fun k ↦ residualSlice (doubleLayerTensor U) (X k))).prod *
        normalizedDiagonal (doubleLayerTensor U)) = 0 := by
    rw [Matrix.trace_mul_comm]
    simpa [isResidual, X', mixedResidualFactor, List.ofFn_succ] using hclosed
  exact Matrix.rankOne_sandwich_eq_zero_of_trace _ _ ρ Φ hE htrace

/-- If a normalized transfer power is rank one, every nonempty residual word
of the corresponding blocked double layer is annihilated by its normalized
diagonal. This theorem performs the physical blocking, explicit product-index
reindexing, mixed-trace extraction, trace rotation, and rank-one sandwich.

Source: arXiv:1703.09188, equation `ESE=0`, lines 405--409. -/
theorem IsMPU.blocked_normalizedDiagonal_sandwich_residual_prod_eq_zero
    [NeZero d] {U : MPOTensor d D} (hU : IsMPU U)
    (J : ℕ) (hJ : 0 < J) (ρ Φ : Fin D × Fin D → ℂ)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ Φ)
    {m : ℕ} (hm : 0 < m)
    (X : Fin m → Matrix (Fin (MPSTensor.blockPhysDim d J))
      (Fin (MPSTensor.blockPhysDim d J)) ℂ) :
    let V := MPOTensor.blockTensor U J
    normalizedDiagonal (doubleLayerTensor V) *
        (List.ofFn (fun k ↦ residualSlice (doubleLayerTensor V) (X k))).prod *
      normalizedDiagonal (doubleLayerTensor V) = 0 := by
  letI : NeZero (MPSTensor.blockPhysDim d J) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero J (NeZero.ne d)⟩
  let V := MPOTensor.blockTensor U J
  have hV : IsMPU V := hU.blockTensor J hJ
  let ρ' : Fin (D * D) → ℂ := fun i ↦ ρ (finProdFinEquiv.symm i)
  let Φ' : Fin (D * D) → ℂ := fun i ↦ Φ (finProdFinEquiv.symm i)
  have hE : normalizedDiagonal (doubleLayerTensor V) = Matrix.vecMulVec ρ' Φ' := by
    change normalizedDiagonal (doubleLayerTensor (MPOTensor.blockTensor U J)) = _
    rw [normalizedDiagonal_doubleLayerTensor_blockTensor, hpower]
    rfl
  exact hV.normalizedDiagonal_mul_prod_residualSlice_mul_normalizedDiagonal_eq_zero
    hm X ρ' Φ' hE

end MPOTensor
