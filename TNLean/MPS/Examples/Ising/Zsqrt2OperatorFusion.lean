/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Rings.Zsqrt2Ring
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.MPDO.DirectSum

/-!
# Fusion of periodic operators from a letter identity over `ℤ[√2]`

Let `X`, `Y`, `T` be matrix product operator tensors with entries in `ℤ[√2]`. If one explicit
change of bond coordinates `G`, with inverse `c⁻¹ H`, conjugates every letter of the stacked
tensor `X ⋆ Y` into the letter of `T` padded by a zero block, then the periodic operators satisfy
`O_L(X) O_L(Y) = O_L(T)` at every positive length. The hypotheses are identities between explicit
matrices over `ℤ[√2]`, which the kernel decides. This is the exact-arithmetic form of the
word-trace route `MPOTensor.mpo_mul_eq_of_trace_evalWord`: the similarity gives the word traces
directly, without a compression datum.

## Main definitions

* `MPSTensor.padZsqrt2`: a matrix over `ℤ√2` padded by a zero block, in the bond order of
  `MPOTensor.directSum`.

When the letters of the two factors are scaled matrix units, the conjugated stacked letter is an
explicit short sum (`MPSTensor.mul_mulTensorR_mul_transpose_eq_list`), which keeps the kernel
evaluation of the letter identities cheap.

## Main results

* `MPSTensor.mulTensorR_of_eq_smul_single`: the stacked letter of two tensors of scaled matrix
  units is a sum of scaled matrix units.
* `MPSTensor.mul_mulTensorR_mul_transpose_eq_list`: its conjugate by `G` and `Gᵀ`, as a sum
  over the labels with a nonzero coefficient.
* `MPSTensor.mulTensorR_eq_zero_of_ne`: the stacked letter of two block-diagonal tensors
  vanishes across blocks.
* `MPSTensor.mpo_mul_eq_of_zsqrt2_conj`: the fusion of two periodic operators from a letter
  identity over `ℤ√2`.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-! ### Stacked letters of tensors of scaled matrix units -/

section ScaledUnits

variable {R : Type*} [CommRing R] {d D₁ D₂ : ℕ}

/-- The bond-space product of two tensors of scaled matrix units is a sum of scaled matrix
units. -/
theorem mulTensorR_of_eq_smul_single
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (a b : Fin d → Fin d → R)
    (l r : Fin d → Fin d → Fin D₁) (l' r' : Fin d → Fin d → Fin D₂)
    (hM : ∀ i j, M i j = a i j • Matrix.single (l i j) (r i j) 1)
    (hN : ∀ i j, N i j = b i j • Matrix.single (l' i j) (r' i j) 1) (i k : Fin d) :
    mulTensorR M N i k = ∑ j : Fin d, (a i j * b j k) •
      Matrix.single (finProdFinEquiv (l i j, l' j k)) (finProdFinEquiv (r i j, r' j k)) 1 := by
  unfold mulTensorR
  ext x y
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [hM, hN, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Matrix.single_kronecker_single, smul_smul, Matrix.smul_apply,
    smul_eq_mul, Matrix.single_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq, mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (b j k) (a i j)]

/-- Conjugating a sum of scaled matrix units by a matrix and its transpose. -/
theorem mul_sum_smul_single_mul_transpose {m n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] (G : Matrix m n R) (c : ι → R) (p q : ι → n) :
    G * (∑ j, c j • Matrix.single (p j) (q j) (1 : R)) * Gᵀ =
      Matrix.of fun x y => ∑ j, c j * G x (p j) * G y (q j) := by
  ext x y
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, ite_and]
  ring

/-- **The conjugated stacked letter of two tensors of scaled matrix units.** If the letters of
`M` and `N` are scaled matrix units and the coefficient `a i j` vanishes for `j` outside a
duplicate-free list `next i`, then conjugating a letter of the stacked tensor by `G` and `Gᵀ`
gives the explicit sum over `next i`. The right side is cheap to evaluate, so an identity for it
between explicit matrices is decided quickly. -/
theorem mul_mulTensorR_mul_transpose_eq_list
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R) (a b : Fin d → Fin d → R)
    (l r : Fin d → Fin d → Fin D₁) (l' r' : Fin d → Fin d → Fin D₂)
    (hM : ∀ i j, M i j = a i j • Matrix.single (l i j) (r i j) 1)
    (hN : ∀ i j, N i j = b i j • Matrix.single (l' i j) (r' i j) 1)
    (next : Fin d → List (Fin d)) (hnext : ∀ i, (next i).Nodup)
    (hzero : ∀ i j, j ∉ next i → a i j = 0)
    {m : Type*} (G : Matrix m (Fin (D₁ * D₂)) R) (i k : Fin d) :
    G * mulTensorR M N i k * Gᵀ = Matrix.of fun x y => ((next i).map fun j =>
      a i j * b j k * G x (finProdFinEquiv (l i j, l' j k)) *
        G y (finProdFinEquiv (r i j, r' j k))).sum := by
  rw [mulTensorR_of_eq_smul_single M N a b l r l' r' hM hN,
    mul_sum_smul_single_mul_transpose]
  ext x y
  rw [Matrix.of_apply, Matrix.of_apply, ← List.sum_toFinset _ (hnext i)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [hzero i j (by simpa using hj), zero_mul, zero_mul, zero_mul]

/-- The stacked letter of two tensors that are block diagonal for a labelling `ρ` of the physical
index vanishes across blocks. -/
theorem mulTensorR_eq_zero_of_ne {α : Type*} (ρ : Fin d → α)
    (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) R)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) R)
    (hM : ∀ i j, ρ i ≠ ρ j → M i j = 0) (hN : ∀ i j, ρ i ≠ ρ j → N i j = 0) {i k : Fin d}
    (hik : ρ i ≠ ρ k) : mulTensorR M N i k = 0 := by
  unfold mulTensorR
  rw [Finset.sum_eq_zero fun j _ => ?_]
  · simp
  by_cases hj : ρ i = ρ j
  · rw [hN j k (hj ▸ hik), Matrix.kronecker_zero]
  · rw [hM i j hj, Matrix.zero_kronecker]

end ScaledUnits

/-! ### Fusion from a letter identity -/

/-- A matrix over `ℤ√2` padded by a zero block of size `z`, in the bond order of
`MPOTensor.directSum`. -/
def padZsqrt2 (z : ℕ) {k : ℕ} (X : Matrix (Fin k) (Fin k) (ℤ√2)) :
    Matrix (Fin (k + z)) (Fin (k + z)) (ℤ√2) :=
  (Matrix.fromBlocks X 0 0 0).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem complexOfZsqrt2_padZsqrt2 (z : ℕ) {k : ℕ} (X : Matrix (Fin k) (Fin k) (ℤ√2)) :
    complexOfZsqrt2 (padZsqrt2 z X) =
      (Matrix.fromBlocks (complexOfZsqrt2 X) 0 0 0).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
  ext i j
  simp only [padZsqrt2, complexOfZsqrt2_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp

/-- A padded scaled matrix unit is the scaled matrix unit at the embedded indices. -/
theorem padZsqrt2_smul_single (z : ℕ) {k : ℕ} (c : ℤ√2) (a b : Fin k) :
    padZsqrt2 z (c • Matrix.single a b 1) =
      c • Matrix.single (Fin.castAdd z a) (Fin.castAdd z b) 1 := by
  have h : Matrix.fromBlocks (c • Matrix.single a b (1 : ℤ√2)) 0 0 (0 : Matrix (Fin z) (Fin z) _) =
      Matrix.single (Sum.inl a) (Sum.inl b) c := by
    ext (i | i) (j | j) <;> simp [Matrix.single_apply]
  rw [padZsqrt2, h, Matrix.submatrix_single_equiv, Matrix.smul_single, smul_eq_mul, mul_one]
  simp

/-- **The fusion of two periodic operators from a letter identity over `ℤ√2`.** If an explicit
matrix `G` with inverse `c⁻¹ H` conjugates every letter of the stacked tensor `X ⋆ Y` into the
letter of `T` padded by a zero block, then `O_L(X) O_L(Y) = O_L(T)` at every positive length. -/
theorem mpo_mul_eq_of_zsqrt2_conj {d D₁ D₂ k z : ℕ}
    (XZ : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) (ℤ√2))
    (YZ : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) (ℤ√2))
    (TZ : Fin d → Fin d → Matrix (Fin k) (Fin k) (ℤ√2))
    (G : Matrix (Fin (k + z)) (Fin (D₁ * D₂)) (ℤ√2))
    (H : Matrix (Fin (D₁ * D₂)) (Fin (k + z)) (ℤ√2)) (c : ℤ√2) (hc : c ≠ 0)
    (hGH : G * H = c • 1) (hHG : H * G = c • 1)
    (hconj : ∀ i j, G * mulZsqrt2Tensor XZ YZ i j * H = c • padZsqrt2 z (TZ i j))
    {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo (fun i j => complexOfZsqrt2 (XZ i j)) L *
        MPOTensor.mpo (fun i j => complexOfZsqrt2 (YZ i j)) L =
      MPOTensor.mpo (fun i j => complexOfZsqrt2 (TZ i j)) L := by
  rw [← MPOTensor.mpo_mulTensor]
  have hM : MPOTensor.mulTensor (fun i j => complexOfZsqrt2 (XZ i j))
      (fun i j => complexOfZsqrt2 (YZ i j)) =
      fun i j => complexOfZsqrt2 (mulZsqrt2Tensor XZ YZ i j) :=
    funext fun i => funext fun j => mulTensor_complexOfRing _ XZ YZ i j
  have hγ : zsqrt2ToComplex c ≠ 0 := zsqrt2ToComplex_ne_zero hc
  rw [hM, MPOTensor.mpo_eq_of_conj (N := MPOTensor.directSum
      (fun i j => complexOfZsqrt2 (TZ i j)) (0 : MPOTensor d z))
      (G := complexOfZsqrt2 G) (H := (zsqrt2ToComplex c)⁻¹ • complexOfZsqrt2 H) ?_ ?_ ?_,
    MPOTensor.mpo_directSum, MPOTensor.mpo_zero_of_pos hL, add_zero]
  · rw [Matrix.mul_smul, ← complexOfZsqrt2_mul, hGH, complexOfZsqrt2_smul, complexOfZsqrt2_one,
      smul_smul, inv_mul_cancel₀ hγ, one_smul]
  · rw [Matrix.smul_mul, ← complexOfZsqrt2_mul, hHG, complexOfZsqrt2_smul, complexOfZsqrt2_one,
      smul_smul, inv_mul_cancel₀ hγ, one_smul]
  · intro i j
    rw [Matrix.mul_smul, ← complexOfZsqrt2_mul, ← complexOfZsqrt2_mul, hconj,
      complexOfZsqrt2_smul, smul_smul, inv_mul_cancel₀ hγ, one_smul, complexOfZsqrt2_padZsqrt2]
    rfl

end MPSTensor
