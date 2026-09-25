/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.MPS.MPDO.Defs

/-!
# Bond similarities and periodic operators of matrix-unit tensors

Two matrix product operator tensors whose letters are related by one bond-space similarity
`G M^{ij} H = N^{ij}`, with `G H = 1` and `H G = 1`, have the same periodic operators, even when
the two bond spaces are presented with different index sets of the same size. The zero tensor has
the zero periodic operator at every positive length. When every letter is a scaled matrix unit,
the matrix elements of the periodic operator are read off from the cyclic chaining of the units.

## Main results

* `MPOTensor.evalWord_eq_mul_mul_of_conj`: a bond similarity transports word evaluations.
* `MPOTensor.mpo_eq_of_conj`: a letterwise bond similarity preserves periodic operators.
* `MPOTensor.mpo_zero_of_pos`: the zero tensor has the zero periodic operator at positive length.
* `MPOTensor.mpo_apply_of_eq_smul_single`: the periodic operator of a tensor whose letters are
  scaled matrix units.
-/

open scoped Matrix

namespace MPOTensor

variable {d D D' : ℕ}

/-- A bond-space similarity with a two-sided inverse transports word evaluations. -/
theorem evalWord_eq_mul_mul_of_conj {M : MPOTensor d D} {N : MPOTensor d D'}
    {G : Matrix (Fin D') (Fin D) ℂ} {H : Matrix (Fin D) (Fin D') ℂ} (hGH : G * H = 1)
    (hHG : H * G = 1) (hconj : ∀ i j, G * M i j * H = N i j) :
    ∀ is js : List (Fin d), evalWord M is js = H * evalWord N is js * G
  | [], [] => by simp [hHG]
  | [], _ :: _ => by simp [evalWord]
  | _ :: _, [] => by simp [evalWord]
  | i :: is, j :: js => by
    have hM : M i j = H * N i j * G := by
      rw [← hconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHG, Matrix.one_mul,
        Matrix.mul_assoc, hHG, Matrix.mul_one]
    rw [evalWord_cons, evalWord_cons, evalWord_eq_mul_mul_of_conj hGH hHG hconj is js, hM]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G H, hGH, Matrix.one_mul]

/-- Tensors related letter by letter by a bond-space similarity with a two-sided inverse have the
same periodic operators, even when the bond dimensions are presented differently. -/
theorem mpo_eq_of_conj {M : MPOTensor d D} {N : MPOTensor d D'}
    {G : Matrix (Fin D') (Fin D) ℂ} {H : Matrix (Fin D) (Fin D') ℂ} (hGH : G * H = 1)
    (hHG : H * G = 1) (hconj : ∀ i j, G * M i j * H = N i j) (L : ℕ) :
    mpo M L = mpo N L := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_eq_mul_mul_of_conj hGH hHG hconj, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hGH, Matrix.one_mul]

/-- The MPO of the zero local tensor vanishes at every positive chain length. -/
theorem mpo_zero_of_pos {L : ℕ} (hL : 0 < L) : mpo (0 : MPOTensor d D) L = 0 := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, Matrix.zero_apply]
  rw [evalWord_ofFn]
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [List.prod_eq_zero (List.mem_ofFn.mpr ⟨0, rfl⟩), Matrix.trace_zero]

/-- **Periodic operator of a tensor of scaled matrix units.** When every letter is a scaled
matrix unit `c i j • E_{l i j, r i j}`, the `(σ, τ)` entry at positive length is the product of
the scalars along the configuration if the matrix units chain around the ring, and zero
otherwise. -/
theorem mpo_apply_of_eq_smul_single (M : MPOTensor d D) (c : Fin d → Fin d → ℂ)
    (l r : Fin d → Fin d → Fin D) (hM : ∀ i j, M i j = c i j • Matrix.single (l i j) (r i j) 1)
    {N : ℕ} (hN : 0 < N) (σ τ : Fin N → Fin d) :
    mpo M N σ τ =
      if ∀ k, r (σ k) (τ k) = l (σ (finRotate N k)) (τ (finRotate N k)) then
        ∏ k, c (σ k) (τ k) else 0 := by
  obtain ⟨L, rfl⟩ : ∃ L', N = L' + 1 := ⟨N - 1, by omega⟩
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_ofFn]
  simp_rw [hM]
  exact Matrix.trace_ofFn_prod_smul_single L _ _ _

end MPOTensor
