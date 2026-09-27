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
* `MPOTensor.mpo_eq_of_diagonal_conj`: the same for a diagonal bond similarity with nowhere-zero
  entries.
* `MPOTensor.mpo_apply_comp`: restricting the physical alphabet along a map restricts the
  periodic operators.
* `MPOTensor.mpo_zero_of_pos`: the zero tensor has the zero periodic operator at positive length.
* `MPOTensor.mpo_apply_of_eq_smul_single`: the periodic operator of a tensor whose letters are
  scaled matrix units.
-/

open scoped Matrix

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- A diagonal matrix with nowhere-zero entries times the diagonal matrix of the entrywise
inverses is the identity. -/
theorem diagonal_mul_diagonal_inv {v : n → K} (hv : ∀ i, v i ≠ 0) :
    diagonal v * diagonal v⁻¹ = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hv i))

/-- The diagonal matrix of the entrywise inverses of nowhere-zero entries times the original
diagonal matrix is the identity. -/
theorem diagonal_inv_mul_diagonal {v : n → K} (hv : ∀ i, v i ≠ 0) :
    diagonal v⁻¹ * diagonal v = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hv i))

end Matrix

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

/-- Tensors related letter by letter by a diagonal bond similarity `diag g`, with `g` nowhere
zero, have the same periodic operators. -/
theorem mpo_eq_of_diagonal_conj {M N : MPOTensor d D} (g : Fin D → ℂ) (hg : ∀ p, g p ≠ 0)
    (hconj : ∀ i j, Matrix.diagonal g * M i j * Matrix.diagonal g⁻¹ = N i j) (L : ℕ) :
    mpo M L = mpo N L :=
  mpo_eq_of_conj (Matrix.diagonal_mul_diagonal_inv hg) (Matrix.diagonal_inv_mul_diagonal hg)
    hconj L

/-- Restricting both physical legs of a tensor along a map `g` of alphabets restricts its
periodic operators: the entry of `mpo M L` at `(g ∘ σ, g ∘ τ)` is the entry at `(σ, τ)` of the
periodic operator of the tensor with letters `M^{g i, g j}`. -/
theorem mpo_apply_comp {d' : ℕ} (M : MPOTensor d D) (g : Fin d' → Fin d) (L : ℕ)
    (σ τ : Fin L → Fin d') :
    mpo M L (g ∘ σ) (g ∘ τ) = mpo (fun i j => M (g i) (g j)) L σ τ := by
  simp only [mpo_apply, mpoMatrixEntry, evalWord_ofFn, Function.comp_apply]

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
