/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.PhysicalMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Embedded direct sums of matrix product tensors

Coordinate embeddings with disjoint ranges describe a direct sum without choosing a
particular flattening of its virtual indices. Nonempty words, periodic vectors, and blocked
physical matrices decompose into their sector contributions with the original complex weights.
These identities do not assume orthogonality of physical sector states.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, Supplemental Material,
  equations (S2)–(S4), with one retained copy of each labelled tensor.
-/

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### Coordinate embeddings -/

/-- The coordinate isometry `E : ℂ^{D'} → ℂ^D`, `|a⟩ ↦ |ι a⟩`. -/
def coordEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D) (Fin D') ℂ :=
  of fun x a => if x = ι a then 1 else 0

/-- `E_ιᴴ E_ι'` has the entry `1` where `ι a = ι' a'` and `0` elsewhere. -/
theorem conjTranspose_coordEmbedding_mul_apply {D' D'' : ℕ} (ι : Fin D' → Fin D)
    (ι' : Fin D'' → Fin D) (a : Fin D') (a' : Fin D'') :
    ((coordEmbedding ι)ᴴ * coordEmbedding ι') a a' = if ι a = ι' a' then 1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single (ι a)]
  · by_cases h : ι a = ι' a' <;> simp [coordEmbedding, conjTranspose_apply, h]
  · intro x _ hx
    simp [coordEmbedding, conjTranspose_apply, hx]
  · simp

/-- An injective coordinate map gives an isometry, `E_ιᴴ E_ι = 1`. -/
theorem conjTranspose_coordEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (coordEmbedding ι)ᴴ * coordEmbedding ι = 1 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, one_apply]
  exact if_congr hι.eq_iff rfl rfl

/-- Coordinate maps with disjoint ranges give isometries with orthogonal ranges. -/
theorem conjTranspose_coordEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (coordEmbedding ι)ᴴ * coordEmbedding ι' = 0 := by
  ext a a'
  rw [conjTranspose_coordEmbedding_mul_apply, Matrix.zero_apply, ite_eq_right (h a a')]

/-- `E_ιᴴ (E_ι' Y) = 0` for coordinate maps with disjoint ranges. -/
theorem conjTranspose_coordEmbedding_mul_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') {γ : Type*} (Y : Matrix (Fin D'') γ ℂ) :
    (coordEmbedding ι)ᴴ * (coordEmbedding ι' * Y) = 0 := by
  rw [← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_eq_zero h, Matrix.zero_mul]

/-- `E_ιᴴ (E_ι Y) = Y` for an injective coordinate map. -/
theorem conjTranspose_coordEmbedding_mul_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) {γ : Type*} (Y : Matrix (Fin D') γ ℂ) :
    (coordEmbedding ι)ᴴ * (coordEmbedding ι * Y) = Y := by
  rw [← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self hι, Matrix.one_mul]

/-- The isometry `K = E_ι ⊗ E_ι` embedding the bond pairs `ℂ^{D'} ⊗ ℂ^{D'}` of a block into the
bond pairs of the direct sum; these index the columns of the physical matrix. -/
def pairEmbedding {D' : ℕ} (ι : Fin D' → Fin D) : Matrix (Fin D × Fin D) (Fin D' × Fin D') ℂ :=
  coordEmbedding ι ⊗ₖ coordEmbedding ι

theorem pairEmbedding_apply {D' : ℕ} (ι : Fin D' → Fin D) (p : Fin D × Fin D)
    (r : Fin D' × Fin D') : pairEmbedding ι p r = if p = (ι r.1, ι r.2) then 1 else 0 := by
  rcases p with ⟨x, y⟩
  rcases r with ⟨a, c⟩
  simp only [pairEmbedding, kroneckerMap_apply, coordEmbedding, of_apply, Prod.mk.injEq]
  by_cases h1 : x = ι a <;> by_cases h2 : y = ι c <;> simp [h1, h2]

theorem conjTranspose_pairEmbedding_mul_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) : (pairEmbedding ι)ᴴ * pairEmbedding ι = 1 := by
  rw [pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_self hι, one_kronecker_one]

theorem conjTranspose_pairEmbedding_mul_eq_zero {D' D'' : ℕ} {ι : Fin D' → Fin D}
    {ι' : Fin D'' → Fin D} (h : ∀ a a', ι a ≠ ι' a') :
    (pairEmbedding ι)ᴴ * pairEmbedding ι' = 0 := by
  rw [pairEmbedding, pairEmbedding, conjTranspose_kronecker, ← mul_kronecker_mul,
    conjTranspose_coordEmbedding_mul_eq_zero h, zero_kronecker]

/-! ### The direct sum of blocks of multiplicity one -/

variable {Dj : Fin b → ℕ}

/-- The direct sum `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` of blocks `A_j`, each of multiplicity one, with the block
`j` placed on the bond coordinates `ι_j`: arXiv:2307.01696, Supplemental Material, eq. (S2),
for `m_j = 1`. -/
def blockSum (Aj : (j : Fin b) → MPSTensor d (Dj j)) (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (μ : Fin b → ℂ) : MPSTensor d D :=
  fun i => ∑ j, μ j • (coordEmbedding (ι j) * Aj j i * (coordEmbedding (ι j))ᴴ)

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- A nonempty word of the direct sum is the direct sum of the words of the blocks:
`A^{w} = ⊕ⱼ μⱼ^{|w|} A_j^{w}`. -/
theorem evalWord_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) :
    ∀ w : List (Fin d), w ≠ [] →
      Kraus.evalWord (blockSum Aj ι μ) w =
        ∑ j, μ j ^ w.length •
          (coordEmbedding (ι j) * Kraus.evalWord (Aj j) w * (coordEmbedding (ι j))ᴴ)
  | [], h => absurd rfl h
  | [i], _ => by simp [blockSum]
  | i :: i' :: w, _ => by
    rw [Kraus.evalWord_cons, evalWord_blockSum hι hdisj μ (i' :: w) (List.cons_ne_nil _ _),
      blockSum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single j]
    · rw [smul_mul_smul_comm]
      simp only [Kraus.evalWord_cons, List.length_cons, pow_succ', Matrix.mul_assoc,
        conjTranspose_coordEmbedding_mul_mul_self (hι j)]
    · intro j' _ hj'
      rw [smul_mul_smul_comm]
      simp only [Matrix.mul_assoc,
        conjTranspose_coordEmbedding_mul_mul_eq_zero (hdisj j j' (Ne.symm hj')), Matrix.mul_zero,
        smul_zero]
    · simp

/-- The periodic state of the direct sum on `N ≥ 1` sites:
`|φ_N(A)⟩ = ∑ⱼ μⱼ^N |φ_N(A_j)⟩` (arXiv:2307.01696, Supplemental Material, eqs. (S3) and (S4),
for `m_j = 1`, where `βⱼ = μⱼ^N`). -/
theorem mpv_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {N : ℕ} (hN : N ≠ 0)
    (s : Fin N → Fin d) : mpv (blockSum Aj ι μ) s = ∑ j, μ j ^ N * mpv (Aj j) s := by
  have hw : List.ofFn s ≠ [] := by simpa [List.ofFn_eq_nil_iff] using hN
  rw [mpv_eq, coeff_eq, evalWord_blockSum hι hdisj μ _ hw, trace_sum, List.length_ofFn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_smul, trace_mul_comm, ← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self (hι j),
    Matrix.one_mul, smul_eq_mul, mpv_eq, coeff_eq]

/-- The physical matrix of the `q`-site blocked tensor of the direct sum, for `q ≥ 1`:
`B = ∑ⱼ μⱼ^q B_j K_jᴴ`, where `B_j` is the blocked tensor of the block `j` and `K_j` embeds its
bond pairs. -/
theorem physicalMatrix_blockTensor_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (blockSum Aj ι μ) q) =
      ∑ j, μ j ^ q • (physicalMatrix (blockTensor (Aj j) q) * (pairEmbedding (ι j))ᴴ) := by
  ext w p
  have hw : Kraus.wordOfBlock d q w ≠ [] := by
    rw [← List.length_pos_iff, Kraus.length_wordOfBlock]; omega
  simp only [physicalMatrix, blockTensor, Kraus.blockTensor]
  rw [evalWord_blockSum hι hdisj μ _ hw, Kraus.length_wordOfBlock, Matrix.sum_apply,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply]
  congr 1
  simp only [mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rcases p with ⟨x, y⟩
  simp only [conjTranspose_apply, pairEmbedding_apply, coordEmbedding, of_apply, Prod.mk.injEq,
    physicalMatrix]
  by_cases h1 : x = ι j a <;> by_cases h2 : y = ι j c <;> simp [h1, h2, Kraus.blockTensor]


/-! ### The bond pairs of the blocks -/

/-- The bond pairs `(ι_j a, ι_j c)` of the direct sum that lie in one block `j`. -/
def blockPairs (ι : (j : Fin b) → Fin (Dj j) → Fin D) : Finset (Fin D × Fin D) :=
  Finset.univ.biUnion fun j =>
    Finset.univ.image fun ac : Fin (Dj j) × Fin (Dj j) => (ι j ac.1, ι j ac.2)

theorem mem_blockPairs {ι : (j : Fin b) → Fin (Dj j) → Fin D} {p : Fin D × Fin D} :
    p ∈ blockPairs ι ↔ ∃ j a c, (ι j a, ι j c) = p := by
  simp only [blockPairs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.exists]

end MPSTensor
