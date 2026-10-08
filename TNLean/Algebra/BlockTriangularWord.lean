/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Block
import QICLean.Kraus.MultiBlockWord

/-!
# Block-triangular word products and coordinate embeddings

This file develops the block-triangular algebra behind the asymmetric fundamental theorem of
matrix product states (P5 note): diagonal blocks of a product of block upper-triangular
matrices multiply, word evaluations of a block upper-triangular family stay block upper
triangular with word-evaluated diagonal blocks, and the coordinate embeddings/projections of
each block form a biorthogonal system that reassembles a block-diagonal matrix. The file closes
with the nilpotency count underlying Theorem 7.7(vi): a product of as many strictly block
upper-triangular matrices as there are blocks vanishes.

Blocks are indexed by a type `o` which is ordered indirectly, through an injective labelling
`b : o → α` into a linear order; the case `b = id` recovers the usual block-triangular
statements for an ordered block index. The indirect form is what the asymmetric compression
theorem needs, where the blocks are labelled by target slots and their order is a separate
datum.

Word evaluation on the `Σ k, Fin (n k)` index type is the generic `evalWord` of
`QICLean.Kraus.MultiBlockWord` (unqualified, not `Kraus.evalWord`, which is specialized to
`Fin D` indices).

## Main results

* `Matrix.blockDiag'_mul_of_blockTriangular` — diagonal blocks of a product of block
  upper-triangular matrices multiply (P5 note, Lemma 7.3).
* `Matrix.blockTriangular_evalWord` — word evaluations of a block upper-triangular family
  stay block upper triangular.
* `Matrix.blockDiag'_evalWord` — diagonal blocks of a word evaluation are the word
  evaluations of the diagonal blocks (`eq:p5-triangular-word`).
* `Matrix.blockEmbed`, `Matrix.blockProj` — coordinate embedding/projection of a block, with
  the biorthogonality relations `Matrix.blockProj_mul_blockEmbed_self`,
  `Matrix.blockProj_mul_blockEmbed_of_ne`, `Matrix.blockProj_mul_mul_blockEmbed`, and the
  reassembly identity `Matrix.sum_blockEmbed_mul_mul_blockProj` (`eq:p5-block-biorthogonality`).
* `Matrix.StrictBlockTriangular` and `Matrix.evalWord_eq_zero_of_strictBlockTriangular` — the
  nilpotency count of Theorem 7.7(vi): a product of as many strictly block upper-triangular
  matrices as there are blocks vanishes (`eq:p5-main-nilpotency`).

## References

P5 note (asymmetric fundamental theorem draft), Lemma 7.3 and Theorem 7.7(vi).
-/

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ} {d : ℕ}

section Order

variable {α : Type*} [LinearOrder α] {b : o → α}

omit [DecidableEq o] in
/-- Diagonal blocks of a product of block upper-triangular matrices multiply
(P5 note, Lemma 7.3). -/
theorem blockDiag'_mul_of_blockTriangular (hb : Function.Injective b)
    {X Y : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hX : X.BlockTriangular fun x => b x.1) (hY : Y.BlockTriangular fun x => b x.1) (k : o) :
    (X * Y).blockDiag' k = X.blockDiag' k * Y.blockDiag' k := by
  ext i j
  simp only [blockDiag'_apply, Matrix.mul_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single k]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro i' _
    rcases lt_or_lt_iff_ne.mpr (fun h : b l = b k => hl (hb h)) with hlt | hgt
    · have hX0 : X ⟨k, i⟩ ⟨l, i'⟩ = 0 := hX hlt
      rw [hX0, zero_mul]
    · have hY0 : Y ⟨l, i'⟩ ⟨k, j⟩ = 0 := hY hgt
      rw [hY0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Word evaluations of a block upper-triangular family stay block upper triangular. -/
theorem blockTriangular_evalWord
    {T : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) (w : List (Fin d)) :
    (evalWord T w).BlockTriangular fun x => b x.1 := by
  induction w with
  | nil => simpa [evalWord] using blockTriangular_one
  | cons i w ih => simpa only [evalWord] using (hT i).mul ih

/-- Diagonal blocks of a word evaluation are the word evaluations of the diagonal blocks
(`eq:p5-triangular-word`). -/
theorem blockDiag'_evalWord (hb : Function.Injective b)
    {T : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) (w : List (Fin d)) (k : o) :
    (evalWord T w).blockDiag' k = evalWord (fun i => (T i).blockDiag' k) w := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      simp only [evalWord]
      rw [blockDiag'_mul_of_blockTriangular hb (hT i) (blockTriangular_evalWord hT w) k, ih]

end Order

section Embed

/-- Coordinate embedding of the `k`-th block (`eq:p5-block-biorthogonality`). -/
def blockEmbed (n : o → ℕ) (k : o) : Matrix (Σ k, Fin (n k)) (Fin (n k)) ℂ :=
  Matrix.of fun x j => if x = ⟨k, j⟩ then 1 else 0

/-- Coordinate projection onto the `k`-th block: the transpose of the embedding. -/
def blockProj (n : o → ℕ) (k : o) : Matrix (Fin (n k)) (Σ k, Fin (n k)) ℂ :=
  (blockEmbed n k).transpose

omit [Fintype o] in
/-- The block embedding vanishes away from its recorded coordinate. -/
theorem blockEmbed_apply_of_ne {k : o} {x : Σ k, Fin (n k)} {j : Fin (n k)}
    (h : x ≠ (⟨k, j⟩ : Σ k, Fin (n k))) : blockEmbed n k x j = 0 := by
  simp [blockEmbed, Matrix.of_apply, h]

omit [Fintype o] in
/-- The block embedding vanishes off its own block. -/
theorem blockEmbed_apply_of_fst_ne {k : o} {x : Σ k, Fin (n k)} (h : x.1 ≠ k) (j : Fin (n k)) :
    blockEmbed n k x j = 0 :=
  blockEmbed_apply_of_ne fun heq => h (congrArg Sigma.fst heq)

omit [Fintype o] in
/-- The block projection vanishes off its own block. -/
theorem blockProj_apply_of_fst_ne {k : o} (i : Fin (n k)) {y : Σ k, Fin (n k)} (h : y.1 ≠ k) :
    blockProj n k i y = 0 := by
  simp only [blockProj, Matrix.transpose_apply]
  exact blockEmbed_apply_of_fst_ne h i

omit [Fintype o] in
/-- The block embedding restricted to its own block is the identity indicator. -/
theorem blockEmbed_apply_fst_eq (k : o) (i j : Fin (n k)) :
    blockEmbed n k (⟨k, i⟩ : Σ k, Fin (n k)) j = if i = j then 1 else 0 := by
  simp [blockEmbed, Matrix.of_apply, Sigma.mk.injEq]

omit [Fintype o] in
/-- The block embedding restricted to its own block vanishes off the matching coordinate. -/
theorem blockEmbed_apply_fst_eq_of_ne {k : o} {i j : Fin (n k)} (h : i ≠ j) :
    blockEmbed n k (⟨k, i⟩ : Σ k, Fin (n k)) j = 0 := by
  rw [blockEmbed_apply_fst_eq]; simp [h]

theorem blockProj_mul_blockEmbed_self (k : o) : blockProj n k * blockEmbed n k = 1 := by
  ext i j
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨k, i⟩ : Σ k, Fin (n k))]
  · rw [blockEmbed_apply_fst_eq, blockEmbed_apply_fst_eq]
    simp
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨k, i⟩ : Σ k, Fin (n k))) h

theorem blockProj_mul_blockEmbed_of_ne {k l : o} (h : k ≠ l) :
    blockProj n k * blockEmbed n l = 0 := by
  ext i j
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x _
  rcases eq_or_ne x.1 k with hx | hx
  · have hxne : x.1 ≠ l := hx ▸ h
    rw [blockEmbed_apply_of_fst_ne hxne, mul_zero]
  · rw [blockEmbed_apply_of_fst_ne hx, zero_mul]

theorem blockProj_mul_mul_blockEmbed (M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    blockProj n k * M * blockEmbed n k = M.blockDiag' k := by
  ext i j
  simp only [Matrix.mul_apply, blockDiag'_apply]
  rw [Finset.sum_eq_single (⟨k, j⟩ : Σ k, Fin (n k))]
  · rw [Finset.sum_eq_single (⟨k, i⟩ : Σ k, Fin (n k))]
    · simp [blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
    · intro y _ hy
      simp only [blockProj, Matrix.transpose_apply]
      rw [blockEmbed_apply_of_ne hy, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (⟨k, i⟩ : Σ k, Fin (n k))) h
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (⟨k, j⟩ : Σ k, Fin (n k))) h

/-- Reassembling the diagonal blocks: `∑ k, P k * D k * Q k = blockDiagonal' D`. -/
theorem sum_blockEmbed_mul_mul_blockProj (D : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) :
    ∑ k, blockEmbed n k * D k * blockProj n k = Matrix.blockDiagonal' D := by
  ext x y
  obtain ⟨kx, ix⟩ := x
  obtain ⟨ky, iy⟩ := y
  simp only [Matrix.sum_apply]
  by_cases hxy : kx = ky
  · subst hxy
    rw [blockDiagonal'_apply_eq]
    rw [Finset.sum_eq_single kx]
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single iy]
      · rw [Finset.sum_eq_single ix]
        · simp [blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
        · intro b _ hb
          rw [blockEmbed_apply_fst_eq_of_ne hb.symm, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ ix) h
      · intro a _ ha
        simp only [blockProj, Matrix.transpose_apply]
        rw [blockEmbed_apply_fst_eq_of_ne ha.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ iy) h
    · intro k _ hk
      have hne : kx ≠ k := hk.symm
      simp only [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      simp [blockEmbed_apply_of_fst_ne (x := (⟨kx, ix⟩ : Σ k, Fin (n k))) hne]
    · intro h
      exact absurd (Finset.mem_univ kx) h
  · rw [blockDiagonal'_apply_ne D ix iy hxy]
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hk : kx = k
    · have hne : ky ≠ k := fun heq => hxy (hk.trans heq.symm)
      simp only [blockProj, Matrix.transpose_apply]
      rw [blockEmbed_apply_of_fst_ne (x := (⟨ky, iy⟩ : Σ k, Fin (n k))) hne, mul_zero]
    · have hne : kx ≠ k := hk
      simp [blockEmbed_apply_of_fst_ne (x := (⟨kx, ix⟩ : Σ k, Fin (n k))) hne]

end Embed

section Strict

variable {α : Type*} [LinearOrder α]

/-- Strictly block upper triangular for the block labelling `b`: entries whose column block
label is at most their row block label vanish. -/
def StrictBlockTriangular (b : o → α) (M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) : Prop :=
  ∀ ⦃x y⦄, b y.1 ≤ b x.1 → M x y = 0

variable {b : o → α}

omit [Fintype o] [DecidableEq o] in
theorem strictBlockTriangular_of_blockTriangular_of_blockDiag'_eq_zero
    (hb : Function.Injective b) {M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hM : M.BlockTriangular fun x => b x.1) (hd : ∀ k, M.blockDiag' k = 0) :
    StrictBlockTriangular b M := by
  rintro ⟨kx, ix⟩ ⟨ky, iy⟩ hxy
  rcases hxy.lt_or_eq with hlt | heq
  · exact hM hlt
  · obtain rfl : ky = kx := hb heq
    have h2 : M.blockDiag' ky ix iy = 0 := by rw [hd ky]; simp
    rwa [blockDiag'_apply] at h2

omit [Fintype o] in
theorem StrictBlockTriangular.sub_blockDiagonal'_blockDiag' (hb : Function.Injective b)
    {M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hM : M.BlockTriangular fun x => b x.1) :
    StrictBlockTriangular b (M - Matrix.blockDiagonal' M.blockDiag') := by
  have hdiag : (Matrix.blockDiagonal' M.blockDiag').BlockTriangular fun x => b x.1 := by
    rintro ⟨kx, ix⟩ ⟨ky, iy⟩ hlt
    have hne : kx ≠ ky := by
      rintro rfl
      exact absurd hlt (lt_irrefl _)
    exact Matrix.blockDiagonal'_apply_ne M.blockDiag' ix iy hne
  refine strictBlockTriangular_of_blockTriangular_of_blockDiag'_eq_zero hb (hM.sub hdiag) ?_
  intro k
  simp

end Strict

section Nilpotency

variable {r : ℕ} {b : o → Fin r}

/-- Auxiliary entrywise bound for a word evaluation of strictly block upper-triangular
matrices: `m` letters move the block label up by at least `m`. -/
theorem entry_evalWord_eq_zero_of_lt
    {R : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hR : ∀ i, StrictBlockTriangular b (R i)) :
    ∀ (w : List (Fin d)) (x y : Σ k, Fin (n k)),
      (b y.1 : ℕ) < (b x.1 : ℕ) + w.length → evalWord R w x y = 0 := by
  intro w
  induction w with
  | nil =>
      intro x y h
      simp only [List.length_nil, Nat.add_zero] at h
      have hxy : x ≠ y := by
        rintro rfl
        exact absurd h (lt_irrefl _)
      simp [evalWord, hxy]
  | cons i w' ih =>
      intro x y h
      simp only [List.length_cons] at h
      simp only [evalWord, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hzx : b z.1 ≤ b x.1
      · rw [hR i hzx, zero_mul]
      · have hzx' : (b x.1 : ℕ) < (b z.1 : ℕ) := Fin.lt_def.mp (not_le.mp hzx)
        have hzy : (b y.1 : ℕ) < (b z.1 : ℕ) + w'.length := by omega
        rw [ih z y hzy, mul_zero]

/-- A product of `r` strictly block upper-triangular matrices whose block labels take at most
`r` values vanishes (`eq:p5-main-nilpotency`). -/
theorem evalWord_eq_zero_of_strictBlockTriangular
    {R : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hR : ∀ i, StrictBlockTriangular b (R i)) (w : List (Fin d)) (hw : r ≤ w.length) :
    evalWord R w = 0 := by
  ext x y
  have hy : (b y.1 : ℕ) < r := (b y.1).isLt
  exact entry_evalWord_eq_zero_of_lt hR w x y (by omega)

end Nilpotency

end Matrix
