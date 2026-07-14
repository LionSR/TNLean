/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalCF

/-!
# Coisometries from orthogonal vertical sectors

For a finite family of isometries with mutually orthogonal ranges, this file
forms the block-row coisometry whose rows are their adjoints.  If a tensor
intertwines each isometry with a sector tensor, conjugation by this coisometry
is the direct sum of the sector tensors.  A literal sum over the sector
corners gives the reverse reconstruction identity.

These matrix identities isolate the finite-dimensional construction needed for
the coisometry and direct-sum conclusion of arXiv:1606.00608,
Proposition 4.13, lines 1863--1870.  The reverse identity proved here is the
conditional consequence of an assumed literal sum over the sector corners.

## Main definitions

* `Matrix.sigmaBlockRow`: the block row formed from the adjoints of a family
  of rectangular matrices.

## Main results

* `Matrix.sigmaBlockRow_isCoisometry`: orthogonal isometries give a
  coisometry.
* `Matrix.sigmaBlockRow_conjugation`: sector intertwinings give a
  block-diagonal conjugation identity.
* `Matrix.sigmaBlockRow_reconstruction`: a sum of sector corners equals the
  reverse block-diagonal compression.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1863--1870
-/

open scoped Matrix BigOperators

namespace Matrix

variable {r d s : ℕ} {dim : Fin r → ℕ}

/-- The block row whose sector indexed by `k` is the adjoint of `W k`.

For $W_k : \mathbb C^{D_k}\to\mathbb C^d$, this is the map
$U=\bigl(W_0^\dagger,\ldots,W_{r-1}^\dagger\bigr)^\mathsf T$ from
$\mathbb C^d$ to $\bigoplus_k\mathbb C^{D_k}$.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
noncomputable def sigmaBlockRow
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    Matrix ((k : Fin r) × Fin (dim k)) (Fin d) ℂ :=
  fun x a ↦ (W x.1)ᴴ x.2 a

@[simp]
theorem sigmaBlockRow_conjTranspose
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    (sigmaBlockRow W)ᴴ = fun a x ↦ W x.1 a x.2 := by
  ext a x
  simp [sigmaBlockRow]

/-- Left multiplication of a block row by a block-diagonal matrix acts on
each row sector separately. -/
theorem blockDiagonal'_mul_sigmaBlockRow
    (B : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    blockDiagonal' B * sigmaBlockRow W =
      fun x a ↦ (B x.1 * (W x.1)ᴴ) x.2 a := by
  classical
  ext ⟨k, x⟩ a
  simp only [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp [sigmaBlockRow]
  · intro l hl
    apply Finset.sum_eq_zero
    intro y hy
    rw [blockDiagonal'_apply_ne B x y hl.symm]
    exact zero_mul _

/-- Multiplication of the adjoint block row by a matrix with the same row
sectors is the sum of the corresponding sector products. -/
theorem sigmaBlockRow_conjTranspose_mul
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (C : (k : Fin r) → Matrix (Fin (dim k)) (Fin d) ℂ) :
    (sigmaBlockRow W)ᴴ *
        (show Matrix ((k : Fin r) × Fin (dim k)) (Fin d) ℂ from
          fun x a ↦ C x.1 x.2 a) =
      ∑ k, W k * C k := by
  classical
  ext a b
  simp [Matrix.sum_apply, Matrix.mul_apply, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]

/-- The Gram matrix of a block row is block diagonal when the ranges of its
constituent isometries are pairwise orthogonal. -/
theorem sigmaBlockRow_mul_conjTranspose
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0) :
    sigmaBlockRow W * (sigmaBlockRow W)ᴴ =
      blockDiagonal' (fun k ↦ (W k)ᴴ * W k) := by
  classical
  ext ⟨k, x⟩ ⟨l, y⟩
  by_cases hkl : k = l
  · subst l
    simp [sigmaBlockRow, Matrix.mul_apply]
  · rw [blockDiagonal'_apply_ne _ _ _ hkl]
    have h := congrFun (congrFun (horth k l hkl) x) y
    simpa [sigmaBlockRow, Matrix.mul_apply] using h

/-- The block row of pairwise orthogonal isometries is a coisometry.

This is the identity $UU^\dagger=I$ in the coisometry conclusion of
arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem sigmaBlockRow_isCoisometry
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (W k)ᴴ * W k = 1)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0) :
    sigmaBlockRow W * (sigmaBlockRow W)ᴴ = 1 := by
  classical
  rw [sigmaBlockRow_mul_conjTranspose W horth]
  simp_rw [hiso]
  exact blockDiagonal'_one

/-- Intertwining on pairwise orthogonal sectors makes conjugation by their
block-row coisometry block diagonal.

This is the identity $U\widetilde M_vU^\dagger=\bigoplus_k B_k^v$ in
arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem sigmaBlockRow_conjugation
    (T : Fin s → Matrix (Fin d) (Fin d) ℂ)
    (B : (k : Fin r) → Fin s → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (W k)ᴴ * W k = 1)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0)
    (hinter : ∀ k v, T v * W k = W k * B k v) :
    ∀ v, sigmaBlockRow W * T v * (sigmaBlockRow W)ᴴ =
      blockDiagonal' (fun k ↦ B k v) := by
  classical
  intro v
  ext ⟨k, x⟩ ⟨l, y⟩
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, sigmaBlockRow, sigmaBlockRow_conjTranspose]
  conv_lhs =>
    enter [2, a]
    rw [show (∑ b, T v a b * W l b y) = (W l * B l v) a y by
      exact congrFun (congrFun (hinter l v) a) y]
  change ((W k)ᴴ * (W l * B l v)) x y = _
  rw [← Matrix.mul_assoc]
  by_cases hkl : k = l
  · subst l
    rw [hiso k, one_mul, blockDiagonal'_apply_eq]
  · rw [horth k l hkl, Matrix.zero_mul, blockDiagonal'_apply_ne _ _ _ hkl]
    rfl

/-- A literal sum of orthogonal sector corners is reconstructed by the
block-row coisometry and the corresponding block-diagonal matrix.

This conditional reverse identity follows directly from the assumed literal
sector decomposition; it is not a separate assertion attributed to the source. -/
theorem sigmaBlockRow_reconstruction
    (T : Fin s → Matrix (Fin d) (Fin d) ℂ)
    (B : (k : Fin r) → Fin s → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hreconstruct : ∀ v, T v = ∑ k, W k * B k v * (W k)ᴴ) :
    ∀ v, T v =
      (sigmaBlockRow W)ᴴ * blockDiagonal' (fun k ↦ B k v) * sigmaBlockRow W := by
  classical
  intro v
  rw [hreconstruct v, Matrix.mul_assoc,
    blockDiagonal'_mul_sigmaBlockRow (fun k ↦ B k v) W,
    sigmaBlockRow_conjTranspose_mul W (fun k ↦ B k v * (W k)ᴴ)]
  simp_rw [← Matrix.mul_assoc]

end Matrix
