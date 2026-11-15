/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import TNLean.MPS.Preparation.MatrixPolar
import TNLean.MPS.Preparation.IsometryTree

/-!
# Isometric completions at a binary polar merge

An arbitrary rectangular matrix with at least as many rows as columns factors as an isometry
times its positive polar factor, even when it is not injective. Gram equality and the pinned
unitary-extension theorem give the completion. If the matrix already lies in the range of
an isometry `J`, the completion can be chosen inside that range.

Consequently two independently chosen child isometries admit a full-domain parent merge.
This is the finite-dimensional completion needed for an inhomogeneous version of the tree
in arXiv:2307.01696, eq. (16). It assumes no common coordinate support. It does not by itself
identify the coefficients of an arbitrary chain with the resulting tree or compile that
position-dependent tree into measurement rounds.
-/

open Matrix
open scoped ComplexOrder

namespace Matrix

/-- A rectangular matrix admits a full-domain isometric polar factor when the output
dimension is at least the input dimension. No injectivity is assumed. -/
theorem exists_isometry_mul_polarPos_eq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : Matrix m n ℂ)
    (hdim : Fintype.card n ≤ Fintype.card m) :
    ∃ X : Matrix m n ℂ, X.IsIsometry ∧ X * polarPos B = B := by
  classical
  obtain ⟨j⟩ : Nonempty (n ↪ m) := Function.Embedding.nonempty_of_card_le hdim
  let J : Matrix m n ℂ := (1 : Matrix m m ℂ).submatrix id j
  have hJ : Jᴴ * J = 1 := by
    rw [show Jᴴ = (1 : Matrix m m ℂ).submatrix j id by simp [J]]
    change (1 : Matrix m m ℂ).submatrix j (Equiv.refl m) *
      (1 : Matrix m m ℂ).submatrix (Equiv.refl m) j = 1
    rw [Matrix.submatrix_mul_equiv]
    simpa only [Matrix.one_mul] using Matrix.submatrix_one (α := ℂ) j j.injective
  have hGram : Bᴴ * B = (J * polarPos B)ᴴ * (J * polarPos B) := by
    symm
    rw [conjTranspose_mul, (posSemidef_polarPos B).isHermitian.eq]
    calc polarPos B * Jᴴ * (J * polarPos B) = polarPos B * (Jᴴ * J) * polarPos B := by
          simp only [Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [hJ, Matrix.mul_one, polarPos_mul_polarPos]
  obtain ⟨U, hU⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq B (J * polarPos B) hGram
  have hUi : (U : Matrix m m ℂ).IsIsometry := by
    change (U : Matrix m m ℂ)ᴴ * (U : Matrix m m ℂ) = 1
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.property
  refine ⟨(U : Matrix m m ℂ) * J, Matrix.IsIsometry.mul _ _ hUi hJ, ?_⟩
  rw [Matrix.mul_assoc]
  exact hU.symm

/-- If `B` lies in the range of an isometry `J`, its isometric polar completion can be
chosen as `J W`, where `W` is an isometry on the smaller output space. -/
theorem exists_isometry_polarMerge_of_range {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (J : Matrix m n ℂ) (hJ : J.IsIsometry) (B : Matrix m p ℂ)
    (hsupport : J * Jᴴ * B = B) (hdim : Fintype.card p ≤ Fintype.card n) :
    ∃ W : Matrix n p ℂ, W.IsIsometry ∧ (J * W).IsIsometry ∧
      (J * W) * polarPos B = B := by
  classical
  have hGram : (Jᴴ * B)ᴴ * (Jᴴ * B) = Bᴴ * B := by
    calc (Jᴴ * B)ᴴ * (Jᴴ * B) = Bᴴ * (J * Jᴴ * B) := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [hsupport]
  have hP : polarPos (Jᴴ * B) = polarPos B := by unfold polarPos; rw [hGram]
  obtain ⟨W, hW, hWP⟩ := exists_isometry_mul_polarPos_eq (Jᴴ * B) hdim
  refine ⟨W, hW, Matrix.IsIsometry.mul _ _ hJ hW, ?_⟩
  rw [Matrix.mul_assoc, ← hP, hWP, ← Matrix.mul_assoc, hsupport]

end Matrix

namespace MPSPreparation

/-- Two child isometries admit a full isometric binary merge for every compressed parent
matrix. The child maps may be unrelated and the compressed matrix need not be injective.
Source: the binary polar step of arXiv:2307.01696, eq. (16), with general virtual ranges. -/
theorem exists_isometry_binaryPolarMerge {d χ n₁ n₂ : ℕ} (hχ : 0 < χ)
    (L : Matrix (Fin n₁ → Fin d) (Fin χ) ℂ)
    (R : Matrix (Fin n₂ → Fin d) (Fin χ) ℂ)
    (hL : L.IsIsometry) (hR : R.IsIsometry)
    (C : Matrix (Fin (MPSTensor.blockPhysDim χ 2)) (Fin χ) ℂ) :
    ∃ W : Matrix (Fin (MPSTensor.blockPhysDim χ 2)) (Fin χ) ℂ,
      W.IsIsometry ∧
      (IsometryTree.joinMatrix L R * W) * polarPos (IsometryTree.joinMatrix L R * C) =
        IsometryTree.joinMatrix L R * C := by
  let J := IsometryTree.joinMatrix L R
  have hJ : J.IsIsometry := IsometryTree.isIsometry_joinMatrix hL hR
  have hsupp : J * Jᴴ * (J * C) = J * C := by
    calc J * Jᴴ * (J * C) = J * (Jᴴ * J) * C := by simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hJ, Matrix.mul_one]
  have hdim : Fintype.card (Fin χ) ≤ Fintype.card (Fin (MPSTensor.blockPhysDim χ 2)) := by
    change χ ≤ χ ^ 2
    simpa only [pow_two] using Nat.le_mul_of_pos_right χ hχ
  obtain ⟨W, hW, _, hWP⟩ := Matrix.exists_isometry_polarMerge_of_range J hJ (J * C) hsupp hdim
  exact ⟨W, hW, hWP⟩

end MPSPreparation
