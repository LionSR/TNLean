/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixIdempotentFactorization
import Mathlib.Data.Matrix.Basis

/-!
# Exact matrix-unit factorizations

A system of matrix units acting on a finite-dimensional vector space has an
exact rectangular factorization. The multiplicity is the rank of one diagonal
matrix unit. No preservation of adjoints or of the ambient identity is needed.

This is the algebraic decomposition used in Garre-Rubio, Lootens and Molnár,
arXiv:2203.12563v3, Appendix A.
-/

open scoped Matrix

namespace Matrix

/-- A matrix-unit system factors through equal-dimensional coordinate spaces.
The factorization is exact even when its support is a proper idempotent. -/
theorem exists_matrixUnitFactorization
    {K : Type*} [Field K] {n : Type*} [DecidableEq n] {D : ℕ}
    (E : n → n → Matrix (Fin D) (Fin D) K)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (i₀ : n) :
    ∃ (A : n → Matrix (Fin D) (Fin (E i₀ i₀).rank) K)
      (B : n → Matrix (Fin (E i₀ i₀).rank) (Fin D) K),
      (∀ i j, B i * A j = if i = j then 1 else 0) ∧
      (∀ i j, A i * B j = E i j) := by
  classical
  have hP : E i₀ i₀ * E i₀ i₀ = E i₀ i₀ := by simp [hE]
  obtain ⟨C, H, hHC, hCH⟩ := exists_rankFactorization_of_idempotent (E i₀ i₀) hP
  have hPC : E i₀ i₀ * C = C := by
    calc
      E i₀ i₀ * C = (C * H) * C :=
        congrArg (fun T : Matrix (Fin D) (Fin D) K => T * C) hCH.symm
      _ = C := by rw [Matrix.mul_assoc, hHC, Matrix.mul_one]
  refine ⟨fun i => E i i₀ * C, fun j => H * E i₀ j, ?_, ?_⟩
  · intro i j
    calc
      (H * E i₀ i) * (E j i₀ * C) = H * (E i₀ i * E j i₀) * C := by
        simp only [Matrix.mul_assoc]
      _ = if i = j then 1 else 0 := by
        rw [hE]
        by_cases hij : i = j
        · simp only [hij, ite_true, Matrix.mul_assoc, hPC, hHC]
        · simp [hij]
  · intro i j
    calc
      (E i i₀ * C) * (H * E i₀ j) = (E i i₀ * (C * H)) * E i₀ j := by
        simp only [Matrix.mul_assoc]
      _ = E i j := by simp [hCH, hE]

/-- Reassembling the columns of a rectangular factorization gives the usual
sum over multiplicity blocks. -/
theorem sum_multiplicityBlocks_mul
    {K n m : Type*} [CommSemiring K] [Fintype n] [Fintype m] {D : ℕ}
    (A : n → Matrix (Fin D) m K) (B : n → Matrix m (Fin D) K)
    (M : Matrix n n K) :
    (∑ μ : m, (of fun a i => A i a μ) * M * (of fun j b => B j μ b)) =
      ∑ i : n, ∑ j : n, M i j • (A i * B j) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, of_apply, Finset.sum_mul,
    Finset.mul_sum, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- A system of matrix units is a sum of mutually biorthogonal copies of the
standard representation, with multiplicity equal to a diagonal unit's rank. -/
theorem exists_matrixUnitBlocks
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (E : n → n → Matrix (Fin D) (Fin D) K)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (i₀ : n) :
    ∃ (W : Fin (E i₀ i₀).rank → Matrix (Fin D) n K)
      (V : Fin (E i₀ i₀).rank → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M : Matrix n n K, ∑ μ, W μ * M * V μ =
        ∑ i, ∑ j, M i j • E i j) := by
  classical
  obtain ⟨A, B, hBA, hAB⟩ := exists_matrixUnitFactorization E hE i₀
  let W := fun μ => of fun a i => A i a μ
  let V := fun μ => of fun i a => B i μ a
  refine ⟨W, V, ?_, ?_⟩
  · intro μ ν
    ext i j
    have hentry := congrArg (fun T => T μ ν) (hBA i j)
    change (B i * A j) μ ν = _
    rw [hentry]
    by_cases hij : i = j <;> by_cases hμν : μ = ν <;>
      simp [hij, hμν, Matrix.one_apply]
  · intro M
    rw [sum_multiplicityBlocks_mul]
    simp only [hAB]

/-- A multiplicative linear map on a full matrix algebra is an exact finite
sum of biorthogonal standard blocks. It need not preserve the identity. -/
theorem exists_multiplicativeLinearMap_blocks
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (ρ : Matrix n n K →ₗ[K] Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) (i₀ : n) :
    ∃ (m : ℕ) (W : Fin m → Matrix (Fin D) n K) (V : Fin m → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M, ρ M = ∑ μ, W μ * M * V μ) := by
  classical
  let E := fun i j => ρ (single i j 1)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    dsimp [E]
    rw [← hρ]
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk]
  obtain ⟨W, V, hVW, hsum⟩ := exists_matrixUnitBlocks E hE i₀
  refine ⟨(E i₀ i₀).rank, W, V, hVW, fun M => ?_⟩
  rw [hsum]
  conv_lhs => rw [matrix_eq_sum_single M]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ρ (single i j (M i j)) = M i j • ρ (single i j 1)
  rw [← map_smul]
  congr 1
  simp

end Matrix
