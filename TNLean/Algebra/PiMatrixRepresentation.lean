/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixUnitFactorization
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.GroupWithZero.Pi

/-!
# Exact representations of finite products of matrix algebras

A multiplicative linear map from a finite product of full matrix algebras to
matrices is a sum of biorthogonal standard blocks. The sum of the block
supports is the image of the source identity, which need not be the ambient
identity. Zero-dimensional source factors and zero multiplicities are allowed.
No star-preserving hypothesis occurs.

This proves the finite-dimensional representation decomposition used in
Garre-Rubio, Lootens and Molnár, arXiv:2203.12563v3, Appendix A.
-/

open scoped Matrix

namespace Matrix

/-- The full-matrix representation decomposition also covers an empty matrix
index type, in which case its multiplicity can be chosen to be zero. -/
theorem exists_multiplicativeLinearMap_blocks_of_fintype
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (ρ : Matrix n n K →ₗ[K] Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) :
    ∃ (m : ℕ) (W : Fin m → Matrix (Fin D) n K) (V : Fin m → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M, ρ M = ∑ μ, W μ * M * V μ) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    refine ⟨0, Fin.elim0, Fin.elim0, fun μ => Fin.elim0 μ, fun M => ?_⟩
    have hM : M = 0 := Subsingleton.elim _ _
    simp [hM]
  | inr hn =>
    exact exists_multiplicativeLinearMap_blocks ρ hρ (Classical.choice hn)

/-- Each member of a biorthogonal family is supported on its total
idempotent, on both sides. -/
theorem biorthogonal_sum_support
    {K m n d : Type*} [Semiring K] [Fintype m] [Fintype n] [Fintype d]
    [DecidableEq m] [DecidableEq n]
    (W : m → Matrix d n K) (V : m → Matrix n d K)
    (hVW : ∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) (μ : m) :
    (∑ ν, W ν * V ν) * W μ = W μ ∧
      V μ * (∑ ν, W ν * V ν) = V μ := by
  constructor
  · rw [Matrix.sum_mul, Finset.sum_eq_single μ]
    · rw [Matrix.mul_assoc, hVW, ite_eq_left rfl, Matrix.mul_one]
    · intro ν _ hν
      rw [Matrix.mul_assoc, hVW, ite_eq_right hν, Matrix.mul_zero]
    · simp
  · rw [Matrix.mul_sum, Finset.sum_eq_single μ]
    · rw [← Matrix.mul_assoc, hVW, ite_eq_left rfl, Matrix.one_mul]
    · intro ν _ hν
      rw [← Matrix.mul_assoc, hVW, ite_eq_right (Ne.symm hν), Matrix.zero_mul]
    · simp

/-- Every multiplicative linear representation of a finite product of full
matrix algebras splits exactly into biorthogonal copies of the standard
representations. The total support is the image of the identity, with no
unitality or preservation of adjoints required. -/
theorem exists_piMatrix_blocks
    {K C : Type*} [Field K] [Fintype C]
    (δ : C → ℕ) {D : ℕ}
    (ρ : (∀ c, Matrix (Fin (δ c)) (Fin (δ c)) K) →ₗ[K]
      Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) :
    ∃ (m : C → ℕ)
      (W : ∀ c, Fin (m c) → Matrix (Fin D) (Fin (δ c)) K)
      (V : ∀ c, Fin (m c) → Matrix (Fin (δ c)) (Fin D) K),
      (∀ c μ ν, V c μ * W c ν = if μ = ν then 1 else 0) ∧
      (∀ c d, c ≠ d → ∀ μ ν, V c μ * W d ν = 0) ∧
      (∀ M, ρ M = ∑ c, ∑ μ, W c μ * M c * V c μ) ∧
      ρ 1 = ∑ c, ∑ μ, W c μ * V c μ := by
  classical
  let ρc := fun c => ρ.comp
    (LinearMap.single K (fun c => Matrix (Fin (δ c)) (Fin (δ c)) K) c)
  have hρc (c : C) : ∀ M N, ρc c (M * N) = ρc c M * ρc c N := by
    intro M N
    change ρ (Pi.single c (M * N)) = ρ (Pi.single c M) * ρ (Pi.single c N)
    rw [Pi.single_mul, hρ]
  choose m W V hVW hsum using
    fun c => exists_multiplicativeLinearMap_blocks_of_fintype (ρc c) (hρc c)
  have hsupport (c : C) : ρc c 1 = ∑ μ, W c μ * V c μ := by
    simpa using hsum c 1
  have hleft (c : C) (μ : Fin (m c)) : ρc c 1 * W c μ = W c μ := by
    rw [hsupport]
    exact (biorthogonal_sum_support (W c) (V c) (hVW c) μ).1
  have hright (c : C) (μ : Fin (m c)) : V c μ * ρc c 1 = V c μ := by
    rw [hsupport]
    exact (biorthogonal_sum_support (W c) (V c) (hVW c) μ).2
  have horth (c d : C) (hcd : c ≠ d) : ρc c 1 * ρc d 1 = 0 := by
    change ρ (Pi.single c 1) * ρ (Pi.single d 1) = 0
    rw [← hρ, ← Pi.single_mul_left]
    simp [Pi.single_eq_of_ne hcd]
  have htotal (M : ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) K) :
      ρ M = ∑ c, ∑ μ, W c μ * M c * V c μ := by
    calc
      ρ M = ρ (∑ c, Pi.single c (M c)) := by rw [LinearMap.sum_single_apply]
      _ = ∑ c, ρc c (M c) := by simp [ρc]
      _ = _ := by simp only [hsum]
  refine ⟨m, W, V, hVW, ?_, htotal, ?_⟩
  · intro c d hcd μ ν
    calc
      V c μ * W d ν = (V c μ * ρc c 1) * (ρc d 1 * W d ν) := by
        rw [hright, hleft]
      _ = V c μ * (ρc c 1 * ρc d 1) * W d ν := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [horth c d hcd, Matrix.mul_zero, Matrix.zero_mul]
  · simpa using htotal 1

end Matrix
