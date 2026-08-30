/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TwoInjectiveComparison.Basic

/-!
# Composition of the end operations in Lemma 5

The comparison of the two injective end blocks in Lemma 5 produces one matrix `X` with

\[
  O_1(A_{1,\nu})=\sum_\mu X_{\mu\nu}A_{1,\mu},\qquad
  O_3(A_{3,\mu})=\sum_\nu X_{\mu\nu}A_{3,\nu}.
\]

This file records the final composition argument of the lemma.  Linear independence makes `X`
unique.  Composing two operations on the left gives the product of their virtual matrices in the
same order.  On the right the underlying physical operations compose in the reverse order; after
transposition this is precisely the ordinary product of `O₃ᵀ` operations.  Thus the assignments
`O₁ ↦ X` and `O₃ᵀ ↦ X` are multiplicative.  The source writes the equivalent second assignment as
`O₃ ↦ Xᵀ`.  No injectivity beyond linear independence of the genuine end family is used.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Lemma 5, especially the end-factor equations and
  composition conclusion at lines 2213--2252 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {K W : Type*} [Fintype K] [AddCommMonoid W] [Module ℂ W]

/-- The left-end operation `O₁` realizes the virtual operation `X`.

The columns of `X` give the coefficients of `O₁(A₁)`, in the first displayed end-factor equation
of Lemma 5.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsO1VirtualOperation (A₁ : K → W) (O₁ : Module.End ℂ W) (X : Matrix K K ℂ) : Prop :=
  ∀ ν : K, O₁ (A₁ ν) = ∑ μ : K, X μ ν • A₁ μ

/-- The right-end operation `O₃`, read in the source's transposed orientation, realizes `X`.

The rows of `X` give the coefficients of `O₃(A₃)`.  The source writes the resulting map as
`O₃ ↦ Xᵀ`, equivalently `O₃ᵀ ↦ X`; since transposition reverses products, multiplication of the
transposed operations is represented below by reverse composition of the underlying `O₃`
operations.  Thus this predicate records the transposed orientation of the source equation; it
does not choose a basis or construct a transpose on the abstract endomorphism space.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsO3TransposeVirtualOperation
    (A₃ : K → W) (O₃ : Module.End ℂ W) (X : Matrix K K ℂ) : Prop :=
  ∀ μ : K, O₃ (A₃ μ) = ∑ ν : K, X μ ν • A₃ ν

private theorem coefficientFamily_eq_of_sum_smul_eq
    {J : Type*} (A : K → W) (hA : LinearIndependent ℂ A)
    (c d : J → K → ℂ)
    (h : ∀ j : J, (∑ k : K, c j k • A k) = ∑ k : K, d j k • A k) :
    c = d := by
  classical
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := W)
  funext j k
  have hzero : (∑ i : K, (c j i - d j i) • A i) = 0 := by
    rw [show (∑ i : K, (c j i - d j i) • A i) =
        (∑ i : K, c j i • A i) - ∑ i : K, d j i • A i by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ sub_smul (c j i) (d j i) (A i)]
    rw [h j, sub_self]
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hA) _ hzero k)

/-- The virtual operation in an `O₁` realization is unique.

This is the uniqueness used in the final composition sentence of Lemma 5.  It assumes only linear
independence of the genuine left end family.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO1VirtualOperation.virtualOperation_eq
    {A₁ : K → W} (hA₁ : LinearIndependent ℂ A₁)
    {O₁ : Module.End ℂ W} {X Y : Matrix K K ℂ}
    (hX : IsO1VirtualOperation A₁ O₁ X) (hY : IsO1VirtualOperation A₁ O₁ Y) :
    X = Y := by
  have hcoeff : (fun ν μ ↦ X μ ν) = fun ν μ ↦ Y μ ν :=
    coefficientFamily_eq_of_sum_smul_eq A₁ hA₁ _ _ fun ν ↦ by
      rw [← hX ν, ← hY ν]
  exact Matrix.ext fun μ ν ↦ congrFun (congrFun hcoeff ν) μ

/-- The virtual operation in an `O₃ᵀ` realization is unique.

This is the right-end uniqueness used in the final composition sentence of Lemma 5.  It assumes
only linear independence of the genuine right end family.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO3TransposeVirtualOperation.virtualOperation_eq
    {A₃ : K → W} (hA₃ : LinearIndependent ℂ A₃)
    {O₃ : Module.End ℂ W} {X Y : Matrix K K ℂ}
    (hX : IsO3TransposeVirtualOperation A₃ O₃ X)
    (hY : IsO3TransposeVirtualOperation A₃ O₃ Y) :
    X = Y := by
  have hcoeff : (fun μ ν ↦ X μ ν) = fun μ ν ↦ Y μ ν :=
    coefficientFamily_eq_of_sum_smul_eq A₃ hA₃ _ _ fun μ ↦ by
      rw [← hX μ, ← hY μ]
  exact Matrix.ext fun μ ν ↦ congrFun (congrFun hcoeff μ) ν

/-- Composition of two `O₁` realizations realizes the matrix product in the same order.

This is the left half of the phrase "by composition" in the last sentence of the proof of
Lemma 5.

Source: arXiv:1804.04964, Lemma 5, line 2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO1VirtualOperation.mul
    {A₁ : K → W} {O₁ P₁ : Module.End ℂ W} {X Y : Matrix K K ℂ}
    (hX : IsO1VirtualOperation A₁ O₁ X) (hY : IsO1VirtualOperation A₁ P₁ Y) :
    IsO1VirtualOperation A₁ (O₁ * P₁) (X * Y) := by
  classical
  intro ν
  rw [Module.End.mul_apply, hY ν, map_sum]
  simp_rw [map_smul, hX, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [mul_comm (Y κ ν) (X μ κ)]

/-- Composition in the `O₃ᵀ` orientation realizes the matrix product in the same order.

If `O₃` realizes `X` and `P₃` realizes `Y`, then the underlying right-end operations occur as
`P₃ * O₃`.  This is exactly the transpose rule
`O₃ᵀ * P₃ᵀ = (P₃ * O₃)ᵀ`, and is the right half of the phrase "by composition" in Lemma 5.

Source: arXiv:1804.04964, Lemma 5, line 2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO3TransposeVirtualOperation.mul
    {A₃ : K → W} {O₃ P₃ : Module.End ℂ W} {X Y : Matrix K K ℂ}
    (hX : IsO3TransposeVirtualOperation A₃ O₃ X)
    (hY : IsO3TransposeVirtualOperation A₃ P₃ Y) :
    IsO3TransposeVirtualOperation A₃ (P₃ * O₃) (X * Y) := by
  classical
  intro μ
  rw [Module.End.mul_apply, hX μ, map_sum]
  simp_rw [map_smul, hY, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [Finset.sum_smul]

/-- Uniqueness turns composition of the `O₁` operations into multiplication of their extracted
virtual operations.

Source: arXiv:1804.04964, Lemma 5, line 2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO1VirtualOperation.eq_mul_of_mul
    {A₁ : K → W} (hA₁ : LinearIndependent ℂ A₁)
    {O₁ P₁ : Module.End ℂ W} {X Y Z : Matrix K K ℂ}
    (hX : IsO1VirtualOperation A₁ O₁ X) (hY : IsO1VirtualOperation A₁ P₁ Y)
    (hZ : IsO1VirtualOperation A₁ (O₁ * P₁) Z) :
    Z = X * Y :=
  IsO1VirtualOperation.virtualOperation_eq hA₁ hZ (hX.mul hY)

/-- Uniqueness turns multiplication of the transposed right-end operations into multiplication of
their extracted virtual operations.

Source: arXiv:1804.04964, Lemma 5, line 2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem IsO3TransposeVirtualOperation.eq_mul_of_mul
    {A₃ : K → W} (hA₃ : LinearIndependent ℂ A₃)
    {O₃ P₃ : Module.End ℂ W} {X Y Z : Matrix K K ℂ}
    (hX : IsO3TransposeVirtualOperation A₃ O₃ X)
    (hY : IsO3TransposeVirtualOperation A₃ P₃ Y)
    (hZ : IsO3TransposeVirtualOperation A₃ (P₃ * O₃) Z) :
    Z = X * Y :=
  IsO3TransposeVirtualOperation.virtualOperation_eq hA₃ hZ (hX.mul hY)

/-- The two-end comparison stated directly for the paper's physical operations `O₁` and `O₃ᵀ`.

If the two modified end contractions agree and the two genuine end families are linearly
independent, there is one unique `X` simultaneously realized by `O₁` and by the right operation in
the `O₃ᵀ` orientation.  This is `existsUnique_virtualOperation_of_endPair` with the modified
families written as the actions of the physical operations themselves.

Source: arXiv:1804.04964, Lemma 5, lines 2213--2252 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_virtualOperation_of_O1_O3Transpose
    {V₁ V₃ : Type*} (A₁ : K → V₁ → ℂ) (A₃ : K → V₃ → ℂ)
    (O₁ : Module.End ℂ (V₁ → ℂ)) (O₃ : Module.End ℂ (V₃ → ℂ))
    (hA₁ : LinearIndependent ℂ (fun μ : K ↦ (A₁ μ : V₁ → ℂ)))
    (hA₃ : LinearIndependent ℂ (fun μ : K ↦ (A₃ μ : V₃ → ℂ)))
    (hcontract : ∀ (p₁ : V₁) (p₃ : V₃),
      (∑ μ : K, O₁ (A₁ μ) p₁ * A₃ μ p₃) =
        ∑ ν : K, A₁ ν p₁ * O₃ (A₃ ν) p₃) :
    ∃! X : Matrix K K ℂ,
      IsO1VirtualOperation A₁ O₁ X ∧ IsO3TransposeVirtualOperation A₃ O₃ X := by
  obtain ⟨X, hX, hunique⟩ := existsUnique_virtualOperation_of_endPair
    A₁ (fun μ ↦ O₁ (A₁ μ)) A₃ (fun μ ↦ O₃ (A₃ μ)) hA₁ hA₃ hcontract
  refine ⟨X, ?_, ?_⟩
  · constructor
    · intro ν
      funext p₁
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hX.1 ν p₁
    · intro μ
      funext p₃
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hX.2 μ p₃
  · intro Y hY
    apply hunique
    constructor
    · intro ν p₁
      have h := congrFun (hY.1 ν) p₁
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
    · intro μ p₃
      have h := congrFun (hY.2 μ) p₃
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end PEPS
end TNLean
