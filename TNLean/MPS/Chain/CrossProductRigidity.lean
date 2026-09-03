/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.NormalCommutant
import TNLean.MPS.Chain.OneSidedInverse

/-!
# Cross-product rigidity for matrix families

A family `B` satisfying `B i * A j = A i * B j` with an injective family `A`
is a common scalar multiple of `A`. The same conclusion holds when `A` is normal:
a marked `B` letter is first moved through a word at an injective blocking length.

## Main statements

* `Kraus.IsInjective.eq_smul_of_cross_mul_eq` proves the injective case.
* `Kraus.IsNormal.eq_smul_of_cross_mul_eq` proves the normal case by blocking.

## References

* [arXiv:2502.20257, lines 1255--1325](https://arxiv.org/abs/2502.20257)
-/

open scoped Matrix BigOperators

namespace Kraus

variable {d D : ℕ}

private def evalWordMarkedLast (A B : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [] => 0
  | [i] => B i
  | i :: j :: w => A i * evalWordMarkedLast A B (j :: w)

private theorem mul_evalWord_eq_mul_evalWordMarkedLast
    (A B : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∀ i w, w ≠ [] →
      B i * Kraus.evalWord A w = A i * evalWordMarkedLast A B w := by
  intro i w hw
  induction w generalizing i with
  | nil => exact (hw rfl).elim
  | cons j w ih =>
      cases w with
      | nil => simpa [evalWordMarkedLast] using hcross i j
      | cons k w =>
          calc
            B i * Kraus.evalWord A (j :: k :: w) =
                (B i * A j) * Kraus.evalWord A (k :: w) := by
              rw [Kraus.evalWord_cons, Matrix.mul_assoc]
            _ = (A i * B j) * Kraus.evalWord A (k :: w) := by rw [hcross]
            _ = A i * (B j * Kraus.evalWord A (k :: w)) := by rw [Matrix.mul_assoc]
            _ = A i * (A j * evalWordMarkedLast A B (k :: w)) := by
              rw [ih j (by simp)]
            _ = A i * evalWordMarkedLast A B (j :: k :: w) := rfl

private theorem exists_factor_of_cross_mul_eq_of_isInjective
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsInjective A)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ C : Matrix (Fin D) (Fin D) ℂ, ∀ i, B i = A i * C := by
  let C : Matrix (Fin D) (Fin D) ℂ :=
    ∑ j, Kraus.decompositionMap hA 1 j • B j
  refine ⟨C, fun i ↦ ?_⟩
  calc
    B i = B i * 1 := by rw [Matrix.mul_one]
    _ = B i * ∑ j, Kraus.decompositionMap hA 1 j • A j := by
      rw [Kraus.decompositionMap_sum]
    _ = ∑ j, Kraus.decompositionMap hA 1 j • (B i * A j) := by
      rw [Finset.mul_sum]
      simp only [Matrix.mul_smul]
    _ = ∑ j, Kraus.decompositionMap hA 1 j • (A i * B j) := by
      congr 1
      funext j
      rw [hcross]
    _ = A i * C := by
      simp only [C, Finset.mul_sum, Matrix.mul_smul]

private theorem exists_factor_of_cross_mul_eq_of_isNBlkInjective
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} {N : ℕ}
    (hNpos : 0 < N) (hA : Kraus.IsNBlkInjective A N)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ C : Matrix (Fin D) (Fin D) ℂ, ∀ i, B i = A i * C := by
  let C : Matrix (Fin D) (Fin D) ℂ :=
    ∑ σ : Fin N → Fin d, Kraus.blockDecompositionMap hA 1 σ •
      evalWordMarkedLast A B (List.ofFn σ)
  refine ⟨C, fun i ↦ ?_⟩
  have hword_ne (σ : Fin N → Fin d) : List.ofFn σ ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    omega
  calc
    B i = B i * 1 := by rw [Matrix.mul_one]
    _ = B i * ∑ σ : Fin N → Fin d,
        Kraus.blockDecompositionMap hA 1 σ • Kraus.evalWord A (List.ofFn σ) := by
      rw [Kraus.blockDecompositionMap_sum]
    _ = ∑ σ : Fin N → Fin d, Kraus.blockDecompositionMap hA 1 σ •
        (B i * Kraus.evalWord A (List.ofFn σ)) := by
      rw [Finset.mul_sum]
      simp only [Matrix.mul_smul]
    _ = ∑ σ : Fin N → Fin d, Kraus.blockDecompositionMap hA 1 σ •
        (A i * evalWordMarkedLast A B (List.ofFn σ)) := by
      congr 1
      funext σ
      rw [mul_evalWord_eq_mul_evalWordMarkedLast A B hcross i _ (hword_ne σ)]
    _ = A i * C := by
      simp only [C, Finset.mul_sum, Matrix.mul_smul]

private theorem eq_smul_of_factor_of_cross_mul_eq
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    (hfactor : ∃ C : Matrix (Fin D) (Fin D) ℂ, ∀ i, B i = A i * C)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ δ : ℂ, ∀ i, B i = δ • A i := by
  obtain ⟨C, hC⟩ := hfactor
  have hcomm : ∀ j, C * A j = A j * C := by
    intro j
    obtain ⟨N, hNpos, hN⟩ := hA
    have hletter (i : Fin d) : A i * (C * A j) = A i * (A j * C) := by
      simpa only [hC, Matrix.mul_assoc] using hcross i j
    have hword_nonempty : ∀ w : List (Fin d), w ≠ [] →
        Kraus.evalWord A w * (C * A j) = Kraus.evalWord A w * (A j * C) := by
      intro w hw
      induction w with
      | nil => exact (hw rfl).elim
      | cons i w ih =>
          cases w with
          | nil =>
              simpa only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
                using hletter i
          | cons k w =>
              calc
                Kraus.evalWord A (i :: k :: w) * (C * A j) =
                    A i * (Kraus.evalWord A (k :: w) * (C * A j)) := by
                  rw [Kraus.evalWord_cons, Matrix.mul_assoc]
                _ = A i * (Kraus.evalWord A (k :: w) * (A j * C)) := by
                  rw [ih (by simp)]
                _ = Kraus.evalWord A (i :: k :: w) * (A j * C) := by
                  conv_rhs => rw [Kraus.evalWord_cons]
                  rw [Matrix.mul_assoc]
    have hword (σ : Fin N → Fin d) :
        Kraus.evalWord A (List.ofFn σ) * (C * A j) =
          Kraus.evalWord A (List.ofFn σ) * (A j * C) := by
      apply hword_nonempty
      intro h
      have := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at this
      omega
    calc
      C * A j = 1 * (C * A j) := by rw [Matrix.one_mul]
      _ = (∑ σ : Fin N → Fin d,
          Kraus.blockDecompositionMap hN 1 σ • Kraus.evalWord A (List.ofFn σ)) *
          (C * A j) := by rw [Kraus.blockDecompositionMap_sum]
      _ = ∑ σ : Fin N → Fin d, Kraus.blockDecompositionMap hN 1 σ •
          (Kraus.evalWord A (List.ofFn σ) * (C * A j)) := by
        rw [Finset.sum_mul]
        simp only [Matrix.smul_mul]
      _ = ∑ σ : Fin N → Fin d, Kraus.blockDecompositionMap hN 1 σ •
          (Kraus.evalWord A (List.ofFn σ) * (A j * C)) := by
        congr 1
        funext σ
        rw [hword]
      _ = (∑ σ : Fin N → Fin d,
          Kraus.blockDecompositionMap hN 1 σ • Kraus.evalWord A (List.ofFn σ)) *
          (A j * C) := by
        rw [Finset.sum_mul]
        simp only [Matrix.smul_mul]
      _ = A j * C := by rw [Kraus.blockDecompositionMap_sum, Matrix.one_mul]
  obtain ⟨δ, hδ⟩ := hA.eq_smul_one_of_commute hcomm
  refine ⟨δ, fun i ↦ ?_⟩
  rw [hC, hδ]
  simp

/-- If `A` is injective and `B i * A j = A i * B j` for every pair of indices,
then all matrices of `B` are obtained from `A` by one common scalar.

Source: `Papers/2502.20257/main.tex:1255-1325`. -/
theorem IsInjective.eq_smul_of_cross_mul_eq
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsInjective A)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ δ : ℂ, ∀ i, B i = δ • A i := by
  apply eq_smul_of_factor_of_cross_mul_eq
    ⟨1, by omega, Kraus.isNBlkInjective_one_of_isInjective hA⟩
    (exists_factor_of_cross_mul_eq_of_isInjective hA hcross) hcross

/-- If `A` is normal and `B i * A j = A i * B j` for every pair of indices,
then all matrices of `B` are obtained from `A` by one common scalar.

The proof blocks `A` to an injective word family and moves the marked `B` letter
through each word before applying the block decomposition map.

Source: `Papers/2502.20257/main.tex:1255-1325`. -/
theorem IsNormal.eq_smul_of_cross_mul_eq
    {A B : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    (hcross : ∀ i j, B i * A j = A i * B j) :
    ∃ δ : ℂ, ∀ i, B i = δ • A i := by
  obtain ⟨N, hNpos, hN⟩ := hA
  exact eq_smul_of_factor_of_cross_mul_eq ⟨N, hNpos, hN⟩
    (exists_factor_of_cross_mul_eq_of_isNBlkInjective hNpos hN hcross) hcross

end Kraus
