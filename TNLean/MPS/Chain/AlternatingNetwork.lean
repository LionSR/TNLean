/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PiTensorProductPhase
import TNLean.MPS.Chain.OneSidedInverse

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Alternating open tensor networks

This file proves the nondegenerate form of the alternating-network proportionality
argument in arXiv:2502.20257, Lemma `lemma:1`, lines 2296--2395.  The network is kept
open at its two horizontal ends.  Contracting the physical leg of each injective tensor
against a one-sided inverse separates the tensors in the intervening positions.

## Main definitions

* `MPSTensor.openAlternatingNetwork` is the connected open chain
  \(A_1B_1A_2B_2\cdots A_nB_n\).

## Main results

* `MPSTensor.inverseContraction_openAlternatingNetwork` implements contraction
  by the paper's one-sided inverses of all \(A_i\).
* `MPSTensor.exists_scalars_of_openAlternatingNetwork_eq` is the corrected form of
  arXiv:2502.20257, Lemma `lemma:1`, under nonvanishing of every \(B_i\).

**Local fix (nonzero intervening tensors):** the printed lemma omits nonvanishing,
and a zero factor makes its conclusion false.  Both uses at lines 2567 and 3157
have nonzero intervening tensors.  The convention and the zero-factor degeneration
are recorded in
`docs/paper-gaps/fbc25_alternating_network_nondegeneracy.tex`.

## References

* [arXiv:2502.20257](https://arxiv.org/abs/2502.20257) -- Adrián Franco Rubio,
  Arkadiusz Bochniak, and J. Ignacio Cirac, *Symmetry defects and gauging for quantum
  states with matrix product unitary symmetries*
-/

open scoped BigOperators TensorProduct

open Module

namespace MPSTensor

/-- The connected open chain \(A_1B_1A_2B_2\cdots A_nB_n\).

The functions `d` and `D` give the sitewise physical dimensions and the dimensions
of the \(n+1\) horizontal bonds.  At site \(i\), the injective tensor \(A_i\) has square
bond dimension \(D_i\), while \(B_i\) has left and right bond dimensions \(D_i\) and
\(D_{i+1}\).  Its remaining open leg has index type `p i` and is grouped with its
left bond index.

Source: arXiv:2502.20257, equation `eq:lemma_equality`, lines 2296--2361. -/
noncomputable def openAlternatingNetwork
    {n : ℕ} {d : Fin n → ℕ} (D : Fin (n + 1) → ℕ) (p : Fin n → Type*)
    [∀ i : Fin n, Fintype (p i)]
    (A : (i : Fin n) → MPSTensor (d i) (D i.castSucc))
    (B : (i : Fin n) → Matrix (p i × Fin (D i.castSucc)) (Fin (D i.succ)) ℂ)
    (σ : (i : Fin n) → Fin (d i)) (τ : (i : Fin n) → p i) :
    Matrix (Fin (D 0)) (Fin (D (Fin.last n))) ℂ := fun a b ↦
  ∑ x : (j : Fin (n + 1)) → Fin (D j),
    ∑ y : (i : Fin n) → Fin (D i.castSucc),
      if x 0 = a ∧ x (Fin.last n) = b then
        ∏ i : Fin n,
          A i (σ i) (x i.castSucc) (y i) * B i (τ i, y i) (x i.succ)
      else 0

private theorem piTensorProduct_eq_of_forall_matrix_entry_prod_eq
    {n : ℕ} {row col : Fin n → Type*}
    [∀ i : Fin n, Finite (row i)] [∀ i : Fin n, Finite (col i)]
    (B B' : (i : Fin n) → Matrix (row i) (col i) ℂ)
    (h : ∀ (r : (i : Fin n) → row i) (c : (i : Fin n) → col i),
      (∏ i : Fin n, B i (r i) (c i)) = ∏ i : Fin n, B' i (r i) (c i)) :
    (⨂ₜ[ℂ] i : Fin n, B i) = ⨂ₜ[ℂ] i : Fin n, B' i := by
  classical
  let _ : ∀ i : Fin n, Fintype (row i) := fun i ↦ Fintype.ofFinite _
  let b : (i : Fin n) →
      Basis (row i × col i) ℂ (Matrix (row i) (col i) ℂ) :=
    fun i ↦ Matrix.stdBasis ℂ (row i) (col i)
  apply (Basis.piTensorProduct b).repr.injective
  ext q
  simpa [b, Matrix.stdBasis] using h (fun i ↦ (q i).1) (fun i ↦ (q i).2)

private theorem decompositionMap_matrixUnit_entry
    {d D : ℕ} {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (a b x y : Fin D) :
    (∑ s : Fin d,
      Kraus.decompositionMap hA (Matrix.single a b 1) s * A s x y) =
      Matrix.single a b 1 x y := by
  calc
    _ = (∑ s : Fin d,
        Kraus.decompositionMap hA (Matrix.single a b 1) s • A s) x y := by
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = _ := by
      rw [Kraus.decompositionMap_sum]

private theorem inverseCoefficient_sum
    {n : ℕ} {d : Fin n → ℕ} {D : Fin (n + 1) → ℕ}
    (A : (i : Fin n) → MPSTensor (d i) (D i.castSucc))
    (hA : ∀ i : Fin n, Kraus.IsInjective (A i))
    (z x : (j : Fin (n + 1)) → Fin (D j))
    (q y : (i : Fin n) → Fin (D i.castSucc)) :
    (∑ σ : (i : Fin n) → Fin (d i),
      (∏ i : Fin n,
        Kraus.decompositionMap (hA i)
          (Matrix.single (z i.castSucc) (q i) 1) (σ i)) *
        ∏ i : Fin n, A i (σ i) (x i.castSucc) (y i)) =
      ∏ i : Fin n,
        Matrix.single (z i.castSucc) (q i) 1 (x i.castSucc) (y i) := by
  classical
  calc
    _ = ∏ i : Fin n, ∑ s : Fin (d i),
        Kraus.decompositionMap (hA i)
          (Matrix.single (z i.castSucc) (q i) 1) s *
          A i s (x i.castSucc) (y i) := by
      simpa only [Finset.prod_mul_distrib] using
        (Fintype.prod_sum (fun i s ↦
          Kraus.decompositionMap (hA i)
            (Matrix.single (z i.castSucc) (q i) 1) s *
            A i s (x i.castSucc) (y i))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact decompositionMap_matrixUnit_entry (hA i)
        (z i.castSucc) (q i) (x i.castSucc) (y i)

private theorem matrixUnit_prod_eq_zero_of_path_ne
    {n : ℕ} {D : Fin (n + 1) → ℕ}
    (z x : (j : Fin (n + 1)) → Fin (D j))
    (q y : (i : Fin n) → Fin (D i.castSucc))
    (hxlast : x (Fin.last n) = z (Fin.last n)) (hx : x ≠ z) :
    (∏ i : Fin n,
      Matrix.single (z i.castSucc) (q i) (1 : ℂ) (x i.castSucc) (y i)) = 0 := by
  classical
  have hcast : ∃ i : Fin n, x i.castSucc ≠ z i.castSucc := by
    by_contra h
    apply hx
    funext j
    exact Fin.lastCases hxlast
      (fun i ↦ not_not.mp (not_exists.mp h i)) j
  obtain ⟨i, hi⟩ := hcast
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Matrix.single_apply_of_row_ne hi.symm _ _ _

private theorem matrixUnit_prod_eq_zero_of_middle_ne
    {n : ℕ} {D : Fin (n + 1) → ℕ}
    (z x : (j : Fin (n + 1)) → Fin (D j))
    (q y : (i : Fin n) → Fin (D i.castSucc)) (hy : y ≠ q) :
    (∏ i : Fin n,
      Matrix.single (z i.castSucc) (q i) (1 : ℂ) (x i.castSucc) (y i)) = 0 := by
  classical
  have hmiddle : ∃ i : Fin n, y i ≠ q i := by
    by_contra h
    apply hy
    funext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hmiddle
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Matrix.single_apply_of_col_ne _ _ hi.symm _

/-- Contracting every injective tensor against inverse coefficients for matrix
units separates all intervening tensors in the connected open chain.

This is the inverse-tensor contraction in arXiv:2502.20257, Lemma `lemma:1`,
lines 2365--2392. -/
theorem inverseContraction_openAlternatingNetwork
    {n : ℕ} {d : Fin n → ℕ} (D : Fin (n + 1) → ℕ) (p : Fin n → Type*)
    [∀ i : Fin n, Fintype (p i)]
    (A : (i : Fin n) → MPSTensor (d i) (D i.castSucc))
    (B : (i : Fin n) → Matrix (p i × Fin (D i.castSucc)) (Fin (D i.succ)) ℂ)
    (hA : ∀ i : Fin n, Kraus.IsInjective (A i))
    (z : (j : Fin (n + 1)) → Fin (D j))
    (q : (i : Fin n) → Fin (D i.castSucc)) (τ : (i : Fin n) → p i) :
    (∑ σ : (i : Fin n) → Fin (d i),
      (∏ i : Fin n,
        Kraus.decompositionMap (hA i)
          (Matrix.single (z i.castSucc) (q i) 1) (σ i)) *
        openAlternatingNetwork D p A B σ τ (z 0) (z (Fin.last n))) =
      ∏ i : Fin n, B i (τ i, q i) (z i.succ) := by
  classical
  calc
    _ = ∑ x : (j : Fin (n + 1)) → Fin (D j),
        ∑ y : (i : Fin n) → Fin (D i.castSucc),
          if x 0 = z 0 ∧ x (Fin.last n) = z (Fin.last n) then
            (∏ i : Fin n,
              Matrix.single (z i.castSucc) (q i) 1 (x i.castSucc) (y i)) *
              ∏ i : Fin n, B i (τ i, y i) (x i.succ)
          else 0 := by
      simp only [openAlternatingNetwork, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hxy : x 0 = z 0 ∧ x (Fin.last n) = z (Fin.last n)
      · simp only [ite_eq_left hxy]
        simp_rw [Finset.prod_mul_distrib, ← mul_assoc]
        rw [← Finset.sum_mul, inverseCoefficient_sum A hA z x q y]
      · simp [hxy]
    _ = _ := by
      rw [Fintype.sum_eq_single z]
      · rw [Fintype.sum_eq_single q]
        · simp
        · intro y hy
          rw [ite_eq_left ⟨rfl, rfl⟩]
          exact mul_eq_zero_of_left
            (matrixUnit_prod_eq_zero_of_middle_ne z z q y hy) _
      · intro x hx
        by_cases hboundary : x 0 = z 0 ∧ x (Fin.last n) = z (Fin.last n)
        · apply Finset.sum_eq_zero
          intro y _
          rw [ite_eq_left hboundary]
          exact mul_eq_zero_of_left
            (matrixUnit_prod_eq_zero_of_path_ne z x q y hboundary.2 hx) _
        · simp [hboundary]

private theorem exists_matrix_entry_ne_zero
    {r c : Type*} (M : Matrix r c ℂ) (hM : M ≠ 0) :
    ∃ a b, M a b ≠ 0 := by
  classical
  by_contra h
  apply hM
  ext a b
  by_contra hab
  exact h ⟨a, b, hab⟩

/-- The nondegenerate corrected form of the alternating-network proportionality
lemma: equality of the connected open chains forces the intervening tensors to
be proportional, with product-one proportionality scalars.

Source: arXiv:2502.20257, Lemma `lemma:1` and equation `eq:lemma_equality`,
lines 2296--2395.  Nonvanishing is justified at the two uses on lines 2567 and
3157. -/
theorem exists_scalars_of_openAlternatingNetwork_eq
    {n : ℕ} {d : Fin n → ℕ} (D : Fin (n + 1) → ℕ) (p : Fin n → Type*)
    [∀ i : Fin n, Fintype (p i)]
    (A : (i : Fin n) → MPSTensor (d i) (D i.castSucc))
    (B B' : (i : Fin n) →
      Matrix (p i × Fin (D i.castSucc)) (Fin (D i.succ)) ℂ)
    (hA : ∀ i : Fin n, Kraus.IsInjective (A i))
    (hB : ∀ i : Fin n, B i ≠ 0)
    (hnetwork : ∀ (σ : (i : Fin n) → Fin (d i)) (τ : (i : Fin n) → p i),
      openAlternatingNetwork D p A B σ τ =
        openAlternatingNetwork D p A B' σ τ) :
    ∃ β : Fin n → ℂ,
      (∏ i : Fin n, β i = 1) ∧ ∀ i : Fin n, B i = β i • B' i := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨fun i ↦ Fin.elim0 i, by simp, ?_⟩
    intro i
    exact Fin.elim0 i
  have : NeZero n := ⟨hn⟩
  have hentries :
      ∀ (r : (i : Fin n) → p i × Fin (D i.castSucc))
        (c : (i : Fin n) → Fin (D i.succ)),
        (∏ i : Fin n, B i (r i) (c i)) =
          ∏ i : Fin n, B' i (r i) (c i) := by
    intro r c
    let z : (j : Fin (n + 1)) → Fin (D j) :=
      Fin.cases (r 0).2 (fun i ↦ c i)
    let q : (i : Fin n) → Fin (D i.castSucc) := fun i ↦ (r i).2
    let τ : (i : Fin n) → p i := fun i ↦ (r i).1
    calc
      ∏ i : Fin n, B i (r i) (c i) =
          ∏ i : Fin n, B i (τ i, q i) (z i.succ) := by
            simp [z, q, τ]
      _ = ∑ σ : (i : Fin n) → Fin (d i),
          (∏ i : Fin n,
            Kraus.decompositionMap (hA i)
              (Matrix.single (z i.castSucc) (q i) 1) (σ i)) *
            openAlternatingNetwork D p A B σ τ (z 0) (z (Fin.last n)) :=
        (inverseContraction_openAlternatingNetwork D p A B hA z q τ).symm
      _ = ∑ σ : (i : Fin n) → Fin (d i),
          (∏ i : Fin n,
            Kraus.decompositionMap (hA i)
              (Matrix.single (z i.castSucc) (q i) 1) (σ i)) *
            openAlternatingNetwork D p A B' σ τ (z 0) (z (Fin.last n)) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hnetwork σ τ]
      _ = ∏ i : Fin n, B' i (τ i, q i) (z i.succ) :=
        inverseContraction_openAlternatingNetwork D p A B' hA z q τ
      _ = ∏ i : Fin n, B' i (r i) (c i) := by
        simp [z, q, τ]
  have htensor :
      (⨂ₜ[ℂ] i : Fin n, B i) = ⨂ₜ[ℂ] i : Fin n, B' i :=
    piTensorProduct_eq_of_forall_matrix_entry_prod_eq B B' hentries
  choose r c hrc using fun i ↦ exists_matrix_entry_ne_zero (B i) (hB i)
  obtain ⟨κ, hκprod, hκ⟩ :=
    TNLean.Algebra.PiTensorProductPhase.exists_kappa_of_piTensorProduct_eq_smul
      (fun i (_ : Fin 1) ↦ B' i) (fun i (_ : Fin 1) ↦ B i)
      1 one_ne_zero (fun _ ↦ 0) r c (fun i ↦ by simpa using hrc i)
      (fun _ ↦ by simpa using htensor.symm)
  have hκprod_ne : (∏ i : Fin n, κ i) ≠ 0 := by
    rw [hκprod]
    exact one_ne_zero
  have hκ_ne (i : Fin n) : κ i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hκprod_ne) i (Finset.mem_univ i)
  refine ⟨fun i ↦ (κ i)⁻¹, ?_, ?_⟩
  · rw [Finset.prod_inv_distrib, hκprod, inv_one]
  · intro i
    rw [hκ i 0, ← mul_smul, inv_mul_cancel₀ (hκ_ne i), one_smul]

end MPSTensor
