/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalAdjoint
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.MPU.Basic

/-!
# Simple matrix product unitary tensors

This file formalizes the double layer and the two exact local contraction identities
`simple1` and `simple2` from arXiv:1703.09188, Section III.A.  It then follows the
paper's sequential contraction proof that every simple tensor generates a matrix
product unitary.

The upper tensor in the paper's diagrams is the physical adjoint: its physical
indices are exchanged and its entries are conjugated, while the virtual chain is
not reflected.  Accordingly the double layer uses `physicalAdjointTensor`, not
`adjointTensor`.

## Main definitions

* `doubleLayerTensor` — the local tensor for \(U^\dagger U\).
* `IsMPUSimple` — the paper's `simple1` and `simple2` identities.

## Main results

* `IsMPUSimple.isMPU` — a simple tensor generates MPU.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants", arXiv:1703.09188,
  Section III.A, lines 359--388 and Figures `II_Simple1.png`, `II_Simple2.png`.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The local **double layer** obtained by placing the physical adjoint of `U`
above `U` and contracting their adjacent physical legs.  Its bond index is the
canonical enumeration of a pair of original bond indices.

Closing a chain of these letters gives `mpo U N` conjugate-transposed times
`mpo U N`; see `mpo_doubleLayerTensor`.

Source: arXiv:1703.09188, Section III.A, lines 363--388 and Figures
`II_Simple1.png`, `II_Simple2.png`. -/
noncomputable def doubleLayerTensor (U : MPOTensor d D) : MPOTensor d (D * D) :=
  mulTensor (physicalAdjointTensor U) U

/-- The exact local, canonically reindexed form of the double-layer letter:
\((W^{ik})_{(β₁,β₂),(α₁,α₂)}\) is obtained from
\(\sum_j (U^\sharp)^{ij} \otimes U^{jk}\) using `finProdFinEquiv` on both
bond indices.

Source: arXiv:1703.09188, Definition III.2, lines 363--374 and Figures
`II_Simple1.png`, `II_Simple2.png`. -/
@[simp] theorem doubleLayerTensor_apply (U : MPOTensor d D) (i k : Fin d) :
    doubleLayerTensor U i k =
      (∑ j : Fin d, (physicalAdjointTensor U i j) ⊗ₖ (U j k)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [doubleLayerTensor, mulTensor_apply]

/-- Closing the double layer gives the global product \((U^{(N)})^\dagger U^{(N)}\).

This fixes the diagram orientation: the upper layer is the physical adjoint,
which generates the conjugate transpose without reflecting the virtual chain.

Source: arXiv:1703.09188, lines 363--388, especially the product contracted in
the proof of Proposition III.3(i). -/
theorem mpo_doubleLayerTensor (U : MPOTensor d D) (N : ℕ) :
    mpo (doubleLayerTensor U) N = (mpo U N)ᴴ * mpo U N := by
  rw [doubleLayerTensor, mpo_mulTensor]
  congr 1
  ext σ τ
  rw [mpo_physicalAdjointTensor]
  rfl

/-- An MPU tensor is **simple** when its double-layer letters have boundary
vectors `a` and `b` satisfying the two diagrammatic identities `simple1` and
`simple2`.

Writing \(W^{ij}\) for a double-layer letter and
\(R=|b)(a|\), the fields are exactly
\[
  (a|W^{ij}|b)=\delta_{ij}, \qquad
  W^{ij}W^{k\ell}=W^{ij}R W^{k\ell}.
\]
Thus `simple1` closes one letter with the witnesses to the physical identity,
while `simple2` inserts the rank-one operator \(|b)(a|\) between two adjacent
letters.  This notion is unrelated to the CPSV16 predicate `MPOTensor.IsSimple`.

Source: arXiv:1703.09188, Definition III.2, equations `simple1` and `simple2`,
lines 363--374 and Figures `II_Simple1.png`, `II_Simple2.png`. -/
def IsMPUSimple (U : MPOTensor d D) : Prop :=
  ∃ a b : Fin (D * D) → ℂ,
    (∀ i j : Fin d,
      a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0) ∧
    (∀ i j k l : Fin d,
      doubleLayerTensor U i j * doubleLayerTensor U k l =
        doubleLayerTensor U i j * vecMulVec b a * doubleLayerTensor U k l)

namespace IsMPUSimple

private theorem sandwich_mul_rankOne_mul {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    a ⬝ᵥ ((A * vecMulVec b a * X) *ᵥ b) =
      (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ (X *ᵥ b)) := by
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec]
  simp [dotProduct, Finset.mul_sum, Finset.sum_mul]

private theorem sandwich_listProd {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B → A * B = A * vecMulVec b a * B) :
    ∀ l : List (Matrix n n ℂ), l ≠ [] → (∀ A ∈ l, P A) →
      a ⬝ᵥ (l.prod *ᵥ b) =
        (l.map fun A ↦ a ⬝ᵥ (A *ᵥ b)).prod := by
  intro l hl hP
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          have hA : P A := hP A (by simp)
          have hB : P B := hP B (by simp)
          have htail : ∀ X ∈ B :: l, P X := by
            intro X hX
            exact hP X (by simp [hX])
          rw [List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
            hpair A B hA hB, Matrix.mul_assoc,
            sandwich_mul_rankOne_mul]
          change (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ ((B :: l).prod *ᵥ b)) = _
          rw [ih (by simp) htail]
          simp

private theorem trace_mul_rankOne_mul {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    Matrix.trace (A * vecMulVec b a * X) = a ⬝ᵥ ((X * A) *ᵥ b) := by
  rw [Matrix.trace_mul_comm (A * vecMulVec b a) X, ← Matrix.mul_assoc,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, ← Matrix.mulVec_mulVec]
  simp [dotProduct, mul_comm]

private theorem trace_listProd {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B → A * B = A * vecMulVec b a * B)
    (l : List (Matrix n n ℂ)) (hl : 1 < l.length) (hP : ∀ A ∈ l, P A) :
    Matrix.trace l.prod = (l.map fun A ↦ a ⬝ᵥ (A *ᵥ b)).prod := by
  rcases l with _ | ⟨A, l⟩
  · simp at hl
  cases l with
  | nil => simp at hl
  | cons B l =>
      have hA : P A := hP A (by simp)
      have hB : P B := hP B (by simp)
      have hrot : ∀ X ∈ (B :: l) ++ [A], P X := by
        intro X hX
        apply hP X
        simp only [List.mem_append, List.mem_cons] at hX ⊢
        tauto
      rw [List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
        hpair A B hA hB, Matrix.mul_assoc, trace_mul_rankOne_mul]
      have hprod : ((B :: l) ++ [A]).prod = B * l.prod * A := by
        simp [Matrix.mul_assoc]
      rw [← hprod, sandwich_listProd a b P hpair _ (by simp) hrot]
      simp [mul_comm, mul_left_comm]

/-- The `simple1` contraction supplied by witnesses for an MPU-simple tensor.

Source: arXiv:1703.09188, equation `simple1`, lines 363--370 and Figure
`II_Simple1.png`. -/
theorem simple1 {U : MPOTensor d D} (hU : IsMPUSimple U) :
    ∃ a b : Fin (D * D) → ℂ, ∀ i j : Fin d,
      a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0 := by
  obtain ⟨a, b, h₁, _⟩ := hU
  exact ⟨a, b, h₁⟩

/-- The exact `simple2` contraction supplied by the same witnesses as
`simple1`: the rank-one operator \(|b)(a|\) may be inserted between adjacent
double-layer letters.

Source: arXiv:1703.09188, equation `simple2`, lines 363--374 and Figure
`II_Simple2.png`. -/
theorem simple2 {U : MPOTensor d D} (hU : IsMPUSimple U) :
    ∃ a b : Fin (D * D) → ℂ, ∀ i j k l : Fin d,
      doubleLayerTensor U i j * doubleLayerTensor U k l =
        doubleLayerTensor U i j * vecMulVec b a * doubleLayerTensor U k l := by
  obtain ⟨a, b, _, h₂⟩ := hU
  exact ⟨a, b, h₂⟩

/-- Sequentially applying `simple2` around a closed double-layer chain and
then `simple1` at every site gives the physical identity.

Source: arXiv:1703.09188, Proposition III.3(i), lines 378--388. -/
theorem mpo_doubleLayerTensor_eq_one {U : MPOTensor d D} (hU : IsMPUSimple U)
    (N : ℕ) (hN : 1 < N) :
    mpo (doubleLayerTensor U) N =
      (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) := by
  obtain ⟨a, b, h₁, h₂⟩ := hU
  ext σ τ
  rw [mpo_apply, mpoMatrixEntry, Matrix.one_apply]
  rw [evalWord_ofFn]
  let P : Matrix (Fin (D * D)) (Fin (D * D)) ℂ → Prop :=
    fun A ↦ ∃ i j, A = doubleLayerTensor U i j
  have hP : ∀ A ∈ List.ofFn (fun x : Fin N ↦ doubleLayerTensor U (σ x) (τ x)), P A := by
    intro A hA
    simp only [List.mem_ofFn] at hA
    obtain ⟨x, rfl⟩ := hA
    exact ⟨σ x, τ x, rfl⟩
  have hpair : ∀ A B, P A → P B → A * B = A * vecMulVec b a * B := by
    rintro A B ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact h₂ i j k l
  rw [trace_listProd a b P hpair _ (by simpa) hP]
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, h₁]
  by_cases hστ : σ = τ
  · subst τ
    simp
  · rw [if_neg hστ]
    have hpoint : ∃ x, σ x ≠ τ x := by
      by_contra h
      apply hστ
      funext x
      exact not_ne_iff.mp (not_exists.mp h x)
    obtain ⟨x, hx⟩ := hpoint
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp [hx]

/-- Every simple tensor generates a matrix product unitary, by the paper's
sequential contraction route through `simple2` and `simple1`.

Source: arXiv:1703.09188, Proposition III.3(i), lines 378--388. -/
theorem isMPU {U : MPOTensor d D} (hU : IsMPUSimple U) : IsMPU U := by
  intro N hN
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose]
  rw [← mpo_doubleLayerTensor]
  exact hU.mpo_doubleLayerTensor_eq_one N hN

end IsMPUSimple

end MPOTensor
