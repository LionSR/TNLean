/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.MatrixAction

/-!
# Matrices acting on the vectors of a sheet

A sheet has one raw register `ℂ^q` at every site of a finite set `Λ`; a vector on the sheet is a
vector of `EuclideanSpace ℂ (Λ → Fin q)`. This file collects the elementary facts about the
action `act A` of a matrix on such vectors that the changes of ownership use: linearity, the
bound `‖A ψ‖ ≤ ‖A‖ ‖ψ‖`, the Gram form of `‖A ψ‖²`, and the telescoping bound for a product of
contractions. It also defines the rank-one projector `|v⟩⟨v|`, the product zero vector on a set
of sites, and the tagged stack `∑_t |t⟩ ⊗ R_t` of a family of operators. Nothing here depends on
a geometry of the sites.

## Main definitions

* `EncodedFrame.rankOne`: the rank-one projector `|v⟩⟨v|`.
* `EncodedFrame.zeroVec`: the product zero vector `|0⟩^{⊗ D}`.
* `EncodedFrame.stack`: the tagged stack `∑_t |t⟩ ⊗ R_t`.

## Main results

* `EncodedFrame.norm_act_le_of_norm_le_one`: a contraction does not increase norms.
* `EncodedFrame.norm_act_eq_of_gram_eq`: matrices with the same Gram matrix move every vector to
  the same length.
* `EncodedFrame.norm_act_list_prod_sub_le`: the defect of a product of contractions is at most
  the sum of their defects.
* `EncodedFrame.stack_conjTranspose_mul_stack`: `(stack R)ᴴ stack S = ∑_t R_tᴴ S_t`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §6.1, `05-frames.tex`, lines 11–97, and the
  proof of Lemma 6.3, lines 237–248.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Euclidean vectors and matrices -/

section Euclidean

variable {m n : Type*} [Fintype m] [Fintype n]

theorem act_sub (A B : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (A - B) ψ = act A ψ - act B ψ := by
  simp [act_apply, Matrix.sub_mulVec]

theorem act_add (A B : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (A + B) ψ = act A ψ + act B ψ := by
  simp [act_apply, Matrix.add_mulVec]

theorem act_smul (a : ℂ) (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (a • A) ψ = a • act A ψ := by
  ext i
  simp [act_apply, Matrix.smul_mulVec]

theorem act_sum {κ : Type*} [Fintype κ] (A : κ → Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    act (∑ k, A k) ψ = ∑ k, act (A k) ψ := by
  ext i
  simp [act_apply, Matrix.sum_mulVec]

theorem act_sub_right (A : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    act A (x - y) = act A x - act A y := by
  simp [act_apply, Matrix.mulVec_sub]

theorem act_one [DecidableEq n] (ψ : EuclideanSpace ℂ n) : act (1 : Matrix n n ℂ) ψ = ψ := by
  simp [act_apply]

theorem norm_act_le [DecidableEq n] (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    ‖act A ψ‖ ≤ ‖A‖ * ‖ψ‖ :=
  A.l2_opNorm_mulVec ψ

theorem norm_act_le_of_norm_le_one [DecidableEq n] {A : Matrix m n ℂ} (hA : ‖A‖ ≤ 1)
    (ψ : EuclideanSpace ℂ n) : ‖act A ψ‖ ≤ ‖ψ‖ :=
  (norm_act_le A ψ).trans (mul_le_of_le_one_left (norm_nonneg _) hA)

/-- The squared norm of `A ψ` is the expectation of `Aᴴ A` in `ψ`. -/
theorem norm_act_sq (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    (‖act A ψ‖ ^ 2 : ℂ) = star (⇑ψ) ⬝ᵥ ((Aᴴ * A) *ᵥ ⇑ψ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (act A ψ)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct_comm]
  exact_mod_cast h.symm

/-- Two matrices with the same Gram matrix move every vector to the same length. -/
theorem norm_act_eq_of_gram_eq {m' : Type*} [Fintype m'] {A : Matrix m n ℂ}
    {B : Matrix m' n ℂ} (h : Aᴴ * A = Bᴴ * B) (ψ : EuclideanSpace ℂ n) :
    ‖act A ψ‖ = ‖act B ψ‖ := by
  have h2 : (‖act A ψ‖ ^ 2 : ℂ) = (‖act B ψ‖ ^ 2 : ℂ) := by
    rw [norm_act_sq, norm_act_sq, h]
  have h3 : ‖act A ψ‖ ^ 2 = ‖act B ψ‖ ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- Relabelling the rows of a matrix along an equivalence does not change the norm of its
action on a vector. -/
theorem norm_act_submatrix_equiv {m' : Type*} [Fintype m'] (A : Matrix m n ℂ) (e : m' ≃ m)
    (ψ : EuclideanSpace ℂ n) : ‖act (A.submatrix e id) ψ‖ = ‖act A ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e (fun i => ‖act A ψ i‖ ^ 2)

/-- **Telescoping on a vector.** For contractions `A₁, …, A_s`, the defect of their product on
`ψ` is at most the sum of their individual defects on `ψ`.

Polynomial-PEPS manuscript, proof of Lemma 6.3, `05-frames.tex`, lines 237–248. -/
theorem norm_act_list_prod_sub_le [DecidableEq n] :
    (l : List (Matrix n n ℂ)) → (∀ A ∈ l, ‖A‖ ≤ 1) → (ψ : EuclideanSpace ℂ n) →
      ‖act l.prod ψ - ψ‖ ≤ (l.map fun A => ‖act A ψ - ψ‖).sum
  | [], _, ψ => by simp [act_one]
  | A :: l, h, ψ => by
    rw [List.prod_cons, List.map_cons, List.sum_cons, act_mul]
    have hA := h A List.mem_cons_self
    have ih := norm_act_list_prod_sub_le l (fun B hB => h B (List.mem_cons_of_mem _ hB)) ψ
    calc ‖act A (act l.prod ψ) - ψ‖
        = ‖act A (act l.prod ψ - ψ) + (act A ψ - ψ)‖ := by
          rw [act_sub_right]; congr 1; abel
      _ ≤ ‖act A (act l.prod ψ - ψ)‖ + ‖act A ψ - ψ‖ := norm_add_le _ _
      _ ≤ ‖act l.prod ψ - ψ‖ + ‖act A ψ - ψ‖ :=
          add_le_add (norm_act_le_of_norm_le_one hA _) le_rfl
      _ ≤ _ := by linarith

end Euclidean

/-! ### Operators on a set of sites -/

/-- The rank-one projector `|v⟩⟨v|`. -/
def rankOne {α : Type*} [Fintype α] (v : EuclideanSpace ℂ α) : Matrix α α ℂ :=
  vecMulVec (⇑v) (star ⇑v)

/-- The product zero vector `|0⟩^{⊗ D}` on the sites of `D`. -/
def zeroVec [NeZero q] (D : Finset ι) : (D → Fin q) → ℂ :=
  Pi.single 0 1

omit [Fintype ι] in
theorem star_zeroVec_dotProduct_zeroVec [NeZero q] (D : Finset ι) :
    star (zeroVec (q := q) D) ⬝ᵥ zeroVec D = 1 := by
  classical
  simp [zeroVec, dotProduct, Pi.single_apply]

theorem star_dotProduct_self_of_norm_eq_one {α : Type*} [Fintype α] {v : EuclideanSpace ℂ α}
    (hv : ‖v‖ = 1) : star (⇑v) ⬝ᵥ ⇑v = 1 := by
  have h : (inner ℂ v v : ℂ) = (‖v‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K v
  rw [EuclideanSpace.inner_eq_star_dotProduct, hv] at h
  rw [dotProduct_comm]
  simpa using h

theorem rankOne_conjTranspose {α : Type*} [Fintype α] (v : EuclideanSpace ℂ α) :
    (rankOne v)ᴴ = rankOne v := by
  simp [rankOne, conjTranspose_vecMulVec]

theorem rankOne_mul_self {α : Type*} [Fintype α] {v : EuclideanSpace ℂ α} (hv : ‖v‖ = 1) :
    rankOne v * rankOne v = rankOne v := by
  rw [rankOne, Matrix.vecMulVec_mul_vecMulVec, star_dotProduct_self_of_norm_eq_one hv, one_smul]

/-! ### Stacking tagged operators -/

section Stack

variable {T m n : Type*} [Fintype T] [Fintype m] [Fintype n]

/-- The tagged stack `∑_t |t⟩ ⊗ R_t` of a family of operators. -/
def stack (R : T → Matrix m n ℂ) : Matrix (T × m) n ℂ := Matrix.of fun r τ => R r.1 r.2 τ

omit [Fintype T] [Fintype m] [Fintype n] in
@[simp]
theorem stack_apply (R : T → Matrix m n ℂ) (t : T) (σ : m) (τ : n) :
    stack R (t, σ) τ = R t σ τ := rfl

omit [Fintype n] in
theorem stack_conjTranspose_mul_stack {n' : Type*} (R : T → Matrix m n ℂ)
    (S : T → Matrix m n' ℂ) : (stack R)ᴴ * stack S = ∑ t, (R t)ᴴ * S t := by
  ext τ τ'
  simp only [mul_apply, conjTranspose_apply, stack_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]

omit [Fintype T] [Fintype m] in
theorem stack_mul {l : Type*} (R : T → Matrix m n ℂ) (A : Matrix n l ℂ) :
    stack R * A = stack fun t => R t * A := by
  ext ⟨t, σ⟩ τ
  simp [mul_apply]

end Stack

end TNLean.PEPS.EncodedFrame
