/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Mixed products of physical maps

A finite family of boundary maps and a finite family of internal-bond maps act
on the two corresponding configuration spaces. Their product acts separately
on every factor of a coherent sum, even when the two families have different
input and output dimensions. Conjugate transpose takes the adjoint of each
individual factor.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {B E X Y P Q : Type*} [Fintype B] [Fintype E]

/-- The product matrix of boundary maps and internal-bond maps.
Source: SCP10, Section 7, lines 2977–3019. -/
def mixedPhysicalProductMatrix (F : B → Matrix Y X ℂ) (K : E → Matrix Q P ℂ) :
    Matrix ((B → Y) × (E → Q)) ((B → X) × (E → P)) ℂ :=
  fun τ σ => (∏ b, F b (τ.1 b) (σ.1 b)) * ∏ e, K e (τ.2 e) (σ.2 e)

/-- Taking the adjoint takes the adjoint of every boundary and internal factor.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem mixedPhysicalProductMatrix_conjTranspose
    (F : B → Matrix Y X ℂ) (K : E → Matrix Q P ℂ) :
    (mixedPhysicalProductMatrix F K).conjTranspose =
      mixedPhysicalProductMatrix (fun b => (F b).conjTranspose)
        (fun e => (K e).conjTranspose) := by
  ext σ τ
  simp only [mixedPhysicalProductMatrix, Matrix.conjTranspose_apply, star_mul,
    star_prod, mul_comm]

variable [DecidableEq B] [DecidableEq E] [Fintype X] [Fintype P]

/-- The physical linear map associated to the mixed product matrix.
Source: SCP10, Section 7, lines 2977–3019. -/
def mixedPhysicalProductMap (F : B → Matrix Y X ℂ) (K : E → Matrix Q P ℂ) :
    (((B → X) × (E → P)) → ℂ) →ₗ[ℂ] (((B → Y) × (E → Q)) → ℂ) :=
  Matrix.mulVecLin (mixedPhysicalProductMatrix F K)

/-- The coefficient of the mixed product map. -/
theorem mixedPhysicalProductMap_apply (F : B → Matrix Y X ℂ) (K : E → Matrix Q P ℂ)
    (ψ : ((B → X) × (E → P)) → ℂ) (τ : (B → Y) × (E → Q)) :
    mixedPhysicalProductMap F K ψ τ =
      ∑ σ : (B → X) × (E → P),
        ((∏ b, F b (τ.1 b) (σ.1 b)) * ∏ e, K e (τ.2 e) (σ.2 e)) * ψ σ := rfl

/-- A mixed product map acts separately on every factor of a coherent sum.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem mixedPhysicalProductMap_sum_prod {A : Type*} [Fintype A]
    (F : B → Matrix Y X ℂ) (K : E → Matrix Q P ℂ) (w : A → ℂ)
    (x : B → A → X → ℂ) (y : E → A → P → ℂ) :
    mixedPhysicalProductMap F K
        (fun σ => ∑ a, w a * (∏ b, x b a (σ.1 b)) * ∏ e, y e a (σ.2 e)) =
      fun τ => ∑ a, w a * (∏ b, (F b *ᵥ x b a) (τ.1 b)) *
        ∏ e, (K e *ᵥ y e a) (τ.2 e) := by
  ext τ
  simp only [mixedPhysicalProductMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = w a * ∑ σ : (B → X) × (E → P),
        (∏ b, F b (τ.1 b) (σ.1 b) * x b a (σ.1 b)) *
          ∏ e, K e (τ.2 e) (σ.2 e) * y e a (σ.2 e) := by
      simp only [Finset.mul_sum, Finset.prod_mul_distrib, mul_assoc, mul_left_comm,
        mul_comm]
    _ = w a * ((∏ b, ∑ i : X, F b (τ.1 b) i * x b a i) *
        ∏ e, ∑ j : P, K e (τ.2 e) j * y e a j) := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      rw [Fintype.prod_sum, Fintype.prod_sum]
    _ = _ := by rw [mul_assoc]; rfl

end TNLean.PEPS
