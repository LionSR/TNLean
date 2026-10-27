/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SitewiseOperatorProduct

/-!
# Products with arbitrary closing matrices

The applications include an empty chain and two independently supplied tensors
at each of two sites. The latter permits arbitrary noncommuting bond matrices.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace MPOTensor

/-- info: 'MPOTensor.trace_prod_mulTensor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms trace_prod_mulTensor

example (q D₁ D₂ : ℕ)
    (C₁ : Matrix (Fin D₁) (Fin D₁) ℂ) (C₂ : Matrix (Fin D₂) (Fin D₂) ℂ) :
    let e : Fin (D₁ * D₂) ≃ Fin D₁ × Fin D₂ := finProdFinEquiv.symm
    Matrix.trace ((C₁ ⊗ₖ C₂).submatrix e e) = Matrix.trace C₁ * Matrix.trace C₂ := by
  simpa only [List.ofFn_zero, List.prod_nil, Fintype.sum_unique, Matrix.mul_one] using
    trace_prod_mulTensor (L := 0) (q := q) Fin.elim0 Fin.elim0 C₁ C₂ Fin.elim0 Fin.elim0

example (P Q R S : MPOTensor 2 2)
    (C₁ C₂ : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : Fin 2 → Fin 2) :
    let A : Fin 2 → MPOTensor 2 2 := ![P, Q]
    let B : Fin 2 → MPOTensor 2 2 := ![R, S]
    let e : Fin 4 ≃ Fin 2 × Fin 2 :=
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm
    Matrix.trace ((C₁ ⊗ₖ C₂).submatrix e e *
      (List.ofFn (fun v ↦ mulTensor (A v) (B v) (σ v) (τ v))).prod) =
      ∑ ρ : Fin 2 → Fin 2,
        Matrix.trace (C₁ * (List.ofFn (fun v ↦ A v (σ v) (ρ v))).prod) *
          Matrix.trace (C₂ * (List.ofFn (fun v ↦ B v (ρ v) (τ v))).prod) := by
  intro A B e
  exact trace_prod_mulTensor A B C₁ C₂ σ τ

end MPOTensor

end
