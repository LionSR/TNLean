/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.Algebra.ListProduct
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Products of site-dependent matrix product operators

Let the tensors at site `v` be `A v` and `B v`, with closing matrices `C₁` and
`C₂`. Contracting the intermediate physical index at each site represents the
product of the two operators, with bond dimension `D₁ * D₂` and closing matrix
`C₁ ⊗ₖ C₂`. The tensors may vary from site to site, and the chain and bond
dimensions may vanish.

The main identity is `MPOTensor.trace_prod_mulTensor`; its identity-closing
specialization is `MPOTensor.trace_prod_mulTensor_one`. Two ordered matrix
product identities give the coordinate change and Kronecker factorization
used in the proof.

This extends the product construction in arXiv:1606.00608, Section 4.5,
lines 986–993, to site-dependent tensors and supplied closing matrices.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace Matrix

/-- A simultaneous coordinate change preserves the ordered matrix product.
Supporting product algebra for CPSV17, arXiv:1606.00608, §4.5, lines 986–993. -/
private theorem prod_ofFn_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {L : ℕ}
    (F : Fin L → Matrix ι ι ℂ) (e : κ ≃ ι) :
    (List.ofFn (fun v ↦ (F v).submatrix e e)).prod =
      ((List.ofFn F).prod).submatrix e e := by
  simpa only [List.map_ofFn, Function.comp_def, coe_reindexRingEquiv,
    reindex_apply, Equiv.symm_symm] using
    (map_list_prod (reindexRingEquiv ℂ e.symm) (List.ofFn F)).symm

/-- Sitewise Kronecker products preserve the order in each factor.
Supporting product algebra for CPSV17, arXiv:1606.00608, §4.5, lines 986–993. -/
private theorem prod_ofFn_kronecker {D₁ D₂ L : ℕ}
    (A : Fin L → Matrix (Fin D₁) (Fin D₁) ℂ)
    (B : Fin L → Matrix (Fin D₂) (Fin D₂) ℂ) :
    (List.ofFn (fun v ↦ A v ⊗ₖ B v)).prod =
      (List.ofFn A).prod ⊗ₖ (List.ofFn B).prod := by
  induction L with
  | zero => simp only [List.ofFn_zero, List.prod_nil, one_kronecker_one]
  | succ L ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih (fun v ↦ A v.succ) (fun v ↦ B v.succ)]
    exact (mul_kronecker_mul (A 0) (List.ofFn (fun v ↦ A v.succ)).prod
      (B 0) (List.ofFn (fun v ↦ B v.succ)).prod).symm

end Matrix

namespace MPOTensor

/-- Contracting the physical middle index site by site multiplies the two
nonuniform trace-form operators. The closing matrix is the Kronecker product
of their supplied closing matrices. All chain and bond dimensions may be zero.
This is the site-dependent form of CPSV17, arXiv:1606.00608, Section 4.5,
lines 986–993, supporting the stacked tensors in ALVV Proposition 5.7. -/
theorem trace_prod_mulTensor {L q D₁ D₂ : ℕ}
    (A : Fin L → MPOTensor q D₁) (B : Fin L → MPOTensor q D₂)
    (C₁ : Matrix (Fin D₁) (Fin D₁) ℂ) (C₂ : Matrix (Fin D₂) (Fin D₂) ℂ)
    (σ τ : Fin L → Fin q) :
    let e : Fin (D₁ * D₂) ≃ Fin D₁ × Fin D₂ := finProdFinEquiv.symm
    Matrix.trace ((C₁ ⊗ₖ C₂).submatrix e e *
      (List.ofFn (fun v ↦ mulTensor (A v) (B v) (σ v) (τ v))).prod) =
      ∑ ρ : Fin L → Fin q,
        Matrix.trace (C₁ * (List.ofFn (fun v ↦ A v (σ v) (ρ v))).prod) *
          Matrix.trace (C₂ * (List.ofFn (fun v ↦ B v (ρ v) (τ v))).prod) := by
  intro e
  simp only [mulTensor_apply]
  rw [Matrix.prod_ofFn_submatrix_equiv,
    Matrix.submatrix_mul_equiv _ _ e e e, Matrix.trace_submatrix_equiv]
  rw [List.prod_ofFn_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [Matrix.prod_ofFn_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

/-- With identity closing matrices, the site-dependent product tensor has the
ordinary trace coefficients of the product operator. No translation-invariance
assumption is imposed. CPSV17, arXiv:1606.00608, Section 4.5, lines 986–993. -/
theorem trace_prod_mulTensor_one {L q D₁ D₂ : ℕ}
    (A : Fin L → MPOTensor q D₁) (B : Fin L → MPOTensor q D₂)
    (σ τ : Fin L → Fin q) :
    Matrix.trace ((List.ofFn (fun v ↦ mulTensor (A v) (B v) (σ v) (τ v))).prod) =
      ∑ ρ : Fin L → Fin q,
        Matrix.trace ((List.ofFn (fun v ↦ A v (σ v) (ρ v))).prod) *
          Matrix.trace ((List.ofFn (fun v ↦ B v (ρ v) (τ v))).prod) := by
  simpa only [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv, Matrix.one_mul] using
    trace_prod_mulTensor A B (1 : Matrix (Fin D₁) (Fin D₁) ℂ)
      (1 : Matrix (Fin D₂) (Fin D₂) ℂ) σ τ

end MPOTensor

end
