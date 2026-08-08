/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.TensorMap
import TNLean.Channel.KrausCPTP

/-!
# Localized trace-preserving completely positive maps

This file proves that a rectangular trace-preserving completely positive map
remains trace-preserving and completely positive after tensoring it with the
identity map on a finite matrix factor.

## Main results

* `Matrix.tensorMapIdLM_isKrausCP`: tensoring a Kraus-form completely positive map with the
  identity preserves complete positivity.
* `Matrix.tensorMapIdLM_isKrausCPTP`: tensoring a Kraus-form channel with the
  identity on the second factor preserves its Kraus-form channel structure.
* `Matrix.idTensorMapLM_isKrausCPTP`: tensoring the identity on the first factor
  with a Kraus-form channel preserves its Kraus-form channel structure.

This is the finite-dimensional localization operation used when a physical
channel acts on one site of a blocked matrix-product density operator while
the neighboring site is left unchanged.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 and Appendix C.2, Proposition C.7
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace Matrix

variable {α β δ : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype δ] [DecidableEq δ]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem tensorMapId_krausForm
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} {r : ℕ} (A : Fin r → Matrix β α ℂ)
    (hAform : ∀ X, S X = ∑ i, A i * X * (A i)ᴴ) (X : Matrix (α × δ) (α × δ) ℂ) :
    tensorMapId S X = ∑ i, Matrix.kroneckerMap (· * ·) (A i) 1 * X *
      (Matrix.kroneckerMap (· * ·) (A i) 1)ᴴ := by
  classical
  ext ⟨b, u⟩ ⟨c, v⟩
  rw [tensorMapId_apply, hAform, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, star_mul']
  simp [bipartiteSlice]

/-- Tensoring a completely positive matrix map with the identity on a finite matrix factor
preserves complete positivity. Its Kraus operators are $A_i \otimes I$. -/
theorem tensorMapIdLM_isKrausCP
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCP S) :
    IsKrausCP (tensorMapIdLM (δ := δ) S) := by
  obtain ⟨r, A, hAform⟩ := hS
  exact ⟨r, fun i => Matrix.kroneckerMap (· * ·) (A i) 1,
    tensorMapId_krausForm A hAform⟩

-- The finite and decidable instances construct the product indices in `tensorMapIdLM_isKrausCP`
-- and `PosSemidef`; the unused-instance linters do not detect these uses through those definitions.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Tensoring a Kraus completely positive map with the identity on a finite matrix factor
preserves positive semidefiniteness. -/
theorem tensorMapId_posSemidef_of_isKrausCP {α β δ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype δ] [DecidableEq δ]
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCP S)
    {X : Matrix (α × δ) (α × δ) ℂ} (hX : X.PosSemidef) :
    (Matrix.tensorMapId S X).PosSemidef := by
  have hkraus := (tensorMapIdLM_isKrausCP (δ := δ) hS).map_posSemidef hX
  rwa [Matrix.tensorMapIdLM_apply] at hkraus

/-- Tensoring a trace-preserving completely positive matrix map with the
identity on a finite matrix factor preserves the trace-preserving completely
positive property. Its Kraus operators are $A_i \otimes I$, where $A_i$
are Kraus operators for the original map. -/
theorem tensorMapIdLM_isKrausCPTP
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCPTP S) :
    IsKrausCPTP (tensorMapIdLM (δ := δ) S) := by
  obtain ⟨r, A, hAform, hAtp⟩ := hS
  refine ⟨r, fun i => Matrix.kroneckerMap (· * ·) (A i) 1,
    tensorMapId_krausForm A hAform, ?_⟩
  simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul]
  change ∑ i, ((Matrix.kroneckerBilinear (R := ℂ)).flip
    (1 : Matrix δ δ ℂ)) ((A i)ᴴ * A i) = 1
  rw [← map_sum ((Matrix.kroneckerBilinear (R := ℂ)).flip
    (1 : Matrix δ δ ℂ)), hAtp]
  exact Matrix.one_kronecker_one

/-- Tensoring the identity on a finite matrix factor with a trace-preserving
completely positive matrix map preserves the trace-preserving completely
positive property. -/
theorem idTensorMapLM_isKrausCPTP
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hS : IsKrausCPTP S) :
    IsKrausCPTP (idTensorMapLM (δ := δ) S) := by
  change IsKrausCPTP
    (equivReindexMap (Equiv.prodComm β δ) ∘ₗ tensorMapIdLM S ∘ₗ
      equivReindexMap (Equiv.prodComm δ α))
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (equivReindexMap_isKrausCPTP (Equiv.prodComm δ α))
      (tensorMapIdLM_isKrausCPTP hS))
    (equivReindexMap_isKrausCPTP (Equiv.prodComm β δ))

end Matrix
