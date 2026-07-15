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

* `Matrix.tensorMapIdLM_isKrausCPTP`: tensoring a Kraus-form channel with the
  identity preserves its Kraus-form channel structure.

This is the finite-dimensional localization operation used when a physical
channel acts on one site of a blocked matrix-product density operator while
the neighboring site is left unchanged.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 and Appendix C.2, Proposition C.7
-/

open scoped Matrix BigOperators

namespace Matrix

variable {α β δ : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype δ] [DecidableEq δ]

/-- Tensoring a trace-preserving completely positive matrix map with the
identity on a finite matrix factor preserves the trace-preserving completely
positive property. Its Kraus operators are $A_i \otimes I$, where $A_i$
are Kraus operators for the original map. -/
theorem tensorMapIdLM_isKrausCPTP
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCPTP S) :
    IsKrausCPTP (tensorMapIdLM (δ := δ) S) := by
  obtain ⟨r, A, hAform, hAtp⟩ := hS
  refine ⟨r, fun i => Matrix.kroneckerMap (· * ·) (A i) 1, ?_, ?_⟩
  · intro X
    ext ⟨b, u⟩ ⟨c, v⟩
    change tensorMapId S X (b, u) (c, v) = _
    rw [tensorMapId_apply, hAform, Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, star_mul']
    simp [bipartiteSlice]
  · simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul]
    change ∑ i, ((Matrix.kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix δ δ ℂ)) ((A i)ᴴ * A i) = 1
    rw [← map_sum ((Matrix.kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix δ δ ℂ)), hAtp]
    exact Matrix.one_kronecker_one

end Matrix
