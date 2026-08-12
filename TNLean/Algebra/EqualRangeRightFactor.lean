/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

/-!
# Equal-range endomorphisms

This file proves that two finite-dimensional endomorphisms with equal ranges differ by
precomposition with a linear automorphism. It also gives the corresponding square-matrix
statement with an invertible right factor.

## Main results

* `LinearMap.exists_linearEquiv_comp_eq_of_range_eq`: equal-range endomorphisms differ by
  precomposition with a linear equivalence.
* `Matrix.exists_isUnit_mul_eq_of_range_mulVecLin_eq`: square matrices with the same column
  space differ by an invertible right factor.
-/

open Module

namespace LinearMap

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Two endomorphisms with the same range differ by precomposition with a linear equivalence. -/
theorem exists_linearEquiv_comp_eq_of_range_eq (A B : Module.End K E)
    (h : A.range = B.range) :
    ∃ Y : E ≃ₗ[K] E, A.comp Y.toLinearMap = B := by
  obtain ⟨CA, hCA⟩ := A.ker.exists_isCompl
  obtain ⟨CB, hCB⟩ := B.ker.exists_isCompl
  have hker : finrank K A.ker = finrank K B.ker := by
    have hA := A.finrank_range_add_finrank_ker
    have hB := B.finrank_range_add_finrank_ker
    rw [h] at hA
    omega
  let eker : B.ker ≃ₗ[K] A.ker :=
    Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hker.symm)
  let ecomp : CB ≃ₗ[K] CA :=
    (B.kerComplementEquivRange hCB.symm).trans
      ((LinearEquiv.ofEq B.range A.range h.symm).trans
        (A.kerComplementEquivRange hCA.symm).symm)
  let Y : E ≃ₗ[K] E :=
    (CB.prodEquivOfIsCompl B.ker hCB.symm).symm |>.trans <|
      (ecomp.prodCongr eker).trans (CA.prodEquivOfIsCompl A.ker hCA.symm)
  refine ⟨Y, LinearMap.ext fun x ↦ ?_⟩
  let z := (CB.prodEquivOfIsCompl B.ker hCB.symm).symm x
  have hx : x = (z.1 : E) + z.2 := by
    exact (CB.prodEquivOfIsCompl B.ker hCB.symm).apply_symm_apply x |>.symm
  change A (Y x) = B x
  have hecomp : A (ecomp z.1) = B z.1 := by
    have hecomp' :
        (A.kerComplementEquivRange hCA.symm) (ecomp z.1) =
          LinearEquiv.ofEq B.range A.range h.symm
            ((B.kerComplementEquivRange hCB.symm) z.1) := by
      exact (A.kerComplementEquivRange hCA.symm).apply_symm_apply _
    exact congr_arg Subtype.val hecomp'
  change A (ecomp z.1 + eker z.2) = B x
  rw [map_add, A.mem_ker.mp (eker z.2).property, add_zero, hecomp, hx, map_add,
    B.mem_ker.mp z.2.property, add_zero]

end LinearMap

namespace Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Square matrices with the same column space differ by an invertible right factor. -/
theorem exists_isUnit_mul_eq_of_range_mulVecLin_eq (A B : Matrix n n K)
    (h : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    ∃ Y : Matrix n n K, IsUnit Y ∧ A * Y = B := by
  obtain ⟨e, he⟩ := LinearMap.exists_linearEquiv_comp_eq_of_range_eq A.toLin' B.toLin' h
  let Y := e.toLinearMap.toMatrix'
  refine ⟨Y, ?_, ?_⟩
  · rw [LinearMap.isUnit_toMatrix'_iff, Module.End.isUnit_iff]
    exact e.bijective
  · apply Matrix.toLin'.injective
    simpa [Y] using he

end Matrix
