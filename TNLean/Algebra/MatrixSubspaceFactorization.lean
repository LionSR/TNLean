/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Factoring linear maps through a matrix on a subspace

Let `f` map a subspace `U` onto the coordinate space `ℂ^m`, and let `g` vanish on `U ∩ ker f`.
Then `g = X f` on `U` for a matrix `X`. When the coordinate space is one-dimensional the factor is
a scalar, and a scalar matrix with a right inverse is a nonzero scalar whose inverse is the
reciprocal scalar.

## Main results

* `Matrix.exists_mulVec_eq_of_surjOn`: `g = X f` on `U` for a matrix `X`.
* `Matrix.exists_eq_smul_one_of_subsingleton`: a matrix over a one-point index type is a scalar.
* `Matrix.ne_zero_and_eq_inv_smul_one_of_smul_one_mul_eq_one`: `(c • 1) * Y = 1` gives `c ≠ 0`
  and `Y = c⁻¹ • 1`.
-/

namespace Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {m n : Type*} [Fintype m]

/-- A linear map onto a coordinate space on a subspace `U` factors, on `U`, every linear map
whose kernel on `U` contains its own: if `f` maps `U` onto `ℂ^m` and `g` vanishes on
`U ∩ ker f`, then `g = X f` on `U` for a matrix `X`. -/
theorem exists_mulVec_eq_of_surjOn (U : Submodule ℂ V) (f : V →ₗ[ℂ] m → ℂ)
    (g : V →ₗ[ℂ] n → ℂ) (hf : Set.SurjOn f U Set.univ) (hfg : ∀ x ∈ U, f x = 0 → g x = 0) :
    ∃ X : Matrix n m ℂ, ∀ x ∈ U, X *ᵥ f x = g x := by
  classical
  have hsurj : LinearMap.range (f.domRestrict U) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hf (Set.mem_univ v)
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨r, hr⟩ := (f.domRestrict U).exists_rightInverse_of_surjective hsurj
  refine ⟨LinearMap.toMatrix' (g.domRestrict U ∘ₗ r), fun x hx => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have h1 : f ((r (f x) : V) - x) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hr (f x)
  have h2 := hfg _ (U.sub_mem (r (f x)).2 hx) h1
  rw [map_sub, sub_eq_zero] at h2
  simpa using h2

/-- A matrix over a one-point index type is a scalar. -/
theorem exists_eq_smul_one_of_subsingleton [DecidableEq n] [Subsingleton n] [Nonempty n]
    (X : Matrix n n ℂ) : ∃ c : ℂ, X = c • 1 := by
  obtain ⟨j₀⟩ := ‹Nonempty n›
  refine ⟨X j₀ j₀, Matrix.ext fun i j => ?_⟩
  rw [Subsingleton.elim i j₀, Subsingleton.elim j j₀]
  simp

/-- If a scalar matrix `c • 1` on a nonempty index type has a right inverse `Y`, then `c ≠ 0`
and `Y = c⁻¹ • 1`. -/
theorem ne_zero_and_eq_inv_smul_one_of_smul_one_mul_eq_one [Fintype n] [DecidableEq n] [Nonempty n]
    {Y : Matrix n n ℂ} {c : ℂ} (h : (c • 1 : Matrix n n ℂ) * Y = 1) : c ≠ 0 ∧ Y = c⁻¹ • 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, Matrix.zero_mul] at h
    exact zero_ne_one h
  refine ⟨hc, ?_⟩
  rw [Matrix.smul_mul, Matrix.one_mul] at h
  rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Matrix
