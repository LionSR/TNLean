/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.Linarith

/-!
# Euclidean extension by zero along a finite embedding

An embedding of finite coordinate sets induces a linear isometry by extension
by zero. The same construction applies to the dependent configuration embedding
of a finite family of physical spaces. The norm identity is the finite sum
identity along an injection, with all coefficients outside its range zero.
-/

open scoped BigOperators

namespace Function.Embedding

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Extension by zero along a physical embedding is an actual Euclidean
isometry. This also applies to the dependent configuration embedding of an
entire finite chain. -/
noncomputable def euclideanExtendByZero (e : I ↪ J) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J where
  toLinearMap := LinearMap.withLpMap 2 (Function.ExtendByZero.linearMap ℂ e)
  norm_map' v := by
    classical
    have hsum := Fintype.sum_of_injective e e.injective
      (fun i ↦ ‖v i‖ ^ 2)
      (fun j ↦ ‖Function.extend e (fun i ↦ v i) 0 j‖ ^ 2)
      (fun j hj ↦ by
        rw [Function.extend_apply' _ _ j hj]
        simp)
      (fun i ↦ by rw [e.injective.extend_apply])
    have hsq :
        ‖LinearMap.withLpMap 2 (Function.ExtendByZero.linearMap ℂ e) v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact hsum.symm
    nlinarith [norm_nonneg (LinearMap.withLpMap 2
      (Function.ExtendByZero.linearMap ℂ e) v), norm_nonneg v]

/-- Extension by zero preserves the Euclidean norm of every coefficient vector. -/
theorem norm_euclideanExtendByZero (e : I ↪ J) (v : EuclideanSpace ℂ I) :
    ‖e.euclideanExtendByZero v‖ = ‖v‖ :=
  e.euclideanExtendByZero.norm_map v

/-- The embedded vector agrees with the original vector on every actual
physical coordinate. -/
@[simp] theorem euclideanExtendByZero_apply_image (e : I ↪ J)
    (v : EuclideanSpace ℂ I) (i : I) :
    e.euclideanExtendByZero v (e i) = v i :=
  e.injective.extend_apply (fun i ↦ v i) 0 i

/-- No coefficient is added outside the embedded physical alphabet. -/
theorem euclideanExtendByZero_apply_not_mem_range (e : I ↪ J)
    (v : EuclideanSpace ℂ I) (j : J) (hj : j ∉ Set.range e) :
    e.euclideanExtendByZero v j = 0 :=
  Function.extend_apply' (f := (e : I → J)) (fun i ↦ v i) 0 j hj

end Function.Embedding
