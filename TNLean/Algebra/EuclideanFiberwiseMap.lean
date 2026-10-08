/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operators on finite Euclidean direct sums

A Euclidean vector indexed by `S × I` is a finite family of vectors indexed
by `I`. Applying one operator to each member of the family preserves
composition and adjoints. Its operator norm does not exceed the norm of the
original operator, including when any of the coordinate sets are empty.
The inner product is the sum of the inner products of the fibers.

These elementary direct-sum identities provide the finite-dimensional
estimates used for spectator boundaries in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (i), lines 2442--2531.
No tensor, normalization, or injectivity hypothesis is involved.
-/

namespace EuclideanSpace
variable {𝕜 S I J : Type*} [RCLike 𝕜] [Fintype S] [Fintype I] [Fintype J]

/-- Extract one vector from a finite Euclidean family. No finiteness hypothesis
is needed for this linear coordinate projection. -/
noncomputable def fiberₗ (s : S) :
    EuclideanSpace 𝕜 (S × I) →ₗ[𝕜] EuclideanSpace 𝕜 I :=
  (WithLp.linearEquiv 2 𝕜 (I → 𝕜)).symm.toLinearMap.comp
    ((LinearMap.pi fun i => LinearMap.proj (s, i)).comp
      (WithLp.linearEquiv 2 𝕜 (S × I → 𝕜)).toLinearMap)

/-- Apply an operator independently to each vector in a finite Euclidean family.
The source and target coordinate sets may differ. -/
noncomputable def fiberwiseMap (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J) :
    EuclideanSpace 𝕜 (S × I) →L[𝕜] EuclideanSpace 𝕜 (S × J) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 𝕜 (S × J → 𝕜)).symm.toLinearMap.comp
      (LinearMap.pi fun p => (LinearMap.proj p.2).comp
        ((WithLp.linearEquiv 2 𝕜 (J → 𝕜)).toLinearMap.comp
          (G.toLinearMap.comp (fiberₗ p.1))))

omit [Fintype S] [Fintype I] in
/-- Coordinate evaluation of the Euclidean family projection. -/
@[simp] theorem fiberₗ_apply (s : S) (x : EuclideanSpace 𝕜 (S × I)) (i : I) :
    fiberₗ s x i = x (s, i) := rfl

/-- Coordinate evaluation of the operator acting on each family member. -/
@[simp] theorem fiberwiseMap_apply (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J)
    (x : EuclideanSpace 𝕜 (S × I)) (s : S) (j : J) :
    fiberwiseMap S G x (s, j) = G (fiberₗ s x) j := rfl

/-- Extracting a fiber after applying the family operator gives the original
operator applied to that fiber. -/
@[simp] theorem fiberₗ_fiberwiseMap (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J)
    (x : EuclideanSpace 𝕜 (S × I)) (s : S) :
    fiberₗ s (fiberwiseMap S G x) = G (fiberₗ s x) := by
  rfl

/-- A finite direct sum does not increase the operator norm. The bound is
uniform in the family index and remains valid for empty coordinate sets. -/
theorem norm_fiberwiseMap_le (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J) :
    ‖fiberwiseMap S G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ p : S × J, ‖fiberwiseMap S G x p‖ ^ 2 = ∑ s, ‖G (fiberₗ s x)‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, fiberwiseMap_apply, EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ s, (‖G‖ * ‖fiberₗ s x‖) ^ 2 := by
      exact Finset.sum_le_sum fun s _ =>
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr
          (G.le_opNorm _)
    _ = ‖G‖ ^ 2 * ∑ p : S × I, ‖x p‖ ^ 2 := by
      simp only [mul_pow, EuclideanSpace.norm_sq_eq, fiberₗ_apply, Fintype.sum_prod_type,
        Finset.mul_sum]

/-- Inner products against a finite direct-sum operator split over its fibers. -/
theorem inner_fiberwiseMap (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J)
    (x : EuclideanSpace 𝕜 (S × I)) (y : EuclideanSpace 𝕜 (S × J)) :
    inner 𝕜 y (fiberwiseMap S G x) =
      ∑ s, inner 𝕜 (fiberₗ s y) (G (fiberₗ s x)) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, fiberwiseMap_apply, fiberₗ_apply]

/-- The adjoint of a finite direct-sum operator is the direct sum of its adjoint. -/
theorem fiberwiseMap_adjoint (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J) :
    (fiberwiseMap S G).adjoint = fiberwiseMap S G.adjoint := by
  refine ContinuousLinearMap.ext fun x => ext_inner_left 𝕜 fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_fiberwiseMap]
  simp only [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply,
    Fintype.sum_prod_type, fiberwiseMap_apply, fiberₗ_apply]

/-- Finite direct sums preserve composition. -/
theorem fiberwiseMap_comp {H : Type*} [Fintype H] (S : Type*) [Fintype S]
    (G : EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 H)
    (F : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J) :
    (fiberwiseMap S G).comp (fiberwiseMap S F) = fiberwiseMap S (G.comp F) := by
  rfl

/-- The direct sum of identity operators is the identity. -/
theorem fiberwiseMap_id (S : Type*) [Fintype S] :
    fiberwiseMap S (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 I)) =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (S × I)) := by
  rfl

/-- Finite direct sums preserve differences of operators. -/
theorem fiberwiseMap_sub (S : Type*) [Fintype S]
    (G H : EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 J) :
    fiberwiseMap S (G - H) = fiberwiseMap S G - fiberwiseMap S H := by
  rfl

end EuclideanSpace
