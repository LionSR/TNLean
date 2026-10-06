/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.NormNum

/-!
# Finite spectator extensions of Euclidean operators

Fixing one product coordinate defines a fiber of a Euclidean vector. Applying
one operator independently to every fiber preserves sums, composition,
orthogonal projections, and the operator norm for nonempty spectator spaces.
These facts concern finite Euclidean spaces and require no MPS gap theorem.
-/

open scoped BigOperators ComplexOrder

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- The active-coordinate vector obtained by fixing one right spectator. -/
noncomputable def rightFiber (x : EuclideanSpace ℂ (I × S)) (s : S) :
    EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i => x (i, s)

/-- Apply the same operator independently at every value of a finite right
spectator coordinate. -/
noncomputable def rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) →L[ℂ] EuclideanSpace ℂ (I × S) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun p => G (rightFiber x p.2) p.1
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (x + y) s)) i = _
        rw [show rightFiber (x + y) s = rightFiber x s + rightFiber y s by
          apply PiLp.ext
          intro j
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨i, s⟩
        change (G (rightFiber (c • x) s)) i = _
        rw [show rightFiber (c • x) s = c • rightFiber x s by
          apply PiLp.ext
          intro j
          rfl, map_smul]
        rfl }

/-- Fiberwise extension applies the base operator on the selected fiber. -/
@[simp] theorem rightFiberwiseMap_apply_apply
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (i : I) (s : S) :
    rightFiberwiseMap (S := S) G x (i, s) = G (rightFiber x s) i := rfl

/-- Taking a fiber after extension recovers the base operator on that fiber. -/
@[simp] theorem rightFiber_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) (s : S) :
    rightFiber (rightFiberwiseMap (S := S) G x) s = G (rightFiber x s) := by
  apply PiLp.ext
  intro i
  rfl

/-- Right-spectator extension preserves addition. -/
theorem rightFiberwiseMap_add
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (G + H) =
      rightFiberwiseMap (S := S) G + rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- Right-spectator extension preserves subtraction. -/
theorem rightFiberwiseMap_sub
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (G - H) =
      rightFiberwiseMap (S := S) G - rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- The right-spectator extension of the zero operator is zero. -/
@[simp] theorem rightFiberwiseMap_zero :
    rightFiberwiseMap (I := I) (S := S) 0 = 0 := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- Right-spectator extension preserves finite sums. -/
theorem rightFiberwiseMap_sum {ι : Type*} (s : Finset ι)
    (G : ι → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (∑ i ∈ s, G i) =
      ∑ i ∈ s, rightFiberwiseMap (S := S) (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, rightFiberwiseMap_add, ih]

/-- A vector lies in the kernel of a fiberwise operator exactly when every
right-spectator fiber lies in the kernel of the base operator. -/
theorem mem_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × S)) :
    x ∈ LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap ↔
      ∀ s, rightFiber x s ∈ LinearMap.ker G.toLinearMap := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx s
    apply PiLp.ext
    intro i
    have hi := congrArg (fun y : EuclideanSpace ℂ (I × S) => y (i, s)) hx
    exact hi
  · intro hx
    apply PiLp.ext
    rintro ⟨i, s⟩
    change G (rightFiber x s) i = 0
    exact congrArg (fun y : EuclideanSpace ℂ I => y i) (hx s)

/-- Right-spectator extension preserves composition. -/
theorem rightFiberwiseMap_comp
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (rightFiberwiseMap (S := S) G).comp (rightFiberwiseMap (S := S) H) =
      rightFiberwiseMap (S := S) (G.comp H) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  rfl

/-- Fiberwise extension preserves symmetry. -/
theorem isSymmetric_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetric) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  calc
    ∑ i, ∑ s, inner ℂ (rightFiberwiseMap (S := S) G x (i, s)) (y (i, s)) =
        ∑ s, ∑ i, inner ℂ (G (rightFiber x s) i) (rightFiber y s i) := by
      rw [Finset.sum_comm]
      rfl
    _ = ∑ s, ∑ i, inner ℂ (rightFiber x s i) (G (rightFiber y s) i) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← PiLp.inner_apply, ← PiLp.inner_apply]
      exact hG (rightFiber x s) (rightFiber y s)
    _ = ∑ i, ∑ s, inner ℂ (x (i, s))
        (rightFiberwiseMap (S := S) G y (i, s)) := by
      rw [Finset.sum_comm]
      rfl

/-- Fiberwise extension preserves orthogonal projections. -/
theorem isSymmetricProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetricProjection) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, isSymmetric_rightFiberwiseMap G hG.isSymmetric⟩
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  change G (G (rightFiber x s)) i = G (rightFiber x s) i
  have hs := LinearMap.congr_fun hG.isIdempotentElem.eq (rightFiber x s)
  exact congrArg (fun y : EuclideanSpace ℂ I => y i) hs

/-- The kernel projection of a fiberwise operator is the fiberwise extension
of the base kernel projection. -/
theorem ker_starProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap).starProjection.toLinearMap =
      (rightFiberwiseMap (S := S)
        (LinearMap.ker G.toLinearMap).starProjection).toLinearMap := by
  let U := LinearMap.ker G.toLinearMap
  apply LinearMap.IsSymmetricProjection.ext
    (Submodule.isSymmetricProjection_starProjection _)
    (isSymmetricProjection_rightFiberwiseMap _
      (Submodule.isSymmetricProjection_starProjection U))
  ext x
  constructor
  · intro hx
    rw [Submodule.range_starProjection] at hx
    refine ⟨x, ?_⟩
    apply PiLp.ext
    rintro ⟨i, s⟩
    change U.starProjection (rightFiber x s) i = x (i, s)
    have hs := (mem_ker_rightFiberwiseMap_iff G x).mp hx s
    exact congrArg (fun y : EuclideanSpace ℂ I => y i)
      (U.starProjection_eq_self_iff.mpr hs)
  · rintro ⟨y, rfl⟩
    rw [Submodule.range_starProjection]
    apply (mem_ker_rightFiberwiseMap_iff G _).mpr
    intro s
    change U.starProjection (rightFiber y s) ∈ U
    exact Submodule.starProjection_apply_mem U _

/-- Right-spectator extension does not increase the operator norm. The statement
also covers an empty spectator type. -/
theorem norm_rightFiberwiseMap_le
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ p : I × S, ‖rightFiberwiseMap (S := S) G x p‖ ^ 2 =
        ∑ s, ∑ i, ‖G (rightFiber x s) i‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ s, ‖G (rightFiber x s)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ s, (‖G‖ * ‖rightFiber x s‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr (G.le_opNorm _)
    _ = ‖G‖ ^ 2 * ∑ p : I × S, ‖x p‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_pow, EuclideanSpace.norm_sq_eq]
      simp only [rightFiber, Finset.mul_sum]

/-- A vector supported at one right-spectator coordinate. -/
noncomputable def singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) := by
  classical
  exact WithLp.toLp 2 fun p => if p.2 = s then x p.1 else 0

/-- A vector supported on one spectator fiber has the norm of that fiber. -/
theorem norm_singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    ‖singleRightFiber s x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_comm]
  classical
  rw [Finset.sum_eq_single s]
  · simp [singleRightFiber]
  · intro t _ hts
    simp [singleRightFiber, hts]
  · simp

/-- On a nonempty spectator space, right-spectator extension preserves the
operator norm exactly. -/
theorem norm_rightFiberwiseMap [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖rightFiberwiseMap (S := S) G‖ = ‖G‖ := by
  apply le_antisymm (norm_rightFiberwiseMap_le G)
  let s : S := Classical.choice ‹Nonempty S›
  refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg _) fun x ↦ ?_
  calc
    ‖G x‖ = ‖rightFiberwiseMap (S := S) G (singleRightFiber s x)‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_prod_type, Finset.sum_comm]
      classical
      symm
      rw [Finset.sum_eq_single s]
      · simp [singleRightFiber, rightFiber]
      · intro t _ hts
        have hfiber : rightFiber (singleRightFiber s x) t = 0 := by
          apply PiLp.ext
          intro i
          change (if t = s then x i else 0) = 0
          simp [hts]
        have hpoint : ∀ i : I,
            rightFiberwiseMap (S := S) G (singleRightFiber s x) (i, t) = 0 := by
          intro i
          rw [rightFiberwiseMap_apply_apply, hfiber, map_zero]
          rfl
        apply Finset.sum_eq_zero
        intro i _
        rw [hpoint i]
        norm_num
      · simp
    _ ≤ ‖rightFiberwiseMap (S := S) G‖ * ‖singleRightFiber s x‖ :=
      (rightFiberwiseMap (S := S) G).le_opNorm _
    _ = ‖rightFiberwiseMap (S := S) G‖ * ‖x‖ := by
      rw [norm_singleRightFiber]

/-- Conjugation by a surjective linear isometry preserves the operator norm. -/
theorem norm_conj_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (G : E →L[ℂ] E) :
    ‖U.toLinearIsometry.toContinuousLinearMap.comp
        (G.comp U.symm.toLinearIsometry.toContinuousLinearMap)‖ = ‖G‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
    calc
      ‖U (G (U.symm x))‖ = ‖G (U.symm x)‖ := U.norm_map _
      _ ≤ ‖G‖ * ‖U.symm x‖ := G.le_opNorm _
      _ = ‖G‖ * ‖x‖ := by rw [U.symm.norm_map]
  · let C := U.toLinearIsometry.toContinuousLinearMap.comp
        (G.comp U.symm.toLinearIsometry.toContinuousLinearMap)
    refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg C) fun x ↦ ?_
    calc
      ‖G x‖ = ‖U (G x)‖ := (U.norm_map _).symm
      _ = ‖C (U x)‖ := by
        dsimp only [C, ContinuousLinearMap.comp_apply]
        change ‖U (G x)‖ = ‖U (G (U.symm (U x)))‖
        rw [LinearIsometryEquiv.symm_apply_apply]
      _ ≤ ‖C‖ * ‖U x‖ := C.le_opNorm _
      _ = ‖C‖ * ‖x‖ := by rw [U.norm_map]

end ContinuousLinearMap
