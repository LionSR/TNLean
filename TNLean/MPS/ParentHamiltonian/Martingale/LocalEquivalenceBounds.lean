/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction

/-!
# Volume-independent bounds for finitely many physical changes

An invertible map on a fixed local window extends to the whole chain by
identity on the exterior coordinates. Its forward and inverse norm bounds
are unchanged. Composing two such maps therefore has norm bounds given by
the product of the two local bounds, independently of the chain length.
These are the bounded-boundary changes used in the open endpoint argument
of arXiv:2203.12563, Section 5, lines 1690–1692.
-/

namespace MPSTensor

open ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- Extend an invertible physical map independently over every exterior
configuration. -/
noncomputable def rightFiberwiseLinearEquiv
    (e : EuclideanSpace ℂ I ≃ₗ[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) ≃ₗ[ℂ] EuclideanSpace ℂ (I × S) where
  __ := (rightFiberwiseMap (S := S) e.toLinearMap.toContinuousLinearMap).toLinearMap
  invFun := rightFiberwiseMap (S := S) e.symm.toLinearMap.toContinuousLinearMap
  left_inv x := by
    apply PiLp.ext
    rintro ⟨i, s⟩
    change e.symm (rightFiber
      (rightFiberwiseMap e.toLinearMap.toContinuousLinearMap x) s) i = x (i, s)
    rw [rightFiber_rightFiberwiseMap]
    change e.symm (e (rightFiber x s)) i = x (i, s)
    rw [e.symm_apply_apply]
    rfl
  right_inv x := by
    apply PiLp.ext
    rintro ⟨i, s⟩
    change e (rightFiber
      (rightFiberwiseMap e.symm.toLinearMap.toContinuousLinearMap x) s) i = x (i, s)
    rw [rightFiber_rightFiberwiseMap]
    change e (e.symm (rightFiber x s)) i = x (i, s)
    rw [e.apply_symm_apply]
    rfl

/-- Adding exterior identity factors cannot increase the norm of a local
physical map. -/
theorem norm_rightFiberwiseLinearEquiv_apply_le
    (e : EuclideanSpace ℂ I ≃ₗ[ℂ] EuclideanSpace ℂ I)
    (v : EuclideanSpace ℂ (I × S)) :
    ‖rightFiberwiseLinearEquiv (S := S) e v‖ ≤
      ‖e.toLinearMap.toContinuousLinearMap‖ * ‖v‖ := by
  change ‖rightFiberwiseMap e.toLinearMap.toContinuousLinearMap v‖ ≤ _
  calc
    ‖rightFiberwiseMap (S := S) e.toLinearMap.toContinuousLinearMap v‖ ≤
        ‖rightFiberwiseMap (S := S) e.toLinearMap.toContinuousLinearMap‖ * ‖v‖ :=
      (rightFiberwiseMap (S := S) e.toLinearMap.toContinuousLinearMap).le_opNorm v
    _ ≤ ‖e.toLinearMap.toContinuousLinearMap‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (norm_rightFiberwiseMap_le (S := S) e.toLinearMap.toContinuousLinearMap)
        (norm_nonneg v)

/-- The inverse of the exterior extension has the original inverse norm
bound, without a factor depending on the number of exterior sites. -/
theorem norm_rightFiberwiseLinearEquiv_symm_apply_le
    (e : EuclideanSpace ℂ I ≃ₗ[ℂ] EuclideanSpace ℂ I)
    (v : EuclideanSpace ℂ (I × S)) :
    ‖(rightFiberwiseLinearEquiv (S := S) e).symm v‖ ≤
      ‖e.symm.toLinearMap.toContinuousLinearMap‖ * ‖v‖ :=
  norm_rightFiberwiseLinearEquiv_apply_le e.symm v

variable {d R N : ℕ}

/-- Extend an invertible local-window map to its cyclic placement in the
chain, retaining identity on every exterior physical coordinate. -/
noncomputable def localPhysicalLinearEquivES
    (e : EuclideanSpace ℂ (Cfg d R) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) :
    EuclideanSpace ℂ (Cfg d N) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  U.toLinearEquiv.trans ((rightFiberwiseLinearEquiv (S := Cfg d (N - R)) e).trans
    U.symm.toLinearEquiv)

/-- A local physical change has a forward norm bound independent of volume. -/
theorem norm_localPhysicalLinearEquivES_apply_le
    (e : EuclideanSpace ℂ (Cfg d R) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    ‖localPhysicalLinearEquivES e hRN i v‖ ≤
      ‖e.toLinearMap.toContinuousLinearMap‖ * ‖v‖ := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  change ‖U.symm (rightFiberwiseLinearEquiv e (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_apply_le e (U v)

/-- A local physical change has an inverse norm bound independent of volume. -/
theorem norm_localPhysicalLinearEquivES_symm_apply_le
    (e : EuclideanSpace ℂ (Cfg d R) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hRN : R ≤ N) (i : Fin N) (v : EuclideanSpace ℂ (Cfg d N)) :
    ‖(localPhysicalLinearEquivES e hRN i).symm v‖ ≤
      ‖e.symm.toLinearMap.toContinuousLinearMap‖ * ‖v‖ := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i
  change ‖U.symm ((rightFiberwiseLinearEquiv e).symm (U v))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using norm_rightFiberwiseLinearEquiv_symm_apply_le e (U v)

/-- Two fixed local physical changes have a product forward bound independent
of their placement and of the chain length. -/
theorem norm_two_localPhysicalLinearEquivES_apply_le
    {R₀ R₁ : ℕ}
    (e₀ : EuclideanSpace ℂ (Cfg d R₀) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R₀))
    (e₁ : EuclideanSpace ℂ (Cfg d R₁) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R₁))
    (hR₀ : R₀ ≤ N) (hR₁ : R₁ ≤ N) (i j : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    ‖((localPhysicalLinearEquivES e₀ hR₀ i).trans
      (localPhysicalLinearEquivES e₁ hR₁ j)) v‖ ≤
      (‖e₀.toLinearMap.toContinuousLinearMap‖ *
        ‖e₁.toLinearMap.toContinuousLinearMap‖) * ‖v‖ := by
  have h₀ := norm_localPhysicalLinearEquivES_apply_le e₀ hR₀ i v
  have h₁ := norm_localPhysicalLinearEquivES_apply_le e₁ hR₁ j
    (localPhysicalLinearEquivES e₀ hR₀ i v)
  exact h₁.trans (by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left h₀ (norm_nonneg e₁.toLinearMap.toContinuousLinearMap))

/-- Two fixed local physical changes have a product inverse bound independent
of their placement and of the chain length. -/
theorem norm_two_localPhysicalLinearEquivES_symm_apply_le
    {R₀ R₁ : ℕ}
    (e₀ : EuclideanSpace ℂ (Cfg d R₀) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R₀))
    (e₁ : EuclideanSpace ℂ (Cfg d R₁) ≃ₗ[ℂ] EuclideanSpace ℂ (Cfg d R₁))
    (hR₀ : R₀ ≤ N) (hR₁ : R₁ ≤ N) (i j : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) :
    ‖((localPhysicalLinearEquivES e₀ hR₀ i).trans
      (localPhysicalLinearEquivES e₁ hR₁ j)).symm v‖ ≤
      (‖e₀.symm.toLinearMap.toContinuousLinearMap‖ *
        ‖e₁.symm.toLinearMap.toContinuousLinearMap‖) * ‖v‖ := by
  have h₁ := norm_localPhysicalLinearEquivES_symm_apply_le e₁ hR₁ j v
  have h₀ := norm_localPhysicalLinearEquivES_symm_apply_le e₀ hR₀ i
    ((localPhysicalLinearEquivES e₁ hR₁ j).symm v)
  exact h₀.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left h₁ (norm_nonneg e₀.symm.toLinearMap.toContinuousLinearMap))

end MPSTensor
