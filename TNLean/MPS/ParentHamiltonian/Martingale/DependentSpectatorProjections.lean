/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.DependentSpectatorGapEquivalence

/-!
# Orthogonal projections with dependent spectator coordinates

Orthogonal projections extend independently over a finite dependent family.
An isometric coordinate change identifies such an extension once its kernels
have been identified on every label and spectator fiber. Empty labels and
empty fibers are allowed.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {Q : Type*} {I S : Q → Type*} [Fintype Q]
  [∀ q, Fintype (I q)] [∀ q, Fintype (S q)]

/-- A dependent sum of orthogonal projections is an orthogonal projection. -/
theorem isSymmetricProjection_sigmaFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (hG : ∀ q, (G q).toLinearMap.IsSymmetricProjection) :
    (sigmaFiberwiseMap G).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply PiLp.ext
    rintro ⟨q, i⟩
    change G q (sigmaFiber (sigmaFiberwiseMap G x) q) i = G q (sigmaFiber x q) i
    rw [sigmaFiber_sigmaFiberwiseMap]
    exact congrArg (fun y : EuclideanSpace ℂ (I q) ↦ y i)
      (LinearMap.congr_fun (hG q).isIdempotentElem.eq (sigmaFiber x q))
  · intro x y
    rw [inner_eq_sum_inner_sigmaFiber, inner_eq_sum_inner_sigmaFiber]
    apply Finset.sum_congr rfl
    intro q _
    change ⟪G q (sigmaFiber x q), sigmaFiber y q⟫_ℂ =
      ⟪sigmaFiber x q, G q (sigmaFiber y q)⟫_ℂ
    exact (hG q).isSymmetric (sigmaFiber x q) (sigmaFiber y q)

/-- Dependent exterior extension preserves orthogonal projections. -/
theorem isSymmetricProjection_dependentRightFiberwiseMap
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (hG : ∀ q, (G q).toLinearMap.IsSymmetricProjection) :
    (dependentRightFiberwiseMap (S := S) G).toLinearMap.IsSymmetricProjection :=
  isSymmetricProjection_sigmaFiberwiseMap _ fun q ↦
    isSymmetricProjection_rightFiberwiseMap _ (hG q)

end ContinuousLinearMap

namespace LinearIsometryEquiv

/-- Identify a projection with a dependent spectator extension from its
actual kernel fibers. This does not assume the operator identity. -/
theorem conj_eq_dependentRightFiberwiseMap_of_ker_iff
    {E Q : Type*} {I S : Q → Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [Fintype Q] [∀ q, Fintype (I q)] [∀ q, Fintype (S q)]
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Σ q, I q × S q))
    (P : E →ₗ[ℂ] E)
    (G : ∀ q, EuclideanSpace ℂ (I q) →L[ℂ] EuclideanSpace ℂ (I q))
    (hP : P.IsSymmetricProjection)
    (hG : ∀ q, (G q).toLinearMap.IsSymmetricProjection)
    (hker : ∀ v, v ∈ LinearMap.ker P ↔ ∀ q s,
      ContinuousLinearMap.dependentRightFiber (U v) q s ∈ LinearMap.ker (G q).toLinearMap) :
    U.toLinearEquiv.conj P =
      (ContinuousLinearMap.dependentRightFiberwiseMap (S := S) G).toLinearMap := by
  let L := U.toLinearEquiv.conj P
  let R := (ContinuousLinearMap.dependentRightFiberwiseMap (S := S) G).toLinearMap
  have hL : L.IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.map U.toLinearEquiv.conjRingEquiv,
      (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff P U).mpr hP.isSymmetric⟩
  have hR : R.IsSymmetricProjection :=
    ContinuousLinearMap.isSymmetricProjection_dependentRightFiberwiseMap G hG
  have hk : LinearMap.ker L = LinearMap.ker R := by
    ext y
    have hconj : y ∈ LinearMap.ker L ↔ U.symm y ∈ LinearMap.ker P := by
      change U (P (U.symm y)) = 0 ↔ P (U.symm y) = 0
      exact U.map_eq_zero_iff
    rw [hconj, ContinuousLinearMap.mem_ker_dependentRightFiberwiseMap_iff, hker]
    simp only [U.apply_symm_apply]
  apply LinearMap.IsSymmetricProjection.ext hL hR
  have hrL : LinearMap.range L = (LinearMap.ker L)ᗮ := by
    rw [← hL.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hrR : LinearMap.range R = (LinearMap.ker R)ᗮ := by
    rw [← hR.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  rw [hrL, hrR, hk]

end LinearIsometryEquiv
