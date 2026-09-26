/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport

/-!
# Order of operators after adjoining free sites

An operator acting on the active sites extends independently over each value
of the remaining physical coordinates. Its quadratic form is the sum of the
active quadratic forms. In particular, this extension preserves positivity
and inequalities between self-adjoint operators.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- The quadratic form of an extended operator is the sum of its quadratic
forms on the active-coordinate restrictions. -/
theorem inner_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x y : EuclideanSpace ℂ (I × S)) :
    ⟪rightFiberwiseMap (S := S) G x, y⟫_ℂ =
      ∑ s : S, ⟪G (rightFiber x s), rightFiber y s⟫_ℂ := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Extending an operator by free right coordinates preserves positivity. -/
theorem isPositive_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsPositive) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsPositive := by
  refine ⟨isSymmetric_rightFiberwiseMap G hG.isSymmetric, fun x ↦ ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, inner_rightFiberwiseMap, map_sum] using
    (Finset.sum_nonneg fun (s : S) (_ : s ∈ Finset.univ) ↦ hG.2 (rightFiber x s))

/-- Extending two operators by the same free coordinates preserves their
order. -/
theorem rightFiberwiseMap_mono
    {G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I}
    (h : G.toLinearMap ≤ H.toLinearMap) :
    (rightFiberwiseMap (S := S) G).toLinearMap ≤
      (rightFiberwiseMap (S := S) H).toLinearMap := by
  apply (LinearMap.le_def _ _).mpr
  simpa only [rightFiberwiseMap_sub, toLinearMap_sub] using
    (isPositive_rightFiberwiseMap (S := S) (H - G) h)

/-- Extension by free right coordinates commutes with scalar multiplication
of the active operator. -/
theorem rightFiberwiseMap_smul
    (c : ℂ) (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) (c • G) = c • rightFiberwiseMap (S := S) G := by
  rfl

end ContinuousLinearMap

/-- A change of orthonormal coordinates preserves and reflects operator
order. -/
theorem LinearIsometryEquiv.conj_le_conj_iff
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (G H : E →ₗ[ℂ] E) :
    U.toLinearEquiv.conj G ≤ U.toLinearEquiv.conj H ↔ G ≤ H := by
  rw [LinearMap.le_def, ← _root_.map_sub U.toLinearEquiv.conj H G]
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.le_def] using!
    (LinearMap.isPositive_linearIsometryEquiv_conj_iff (T := H - G) U)
