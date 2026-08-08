/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Wigner.ProjectivePureState
import TNLean.Channel.Wigner.Upstream.WignerRigidity

/-!
# Projective carrier identification for Wigner rigidity

This module identifies rays over `Fin d → ℂ`, used for TNLean's pure-state
matrices, with rays over `EuclideanSpace ℂ (Fin d)`, used by the Wigner rigidity
theorem adapted from `zblore/csd-lean4` commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`.

The identification is induced by `WithLp.linearEquiv`. It preserves transition
probability, unitary actions, and coordinatewise conjugation.
-/

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

variable {d : ℕ}

/-- Send a finite-coordinate ray to the same ray on its Euclidean-space carrier. -/
noncomputable def toEuclideanRay (p : ℙ ℂ (Fin d → ℂ)) :
    ℙ ℂ (EuclideanSpace ℂ (Fin d)) :=
  p.map (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.injective

/-- Forget the Euclidean-space wrapper on a finite-coordinate ray. -/
noncomputable def fromEuclideanRay (p : ℙ ℂ (EuclideanSpace ℂ (Fin d))) :
    ℙ ℂ (Fin d → ℂ) :=
  p.map (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap
    (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).injective

/-- Forgetting the Euclidean wrapper after adding it fixes every finite-coordinate ray. -/
@[simp]
theorem fromEuclideanRay_toEuclideanRay (p : ℙ ℂ (Fin d → ℂ)) :
    fromEuclideanRay (toEuclideanRay p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      simp [toEuclideanRay, fromEuclideanRay, Projectivization.map_mk]

/-- Adding the Euclidean wrapper after forgetting it fixes every Euclidean-space ray. -/
@[simp]
theorem toEuclideanRay_fromEuclideanRay
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin d))) :
    toEuclideanRay (fromEuclideanRay p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      simp [toEuclideanRay, fromEuclideanRay, Projectivization.map_mk]

private theorem transitionProbability_toEuclideanRay_mk
    (v w : Fin d → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ((transProb (toEuclideanRay (Projectivization.mk ℂ v hv))
      (toEuclideanRay (Projectivization.mk ℂ w hw)) : ℝ) : ℂ) =
        transitionProbability (Projectivization.mk ℂ v hv)
          (Projectivization.mk ℂ w hw) := by
  simp only [toEuclideanRay, Projectivization.map_mk]
  rw [transProb_mk, transitionProbability_mk]
  let e := (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm
  let x := e v
  let y := e w
  have hxy : (inner ℂ x y : ℂ) = star v ⬝ᵥ w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hyx : (inner ℂ y x : ℂ) = star w ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hxxInner : (inner ℂ x x : ℂ) = star v ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hyyInner : (inner ℂ y y : ℂ) = star w ⬝ᵥ w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hxx : ((‖x‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
    push_cast
    exact (inner_self_eq_norm_sq_to_K x).symm.trans hxxInner
  have hyy : ((‖y‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
    push_cast
    exact (inner_self_eq_norm_sq_to_K y).symm.trans hyyInner
  have hnormSq : ((‖(inner ℂ x y : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      (inner ℂ x y : ℂ) * inner ℂ y x := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      inner_conj_symm]
    ring
  unfold transProbVec
  change ((‖(inner ℂ x y : ℂ)‖ ^ 2 /
      (‖x‖ ^ 2 * ‖y‖ ^ 2) : ℝ) : ℂ) = _
  push_cast at hnormSq hxx hyy ⊢
  rw [hnormSq, hxx, hyy, hxy, hyx]

/-- The upstream real transition probability agrees with TNLean's complex
transition probability under the carrier identification. -/
theorem transProb_toEuclideanRay_ofReal_eq (p q : ℙ ℂ (Fin d → ℂ)) :
    ((transProb (toEuclideanRay p) (toEuclideanRay q) : ℝ) : ℂ) =
      transitionProbability p q := by
  induction p using Projectivization.ind with
  | h v hv =>
      induction q using Projectivization.ind with
      | h w hw => exact transitionProbability_toEuclideanRay_mk v w hv hw

/-- Carrier identification intertwines the upstream projective unitary action
with TNLean's finite-coordinate unitary action. -/
theorem fromEuclideanRay_unitary_smul
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin d))) :
    fromEuclideanRay (U • p) = unitaryAction U (fromEuclideanRay p) := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [smul_mk_eq_mk_toEuclideanLin]
      simp only [fromEuclideanRay, Projectivization.map_mk]
      rw [unitaryAction, Projectivization.map_mk]
      rfl

/-- Carrier identification intertwines upstream and TNLean coordinate
conjugation. -/
theorem fromEuclideanRay_conjProj (p : ℙ ℂ (EuclideanSpace ℂ (Fin d))) :
    fromEuclideanRay (conjProj p) = coordinateConjugation (fromEuclideanRay p) := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [conjProj_mk]
      simp only [fromEuclideanRay, Projectivization.map_mk]
      rw [coordinateConjugation, Projectivization.map_mk]
      rfl

end Projectivization
