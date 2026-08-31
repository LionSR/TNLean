/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.SupportCompletion
import TNLean.MPS.MPDO.SitewisePhysicalMatrix

/-!
# Recovery from a sitewise physical isometry

An isometric change of the one-site physical basis induces an isometric
embedding of every finite chain.  Conjugation by the adjoint recovers matrices
on the range of this embedding.  Adding a fixed output on the orthogonal
complement extends this partial inverse to a trace-preserving completely
positive map on the entire enlarged matrix algebra.

The construction is uniform in the chain length and applies, in particular,
to virtual-boundary closures of periodic matrix product operators.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

/-- A trace-preserving completely positive extension of conjugation by the
adjoint of a sitewise physical isometry. -/
noncomputable def sitewisePhysicalRecovery
    (V : Matrix (Fin e) (Fin d) ℂ) (N : ℕ) [NeZero d] :
    Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  let W := sitewisePhysicalMatrix V N
  let P := W * Wᴴ
  Matrix.supportCompletion (singleKrausMap Wᴴ) P
    (Matrix.faithfulDensity (Fin N → Fin d))

/-- The sitewise physical recovery is a quantum channel when the one-site
matrix is an isometry. -/
theorem sitewisePhysicalRecovery_isKrausCPTP
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) (N : ℕ)
    [NeZero d] :
    IsKrausCPTP (sitewisePhysicalRecovery V N) := by
  let W := sitewisePhysicalMatrix V N
  let P := W * Wᴴ
  have hW : Wᴴ * W = 1 := sitewisePhysicalMatrix_isometry V hV N
  have hPherm : P.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self W
  have hPidem : P * P = P := by
    change (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ
    calc
      (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by
        simp only [Matrix.mul_assoc]
      _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
  have hEtrace : ∀ X, Matrix.trace (singleKrausMap Wᴴ X) =
      Matrix.trace (P * X) := by
    intro X
    simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose, P]
    exact Matrix.trace_mul_cycle Wᴴ X W
  change IsKrausCPTP
    (Matrix.supportCompletion (singleKrausMap Wᴴ) P
      (Matrix.faithfulDensity (Fin N → Fin d)))
  exact Matrix.supportCompletion_isKrausCPTP
    (singleKrausMap Wᴴ) P (Matrix.faithfulDensity (Fin N → Fin d))
    (singleKrausMap_isKrausCP Wᴴ) hPherm hPidem hEtrace
    (Matrix.faithfulDensity_posDef (Fin N → Fin d)).posSemidef
    (Matrix.faithfulDensity_trace (Fin N → Fin d))

/-- The sitewise physical recovery is a left inverse to conjugation by the
sitewise isometry. -/
theorem sitewisePhysicalRecovery_apply_singleKrausMap
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) (N : ℕ)
    [NeZero d] (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    sitewisePhysicalRecovery V N
        (singleKrausMap (sitewisePhysicalMatrix V N) X) = X := by
  let W := sitewisePhysicalMatrix V N
  let P := W * Wᴴ
  have hW : Wᴴ * W = 1 := sitewisePhysicalMatrix_isometry V hV N
  have hPherm : P.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self W
  have hPidem : P * P = P := by
    change (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ
    calc
      (W * Wᴴ) * (W * Wᴴ) = W * (Wᴴ * W) * Wᴴ := by
        simp only [Matrix.mul_assoc]
      _ = W * Wᴴ := by rw [hW, Matrix.mul_one]
  have hsupported : P * singleKrausMap W X * P = singleKrausMap W X := by
    simp only [singleKrausMap_apply, P]
    calc
      (W * Wᴴ) * (W * X * Wᴴ) * (W * Wᴴ) =
          W * (Wᴴ * W) * X * (Wᴴ * W) * Wᴴ := by
        simp only [Matrix.mul_assoc]
      _ = W * X * Wᴴ := by rw [hW]; simp
  change Matrix.supportCompletion (singleKrausMap Wᴴ) P
      (Matrix.faithfulDensity (Fin N → Fin d))
      (singleKrausMap W X) = X
  rw [Matrix.supportCompletion_apply_of_supported
    (singleKrausMap Wᴴ) P (Matrix.faithfulDensity (Fin N → Fin d)) _
    hPherm hPidem hsupported]
  simp only [singleKrausMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    Wᴴ * (W * X * Wᴴ) * W = (Wᴴ * W) * X * (Wᴴ * W) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hW]; simp

/-- The sitewise physical recovery removes an isometric physical basis change
from every virtual-boundary closure. -/
theorem sitewisePhysicalRecovery_physCloseN
    (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (M : MPOTensor d D) (N : ℕ) [NeZero d]
    (X : Matrix (Fin D) (Fin D) ℂ) :
    sitewisePhysicalRecovery V N
        (physCloseN (changePhysicalBasis V M) N X) = physCloseN M N X := by
  rw [← singleKrausMap_sitewisePhysicalMatrix_physCloseN]
  exact sitewisePhysicalRecovery_apply_singleKrausMap V hV N (physCloseN M N X)

end MPOTensor
