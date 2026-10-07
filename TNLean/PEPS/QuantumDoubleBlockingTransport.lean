/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.QuantumDoubleNativeGlobalBlocking
import QICLean.Algebra.OrthogonalProjection

/-!
# Operator transport by the actual physical regrouping

New implementation for SCP10, arXiv:1001.3807v3, Section 7.2, lines 2896–2923.
The unitary sends fine-spin configurations to four-spin K registers. Consequently
the operator on the fine spins is Uᴴ H U. Positive coarse periods suffice here.
The checkerboard comparison uses the proved complete T-to-K contraction.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]
variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "F" => TorusVertex (width * 2) (height * 2)
local notation "V" => TorusVertex width height
local notation "K" => (V → G × G × G × G)
local notation "U" => quantumDoublePhysicalBlockingMatrix
  (G := G) (width := width) (height := height)

/-- Pull back a K-register operator to the original physical spins. -/
def quantumDoubleUnblockOperator (H : Matrix K K ℂ) : Matrix (F → G) (F → G) ℂ :=
  Uᴴ * H * U

/-- Physical regrouping intertwines every pulled-back operator, on the entire
ambient spin space. -/
theorem quantumDoublePhysicalBlockingMatrix_mul_unblockOperator (H : Matrix K K ℂ) :
    U * quantumDoubleUnblockOperator H = H * U := by
  have hU : U * Uᴴ = 1 := quantumDoublePhysicalBlockingMatrix_isUnitaryBetween.2
  simp only [quantumDoubleUnblockOperator, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- Pullback preserves multiplication because the physical regrouping is onto. -/
theorem quantumDoubleUnblockOperator_mul (H J : Matrix K K ℂ) :
    quantumDoubleUnblockOperator (H * J) =
      quantumDoubleUnblockOperator H * quantumDoubleUnblockOperator J := by
  have hU : U * Uᴴ = 1 := quantumDoublePhysicalBlockingMatrix_isUnitaryBetween.2
  calc
    Uᴴ * (H * J) * U = Uᴴ * H * (U * Uᴴ) * J * U := by
      rw [hU, Matrix.mul_one, Matrix.mul_assoc]
    _ = (Uᴴ * H * U) * (Uᴴ * J * U) := by simp only [Matrix.mul_assoc]

/-- Orthogonal projections pull back to orthogonal projections with the actual
physical unitary, without any restriction to the prepared state. -/
theorem quantumDoubleUnblockOperator_isStarProjection (H : Matrix K K ℂ)
    (hH : IsStarProjection H) : IsStarProjection (quantumDoubleUnblockOperator H) :=
  hH.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one U
    quantumDoublePhysicalBlockingMatrix_isUnitaryBetween.2

/-- Commutators are transported on the full ambient physical spaces. -/
theorem quantumDoubleUnblockOperator_commute (H J : Matrix K K ℂ)
    (hHJ : Commute H J) :
    Commute (quantumDoubleUnblockOperator H) (quantumDoubleUnblockOperator J) := by
  change _ * _ = _ * _
  rw [← quantumDoubleUnblockOperator_mul, ← quantumDoubleUnblockOperator_mul, hHJ.eq]

/-- Zero-energy vectors correspond bijectively under physical regrouping. -/
theorem quantumDoubleUnblockOperator_mulVec_eq_zero_iff (H : Matrix K K ℂ)
    (ψ : (F → G) → ℂ) :
    quantumDoubleUnblockOperator H *ᵥ ψ = 0 ↔ H *ᵥ (U *ᵥ ψ) = 0 := by
  constructor
  · intro h
    have hh := congrArg (U *ᵥ ·) h
    rw [Matrix.mulVec_mulVec, quantumDoublePhysicalBlockingMatrix_mul_unblockOperator,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hh
    exact hh
  · intro h
    simp only [quantumDoubleUnblockOperator, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- An operator annihilates the actual fine T network exactly when its blocked
operator annihilates the actual coarse K network. Source: SCP10, equation (7.10). -/
theorem quantumDoubleUnblockOperator_annihilates_checkerboard_iff (H : Matrix K K ℂ) :
    quantumDoubleUnblockOperator H *ᵥ
        (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 ↔
      H *ᵥ (fun τ => torusBondNetwork (fun v c =>
        quantumDoubleKTensor G c.1 c.2.1 c.2.2.1 c.2.2.2 (τ v)) 1 1) = 0 := by
  rw [quantumDoubleUnblockOperator_mulVec_eq_zero_iff,
    quantumDoublePhysicalBlockingMatrix_mulVec_checkerboard]

end TNLean.PEPS
