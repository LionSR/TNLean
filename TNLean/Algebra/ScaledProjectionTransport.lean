/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BinaryProjectionFamily

/-!
# Binary projection transport through a scaled partial isometry

A Hermitian idempotent commuting with the initial support induces an orthogonal
projection on the original physical space. Its complement completes the
measurement on that entire space, including the unused physical directions.

Source: SCP10, arXiv:1001.3807, the local isometry and interference measurement,
lines 2582–2615; auxiliary finite-dimensional statement.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Matrix
variable {H K : Type*} [Fintype H] [Fintype K]

/-- Transport a virtual projection through a scaled partial isometry.
Source: SCP10, local physical isometry in the interference argument,
lines 2582–2615. -/
def scaledProjectionTransport (T : Matrix H K ℂ) (D : Matrix K K ℂ) (c : ℝ) :
    Matrix H H ℂ :=
  (c : ℂ)⁻¹ • (T * D * T.conjTranspose)

/-- The transported projection is positive and intertwines the original map.
Source: SCP10, lines 2582–2615; auxiliary scaled-isometry identity. -/
theorem scaledProjectionTransport_properties
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    (scaledProjectionTransport T D c).IsHermitian ∧
      (scaledProjectionTransport T D c).PosSemidef ∧
      scaledProjectionTransport T D c * scaledProjectionTransport T D c =
        scaledProjectionTransport T D c ∧
      scaledProjectionTransport T D c * T = T * D := by
  let Q := scaledProjectionTransport T D c
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hQT : Q * T = T * D := by
    change (c : ℂ)⁻¹ • (T * D * T.conjTranspose) * T = _
    rw [Matrix.smul_mul, Matrix.mul_assoc, hGram, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hc', one_smul, Matrix.mul_assoc, hcomm,
      ← Matrix.mul_assoc, hTP]
  have hQh : Q.IsHermitian :=
    (Matrix.isHermitian_mul_mul_conjTranspose T hDh).smul (by simp [IsSelfAdjoint])
  have hQI : Q * Q = Q := by
    change Q * ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) = Q
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQT,
      Matrix.mul_assoc T D D, hDI]
    rfl
  refine ⟨hQh, ?_, hQI, hQT⟩
  simpa only [hQh.eq, hQI] using Matrix.posSemidef_self_mul_conjTranspose Q

/-- The original physical space carries a complete binary projection measurement.
Both outcomes act on the actual coefficient map by the corresponding virtual
projection. Source: SCP10, interference measurement, lines 2605–2615;
auxiliary finite-dimensional transport statement. -/
theorem exists_binaryProjectionFamily_transport [DecidableEq H] [DecidableEq K]
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    ∃ Q : Bool → Matrix H H ℂ,
      (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
      (∀ b r, Q b * Q r = if b = r then Q b else 0) ∧
      (∑ b, Q b) = 1 ∧
      Q true = scaledProjectionTransport T D c ∧
      Q true * T = T * D ∧ Q false * T = T * (1 - D) := by
  obtain ⟨hQh, _, hQI, hQT⟩ :=
    scaledProjectionTransport_properties T P D c hc hGram hTP hcomm hDh hDI
  let Q : Bool → Matrix H H ℂ :=
    fun b => if b then scaledProjectionTransport T D c else
      1 - scaledProjectionTransport T D c
  obtain ⟨hh, hi, hs⟩ := binaryProjectionFamily_complete
    (scaledProjectionTransport T D c) hQh hQI
  refine ⟨Q, hh, hi, hs, rfl, hQT, ?_⟩
  change (1 - scaledProjectionTransport T D c) * T = T * (1 - D)
  rw [Matrix.sub_mul, Matrix.one_mul, hQT, Matrix.mul_sub, Matrix.mul_one]

end Matrix
