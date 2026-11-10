/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation

/-!
# Storage of rational open-chain tensor parameters

Count the actual entries on the varying virtual spaces, together with the
scalar cap. Each real or imaginary rational coordinate is stored by its
reduced signed numerator and positive denominator. Their total binary
length is polynomial when the bond dimension is polynomial and the
common height has a polynomial binary exponent.

The finite index spaces are specified by the open-chain representation.
The estimates concern its scalar and tensor entries, and assert no cost
for constructing the representation or performing arithmetic on it.
-/

namespace TNLean.MPS.AreaLaw

/-- The number of actual local entries on the varying virtual spaces is at
most the chain length times the physical dimension times the square of the
advertised virtual dimension. -/
theorem OBCChainTensor.card_parameterIndex_le {q D n : ℕ} (A : OBCChainTensor q D n) :
    Fintype.card (OBCChainTensor.ParameterIndex A) ≤ n * q * D ^ 2 := by
  simp only [OBCChainTensor.ParameterIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin]
  calc
    ∑ p : Fin n, q * (A.bondDim p.castSucc * A.bondDim p.succ) ≤
        ∑ _p : Fin n, q * (D * D) :=
      Finset.sum_le_sum fun p _ ↦ Nat.mul_le_mul_left q
        (Nat.mul_le_mul (A.bondDim_le p.castSucc) (A.bondDim_le p.succ))
    _ = n * q * D ^ 2 := by simp [pow_two]; ring

/-- Binary digits for a rational coordinate: one numerator-sign bit, the
binary digits of its reduced numerator magnitude, and the binary digits of
its reduced positive denominator. A zero magnitude is allotted one digit. -/
def rationalCoordinateBitCount (x : ℚ) : ℕ :=
  1 + (Nat.log2 x.num.natAbs + 1) + (Nat.log2 x.den + 1)

/-- The signed numerator and denominator lengths are bounded by twice the
uniform rational bit length, together with one sign bit. -/
theorem rationalCoordinateBitCount_le (x : ℚ) :
    rationalCoordinateBitCount x ≤ 2 * rationalBitLength x + 1 := by
  have hnum : Nat.log2 x.num.natAbs ≤ Nat.log2 (rationalHeight x) := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (num_natAbs_le_rationalHeight x)
  have hden : Nat.log2 x.den ≤ Nat.log2 (rationalHeight x) := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (den_le_rationalHeight x)
  dsimp only [rationalCoordinateBitCount, rationalBitLength]
  omega

/-- A common rational height bounds the total binary storage of the scalar
cap and every actual local entry, with real and imaginary coordinates
represented by reduced signed fractions. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.exists_coordinates_storage_le
    {L q n H b : ℕ} {v : LeftBlockVector L q n}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) :
    ∃ (x₀ y₀ : ℚ) (x y : OBCChainTensor.ParameterIndex R.data.tensor → ℚ),
      R.data.scalar = ⟨(x₀ : ℝ), (y₀ : ℝ)⟩ ∧
      (∀ e, OBCChainTensor.parameters R.data.tensor e = ⟨(x e : ℝ), (y e : ℝ)⟩) ∧
      rationalCoordinateBitCount x₀ + rationalCoordinateBitCount y₀ +
        ∑ e, (rationalCoordinateBitCount (x e) + rationalCoordinateBitCount (y e)) ≤
          6 * (1 + n * q * (max 1 b) ^ 2) * (Nat.log2 H + 1) := by
  obtain ⟨x₀, y₀, hscalar, hx₀, hy₀⟩ := R.scalar_height.exists_bitLength_le
  choose x y htensor hx hy using fun e : OBCChainTensor.ParameterIndex R.data.tensor ↦
    (R.tensor_height e.1 e.2.1 e.2.2.1 e.2.2.2).exists_bitLength_le
  have hpair (a c : ℚ) (ha : rationalBitLength a ≤ Nat.log2 H + 1)
      (hc : rationalBitLength c ≤ Nat.log2 H + 1) :
      rationalCoordinateBitCount a + rationalCoordinateBitCount c ≤ 6 * (Nat.log2 H + 1) := by
    have ha' := rationalCoordinateBitCount_le a
    have hc' := rationalCoordinateBitCount_le c
    omega
  have hcard : Fintype.card (OBCChainTensor.ParameterIndex R.data.tensor) ≤
      n * q * (max 1 b) ^ 2 := by
    simpa only [← max_assoc, max_self] using
      OBCChainTensor.card_parameterIndex_le R.data.tensor
  refine ⟨x₀, y₀, x, y, hscalar, htensor, ?_⟩
  calc
    _ ≤ 6 * (Nat.log2 H + 1) +
        ∑ _e : OBCChainTensor.ParameterIndex R.data.tensor, 6 * (Nat.log2 H + 1) :=
      Nat.add_le_add (hpair x₀ y₀ hx₀ hy₀)
        (Finset.sum_le_sum fun e _ ↦ hpair (x e) (y e) (hx e) (hy e))
    _ = 6 * (1 + Fintype.card (OBCChainTensor.ParameterIndex R.data.tensor)) *
        (Nat.log2 H + 1) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 (Nat.add_le_add_left hcard 1))

/-- A polynomial bond bound and a quadratic binary height exponent give an
explicit polynomial storage bound for the actual rational tensor data. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.exists_coordinates_storage_le_polynomial
    {L q n b D r E : ℕ} {v : LeftBlockVector L q n}
    (R : RationalLeftOpenMPSRepresentationOfHeight (2 ^ (E * (L + 1) ^ 2)) b v)
    (hn : n ≤ L) (hb : b ≤ D * L ^ r) :
    ∃ (x₀ y₀ : ℚ) (x y : OBCChainTensor.ParameterIndex R.data.tensor → ℚ),
      R.data.scalar = ⟨(x₀ : ℝ), (y₀ : ℝ)⟩ ∧
      (∀ e, OBCChainTensor.parameters R.data.tensor e = ⟨(x e : ℝ), (y e : ℝ)⟩) ∧
      rationalCoordinateBitCount x₀ + rationalCoordinateBitCount y₀ +
        ∑ e, (rationalCoordinateBitCount (x e) + rationalCoordinateBitCount (y e)) ≤
          6 * (1 + L * q * (max 1 (D * L ^ r)) ^ 2) * (1 + E * (L + 1) ^ 2) := by
  obtain ⟨x₀, y₀, x, y, hscalar, htensor, hstorage⟩ := R.exists_coordinates_storage_le
  refine ⟨x₀, y₀, x, y, hscalar, htensor, hstorage.trans ?_⟩
  rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num : 1 < 2)]
  have hcount : n * q * (max 1 b) ^ 2 ≤ L * q * (max 1 (D * L ^ r)) ^ 2 := by
    gcongr
  calc
    _ ≤ 6 * (1 + L * q * (max 1 (D * L ^ r)) ^ 2) * (E * (L + 1) ^ 2 + 1) :=
      Nat.mul_le_mul_right (E * (L + 1) ^ 2 + 1)
        (Nat.mul_le_mul_left 6 (Nat.add_le_add_left hcount 1))
    _ = _ := by ring

end TNLean.MPS.AreaLaw
