/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalMatrixCodes
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalStorage
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ContractionHeights
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalContraction

/-!
# Heights of explicit rational coordinates

Bounds on a decoded complex number control the unique rational coordinates
stored in its code. Thus common-denominator and norm estimates apply to the
actual fractions returned by rational arithmetic, including intermediate
values in a tensor contraction.
-/

namespace TNLean.MPS.AreaLaw

/-- Rational real and imaginary coordinates are determined by their complex value. -/
theorem RationalComplexCode.decode_injective : Function.Injective decodeRationalComplex := by
  intro z w h
  apply Prod.ext
  · have hre := congrArg Complex.re h
    change (z.1 : ℝ) = (w.1 : ℝ) at hre
    exact_mod_cast hre
  · have him := congrArg Complex.im h
    change (z.2 : ℝ) = (w.2 : ℝ) at him
    exact_mod_cast him

/-- An existential height bound on a decoded value bounds the fractions actually
stored in its rational coordinate pair. -/
theorem RationalComplexCode.decode_height_iff {H : ℕ} (z : ℚ × ℚ) :
    HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex z) ↔
      rationalHeight z.1 ≤ H ∧ rationalHeight z.2 ≤ H := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have heq : z = (x, y) := RationalComplexCode.decode_injective hxy
    simpa only [heq] using And.intro hx hy
  · rintro ⟨hx, hy⟩
    exact ⟨z.1, z.2, rfl, hx, hy⟩

/-- A common Gaussian-integer denominator and a norm bound control both
reduced rational coordinates actually stored in a complex code. -/
theorem RationalComplexCode.coordinate_heights_of_common_denominator {M R : ℕ}
    (z : ℚ × ℚ) (hden : HasGaussianIntegerDenominator M (decodeRationalComplex z))
    (hnorm : ‖decodeRationalComplex z‖ ≤ (R : ℝ)) :
    rationalHeight z.1 ≤ M * max 1 R ∧ rationalHeight z.2 ≤ M * max 1 R :=
  (decode_height_iff z).mp (hden.height_of_norm_le hnorm)

/-- A decoded height bound controls the total signed-fraction storage of the
two rational coordinates actually stored in the code. -/
theorem RationalComplexCode.bitCount_le_of_decode_height {H : ℕ} {z : ℚ × ℚ}
    (hz : HasRationalComplexCoordinatesOfHeight H (decodeRationalComplex z)) :
    rationalCoordinateBitCount z.1 + rationalCoordinateBitCount z.2 ≤
      6 * (Nat.log2 H + 1) := by
  obtain ⟨hx, hy⟩ := (RationalComplexCode.decode_height_iff z).mp hz
  have hxbit := rationalBitLength_le hx
  have hybit := rationalBitLength_le hy
  have hxcount := rationalCoordinateBitCount_le z.1
  have hycount := rationalCoordinateBitCount_le z.2
  omega

/-- The actual reduced fractions returned by sequential rational contraction
obey the common-denominator coordinate bound of their represented MPS. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.coefficientCode_height
    {L q k H b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex R.data.tensor → ℚ × ℚ)
    (hcap : decodeRationalComplex cap = R.data.scalar)
    (hP : ∀ e, decodeRationalComplex (P e) = OBCChainTensor.parameters R.data.tensor e)
    (σ : Fin k → Fin q) :
    let z := OBCChainTensor.coefficientOfRationalParameters R.data.tensor cap P σ
    rationalHeight z.1 ≤
        RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b k ∧
      rationalHeight z.2 ≤
        RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b k := by
  dsimp only
  apply (RationalComplexCode.decode_height_iff _).mp
  rw [R.data.decode_coefficientOfRationalParameters cap P hcap hP σ]
  exact R.coordinate_height_common_denominator hk (leftConfigOfFin σ)

/-- The numerator signs, numerator magnitudes, and denominators of the returned
coefficient have a storage bound inherited from the actual tensor parameters. -/
theorem RationalLeftOpenMPSRepresentationOfHeight.coefficientCode_bitCount
    {L q k H b : ℕ} {v : LeftBlockVector L q k}
    (R : RationalLeftOpenMPSRepresentationOfHeight H b v) (hk : k ≤ L)
    (cap : ℚ × ℚ) (P : OBCChainTensor.ParameterIndex R.data.tensor → ℚ × ℚ)
    (hcap : decodeRationalComplex cap = R.data.scalar)
    (hP : ∀ e, decodeRationalComplex (P e) = OBCChainTensor.parameters R.data.tensor e)
    (σ : Fin k → Fin q) :
    let z := OBCChainTensor.coefficientOfRationalParameters R.data.tensor cap P σ
    rationalCoordinateBitCount z.1 + rationalCoordinateBitCount z.2 ≤
      6 * (Nat.log2
        (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b k) + 1) := by
  dsimp only
  apply RationalComplexCode.bitCount_le_of_decode_height
  exact (RationalComplexCode.decode_height_iff _).mpr
    (R.coefficientCode_height hk cap P hcap hP σ)

end TNLean.MPS.AreaLaw
