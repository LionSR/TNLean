/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.CertificateSearch

/-!
# Rational input representations and coordinate counts

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Exact rational input representation required by the finite arithmetic certificate
tester.  This structure deliberately separates the numerical input assumption from the
classical construction of the coordinate isometry in the LVV existence argument. -/
structure RationalCompressedSDPInputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (ε εb : ℝ) where
  /-- Common height bound for every rational coordinate in the fixed input. -/
  height : ℕ
  z_height : Matrix.HasRationalEntriesOfHeight height Z
  objective_height : Matrix.HasRationalEntriesOfHeight height K
  boundary_height : Matrix.HasRationalEntriesOfHeight height X
  densityShift_height : HasRationalComplexCoordinatesOfHeight height (ε : ℂ)
  boundaryShift_height : HasRationalComplexCoordinatesOfHeight height (εb : ℂ)

/-- A rational scalar, regarded as complex, has coordinate height bounded by the
maximum of its rational height and one. -/
theorem ratCast_hasRationalComplexCoordinatesOfHeight (q : ℚ) :
    HasRationalComplexCoordinatesOfHeight (max (rationalHeight q) 1) (q : ℂ) := by
  refine ⟨q, 0, ?_, le_max_left _ _, ?_⟩
  · apply Complex.ext <;> simp
  · simp [rationalHeight]

/-- Canonical common coordinate height of three rational fixed-data codes and two
rational spectral shifts. -/
def rationalCompressedSDPInputCodeHeight
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b)) (ε εb : ℚ) : ℕ :=
  max Z.height <| max K.height <| max X.height <|
    max (max (rationalHeight ε) 1) (max (rationalHeight εb) 1)

/-- Explicit rational codes canonically provide the common fixed-data height required
by the bit-cost analysis. -/
def rationalCompressedSDPInputEncodingOfCodes
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (K : RationalRectMatrixCode (Fin n) (Fin n))
    (X : RationalRectMatrixCode (s × b) (s × b)) (ε εb : ℚ) :
    RationalCompressedSDPInputEncoding Z.decode K.decode X.decode (ε : ℝ) (εb : ℝ) where
  height := rationalCompressedSDPInputCodeHeight Z K X ε εb
  z_height := Z.decode_hasRationalEntriesOfHeight.mono <| le_max_left _ _
  objective_height := K.decode_hasRationalEntriesOfHeight.mono <|
    (le_max_left _ _).trans (le_max_right _ _)
  boundary_height := X.decode_hasRationalEntriesOfHeight.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  densityShift_height := (ratCast_hasRationalComplexCoordinatesOfHeight ε).mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)
  boundaryShift_height := (ratCast_hasRationalComplexCoordinatesOfHeight εb).mono <|
    (le_max_right _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)

/-- Bounded physical fixed data have rational coordinate codes at prescribed positive
entrywise meshes, with explicit canonical height bounds for all three codes. -/
theorem exists_rational_fixed_data_codes_with_height
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX : ℝ} (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          QZ.height ≤ rationalBoundedMatrixGridHeight 1 θZ ∧
          QK.height ≤ rationalBoundedMatrixGridHeight RK θK ∧
          QX.height ≤ rationalBoundedMatrixGridHeight RX θX ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX := by
  obtain ⟨Z', hZ'rat, hZ'close⟩ :=
    exists_rational_isometry_approximation hθZ Z hZ
  obtain ⟨K', hK'rat, hK'close⟩ :=
    exists_rational_rectangular_approximation hRK hθK K hK
  obtain ⟨X', hX'rat, hX'close⟩ :=
    exists_rational_rectangular_approximation hRX hθX X hX
  obtain ⟨QZ, hQZdecode, hQZheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hZ'rat
  obtain ⟨QK, hQKdecode, hQKheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hK'rat
  obtain ⟨QX, hQXdecode, hQXheight⟩ :=
    RationalRectMatrixCode.exists_code_of_hasRationalEntriesOfHeight hX'rat
  refine ⟨QZ, QK, QX, hQZheight, hQKheight, hQXheight, ?_, ?_, ?_⟩
  · simpa only [hQZdecode] using hZ'close
  · simpa only [hQKdecode] using hK'close
  · simpa only [hQXdecode] using hX'close

/-- Common input-code height obtained from the three explicit approximation grids and
the two rational cone shifts. -/
noncomputable def rationalCompressedSDPApproximationCodeHeight
    (RK RX θZ θK θX : ℝ) (ε εb : ℚ) : ℕ :=
  max (rationalBoundedMatrixGridHeight 1 θZ) <|
    max (rationalBoundedMatrixGridHeight RK θK) <|
      max (rationalBoundedMatrixGridHeight RX θX) <|
        max (max (rationalHeight ε) 1) (max (rationalHeight εb) 1)

/-- Canonical rational objective threshold absorbing fixed-data approximation losses. -/
noncomputable def rationalApproxDataEnergyThreshold
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ) : ℚ :=
  rationalNonnegativeUpperApproximation
    ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK)
    (ρ : ℝ)

/-- Canonical rational boundary threshold absorbing all fixed-data approximation
losses, including the coordinate-map perturbation. -/
noncomputable def rationalApproxDataBoundaryThreshold
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) : ℚ :=
  rationalNonnegativeUpperApproximation
    ((δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
      (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) *
          (2 + θZ))) (ρ : ℝ)

theorem le_rationalApproxDataEnergyThreshold
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ) :
    (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) := by
  exact le_rationalNonnegativeUpperApproximation _ _

theorem le_rationalApproxDataBoundaryThreshold
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) :
    (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) *
            (2 + θZ)) ≤
      (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) := by
  exact le_rationalNonnegativeUpperApproximation _ _

theorem rationalApproxDataEnergyThreshold_le
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ)
    (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) ≤
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK) 0 + (ρ : ℝ) := by
  exact rationalNonnegativeUpperApproximation_le hρ

theorem rationalApproxDataBoundaryThreshold_le
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) ≤
      max ((δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
            ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) 0 + (ρ : ℝ) := by
  exact rationalNonnegativeUpperApproximation_le hρ

theorem rationalApproxDataEnergyThreshold_le_add_mesh
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK : ℝ)
    (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ) * θK) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) ≤
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK + (ρ : ℝ) := by
  simpa only [max_eq_left hnonneg] using
    rationalApproxDataEnergyThreshold_le n E κ ε ρ K θK hρ

theorem rationalApproxDataBoundaryThreshold_le_add_mesh
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
      (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) :
    (rationalApproxDataBoundaryThreshold a n r δ κ ε ρ θZ θX : ℝ) ≤
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
        (a * (n : ℝ) ^ 2 * θZ *
          approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
            ((ε + ρ : ℚ) : ℝ) * (2 + θZ)) + (ρ : ℝ) := by
  simpa only [max_eq_left hnonneg] using
    rationalApproxDataBoundaryThreshold_le a n r δ κ ε ρ θZ θX hρ

/-- After canonical upper rounding, the objective contribution is controlled by the
unrounded energy discrepancy, the fixed-matrix error, and one additional mesh unit. -/
theorem rationalApproxDataEnergyThreshold_sub_add_error_le
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK Ephys : ℝ)
    (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
      approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ) * θK) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      (E : ℝ) - Ephys + ‖K‖ * (ρ : ℝ) +
        2 * ((n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK) + (ρ : ℝ) := by
  have hthreshold := rationalApproxDataEnergyThreshold_le_add_mesh
    n E κ ε ρ K θK hρ hnonneg
  linarith

/-- Without a sign assumption on the unrounded objective threshold, the same estimate
holds with its nonnegative part.  This is the form used for Hamiltonians whose energy
origin has not been fixed. -/
theorem rationalApproxDataEnergyThreshold_sub_add_error_le_max
    (n : ℕ) (E κ ε ρ : ℚ) (K : Matrix (Fin n) (Fin n) ℂ) (θK Ephys : ℝ)
    (hρ : 0 < (ρ : ℝ)) :
    (rationalApproxDataEnergyThreshold n E κ ε ρ K θK : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK ≤
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * θK) 0 + (ρ : ℝ) - Ephys +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * θK := by
  have hthreshold := rationalApproxDataEnergyThreshold_le n E κ ε ρ K θK hρ
  linarith

/-- The boundary error produced by the canonical rational threshold is bounded solely
in terms of the unrounded residual, the rational mesh, and the two fixed-data errors. -/
theorem rationalApproxDataBoundaryTotalError_le
    (a n r : ℕ) (δ κ ε ρ : ℚ) (θZ θX : ℝ) (hρ : 0 < (ρ : ℝ))
    (hnonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (a * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
          ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) :
    ((((r : ℚ) ^ 2 * rationalApproxDataBoundaryThreshold
          a n r δ κ ε ρ θZ θX : ℚ) : ℝ)) +
        (r : ℝ) ^ 2 * θX + (r : ℝ) ^ 2 *
          (a * (n : ℝ) ^ 2 * θZ * approxSDPDensityEntryBound n
            ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * (2 + θZ)) ≤
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) +
        (((r : ℝ) ^ 2 + 1) * θX) + ((r : ℝ) ^ 2 + 1) *
          (a * (n : ℝ) ^ 2 * θZ * approxSDPDensityEntryBound n
            ((κ + ρ : ℚ) : ℝ) ((ε + ρ : ℚ) : ℝ) * (2 + θZ))) := by
  have hthreshold := rationalApproxDataBoundaryThreshold_le_add_mesh
    a n r δ κ ε ρ θZ θX hρ hnonneg
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at *
  nlinarith [sq_nonneg (r : ℝ)]

/-- The canonical input height of approximation codes is bounded by the corresponding
three grid heights and the exact heights of the two rational shifts. -/
theorem rationalCompressedSDPInputCodeHeight_le_approximationCodeHeight
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    (RK RX θZ θK θX : ℝ) (ε εb : ℚ)
    (hZ : QZ.height ≤ rationalBoundedMatrixGridHeight 1 θZ)
    (hK : QK.height ≤ rationalBoundedMatrixGridHeight RK θK)
    (hX : QX.height ≤ rationalBoundedMatrixGridHeight RX θX) :
    rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
      rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb := by
  unfold rationalCompressedSDPInputCodeHeight
  unfold rationalCompressedSDPApproximationCodeHeight
  omega

/-- Simultaneous rational approximation of the three physical fixed matrices, stated
directly in the code representation used by the executable search.  Besides the three
entrywise error bounds, the conclusion controls the canonical common input height. -/
theorem exists_rational_fixed_data_codes_with_common_height
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX : ℝ} (ε εb : ℚ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
            rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX := by
  obtain ⟨QZ, QK, QX, hQZheight, hQKheight, hQXheight,
      hQZclose, hQKclose, hQXclose⟩ :=
    exists_rational_fixed_data_codes_with_height Z hZ K X hRK hRX
      hθZ hθK hθX hK hX
  refine ⟨QZ, QK, QX, ?_, hQZclose, hQKclose, hQXclose⟩
  exact rationalCompressedSDPInputCodeHeight_le_approximationCodeHeight
    QZ QK QX RK RX θZ θK θX ε εb hQZheight hQKheight hQXheight

/-- Arbitrary bounded physical fixed data admit a complete rational encoding.  The
coordinate map, objective, and boundary center retain explicit entrywise approximation
witnesses, while the two spectral shifts are chosen as positive rational numbers below
their prescribed targets. -/
theorem exists_rational_compressedSDPInputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {RK RX θZ θK θX tε tεb : ℝ} (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (htε : 0 < tε) (htεb : 0 < tεb)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    ∃ ε εb : ℝ, 0 < ε ∧ ε ≤ tε ∧ 0 < εb ∧ εb ≤ tεb ∧
      ∃ QZ : Matrix ((a × s) × b) (Fin n) ℂ,
        (∀ i j, ‖(Z - QZ) i j‖ ≤ θZ) ∧
        ∃ QK : Matrix (Fin n) (Fin n) ℂ,
          (∀ i j, ‖(K - QK) i j‖ ≤ θK) ∧
          ∃ QX : Matrix (s × b) (s × b) ℂ,
            (∀ i j, ‖(X - QX) i j‖ ≤ θX) ∧
            Nonempty (RationalCompressedSDPInputEncoding QZ QK QX ε εb) := by
  let ε := rationalPositiveTolerance tε
  let εb := rationalPositiveTolerance tεb
  obtain ⟨QZ, hQZ, hQZclose⟩ := exists_rational_isometry_approximation hθZ Z hZ
  obtain ⟨QK, hQK, hQKclose⟩ :=
    exists_rational_rectangular_approximation hRK hθK K hK
  obtain ⟨QX, hQX, hQXclose⟩ :=
    exists_rational_rectangular_approximation hRX hθX X hX
  let HZ := rationalBoundedMatrixGridHeight 1 θZ
  let HK := rationalBoundedMatrixGridHeight RK θK
  let HX := rationalBoundedMatrixGridHeight RX θX
  let Hε := rationalPositiveToleranceOrder tε + 1
  let Hεb := rationalPositiveToleranceOrder tεb + 1
  let HD := max HZ (max HK (max HX (max Hε Hεb)))
  have hZHD : HZ ≤ HD := le_max_left _ _
  have hKHD : HK ≤ HD := (le_max_left _ _).trans (le_max_right _ _)
  have hXHD : HX ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hεHD : Hε ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hεbHD : Hεb ≤ HD :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨ε, εb, rationalPositiveTolerance_pos tε,
    rationalPositiveTolerance_le htε, rationalPositiveTolerance_pos tεb,
    rationalPositiveTolerance_le htεb, QZ, hQZclose, QK, hQKclose, QX, hQXclose,
    ⟨{
      height := HD
      z_height := hQZ.mono hZHD
      objective_height := hQK.mono hKHD
      boundary_height := hQX.mono hXHD
      densityShift_height :=
        (rationalPositiveTolerance_hasRationalCoordinatesOfHeight tε).mono hεHD
      boundaryShift_height :=
        (rationalPositiveTolerance_hasRationalCoordinatesOfHeight tεb).mono hεbHD }⟩⟩

/-- Rational approximation of a classically selected coordinate isometry extends any
rational objective, boundary target, and spectral shifts to a complete exact input
encoding for the finite tester.  The boundary residual grows by at most `ω`. -/
theorem exists_rational_coordinate_inputEncoding
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b] {n : ℕ}
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (A K : Matrix (Fin n) (Fin n) ℂ) (X P N : Matrix (s × b) (s × b) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb : ℕ} {ω ζ : ℝ} (hω : 0 < ω)
    (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hresidual : ∀ i j, ‖((compressedBoundaryLM Z A - X) - (P - N)) i j‖ ≤ ζ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ)) :
    ∃ Q : Matrix ((a × s) × b) (Fin n) ℂ,
      Nonempty (RationalCompressedSDPInputEncoding Q K X ε εb) ∧
      ∀ i j, ‖((compressedBoundaryLM Q A - X) - (P - N)) i j‖ ≤ ζ + ω := by
  obtain ⟨Q, hQ, hQresidual⟩ :=
    exists_rational_coordinate_map_with_boundary_allowance Z hZ A X P N hω hA hresidual
  let HQ := rationalBoundedMatrixGridHeight 1
    (rationalCoordinateMapTolerance (Fintype.card a) n ω)
  let HD := max HQ (max HK (max HX (max Hε Hεb)))
  have hQHD : HQ ≤ HD := le_max_left _ _
  have hKHD : HK ≤ HD := (le_max_left _ _).trans (le_max_right _ _)
  have hXHD : HX ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hεHD : Hε ≤ HD :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hεbHD : Hεb ≤ HD :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨Q, ⟨{
    height := HD
    z_height := hQ.mono hQHD
    objective_height := hK.mono hKHD
    boundary_height := hX.mono hXHD
    densityShift_height := hε.mono hεHD
    boundaryShift_height := hεb.mono hεbHD }⟩, hQresidual⟩

/-- Number of rational scalar coordinates in the fixed compressed input: two per
complex entry of `Z`, `K`, and `X`, and two for each spectral shift. -/
def compressedSDPInputRationalCoordinateCount (a n r : ℕ) : ℕ :=
  2 * ((a * r) * n + n ^ 2 + r ^ 2 + 2)

/-- The explicit coordinate map alone contributes two rational scalar coordinates for
each of its `a r n` complex entries. -/
theorem coordinateMapRationalCoordinateCount_le_compressedSDPInput
    (a n r : ℕ) :
    2 * ((a * r) * n) ≤ compressedSDPInputRationalCoordinateCount a n r := by
  unfold compressedSDPInputRationalCoordinateCount
  omega

/-- The compressed-input coordinate count is monotone in all three matrix orders. -/
theorem compressedSDPInputRationalCoordinateCount_mono
    {a a' n n' r r' : ℕ} (ha : a ≤ a') (hn : n ≤ n') (hr : r ≤ r') :
    compressedSDPInputRationalCoordinateCount a n r ≤
      compressedSDPInputRationalCoordinateCount a' n' r' := by
  unfold compressedSDPInputRationalCoordinateCount
  gcongr

/-- Bit-size bound for a compressed input whose rational coordinates have height at
most `H`. -/
def compressedSDPInputBitSizeBound (a n r H : ℕ) : ℕ :=
  compressedSDPInputRationalCoordinateCount a n r * (Nat.log2 H + 1)

/-- The bit-size bound dominates the number of rational scalar coordinates even at the
smallest possible height. -/
theorem compressedSDPInputRationalCoordinateCount_le_bitSizeBound
    (a n r H : ℕ) :
    compressedSDPInputRationalCoordinateCount a n r ≤
      compressedSDPInputBitSizeBound a n r H := by
  unfold compressedSDPInputBitSizeBound
  nth_rewrite 1 [← Nat.mul_one (compressedSDPInputRationalCoordinateCount a n r)]
  exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))

/-- Any explicit encoding covered by this model has bit-size at least the number of
rational scalar coordinates in the coordinate map. -/
theorem coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
    (a n r H : ℕ) :
    2 * ((a * r) * n) ≤ compressedSDPInputBitSizeBound a n r H :=
  (coordinateMapRationalCoordinateCount_le_compressedSDPInput a n r).trans
    (compressedSDPInputRationalCoordinateCount_le_bitSizeBound a n r H)

/-- The compressed rational input-size bound is monotone in its common coordinate
height. -/
theorem compressedSDPInputBitSizeBound_mono_height
    (a n r : ℕ) {H H' : ℕ} (hH : H ≤ H') :
    compressedSDPInputBitSizeBound a n r H ≤
      compressedSDPInputBitSizeBound a n r H' := by
  unfold compressedSDPInputBitSizeBound
  apply Nat.mul_le_mul_left
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (b := 2) hH) 1

/-- An exponential bound on rational-coordinate height gives a linear bound on the
number of bits per rational coordinate. -/
theorem compressedSDPInputBitSizeBound_le_of_height_le_two_pow
    (a n r H p : ℕ) (hH : H ≤ 2 ^ p) :
    compressedSDPInputBitSizeBound a n r H ≤
      compressedSDPInputRationalCoordinateCount a n r * (p + 1) := by
  unfold compressedSDPInputBitSizeBound
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  rw [Nat.log2_eq_log_two]
  calc
    Nat.log 2 H ≤ Nat.log 2 (2 ^ p) := Nat.log_mono_right hH
    _ = p := Nat.log_pow (by omega) p

/-- If all three matrix orders are at most `M`, the compressed input has at most
`2(M³ + 2M² + 2)` rational scalar coordinates. -/
theorem compressedSDPInputRationalCoordinateCount_le_of_order_bounds
    {a n r M : ℕ} (ha : a ≤ M) (hn : n ≤ M) (hr : r ≤ M) :
    compressedSDPInputRationalCoordinateCount a n r ≤
      2 * (M ^ 3 + 2 * M ^ 2 + 2) := by
  have harn : (a * r) * n ≤ M ^ 3 := by
    calc
      (a * r) * n ≤ (M * M) * M := Nat.mul_le_mul (Nat.mul_le_mul ha hr) hn
      _ = M ^ 3 := by ring
  have hn2 : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hn 2
  have hr2 : r ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hr 2
  unfold compressedSDPInputRationalCoordinateCount
  omega

/-- Polynomial matrix orders and exponentially bounded coordinate height give the
corresponding explicit polynomial compressed-input bit-size bound. -/
theorem compressedSDPInputBitSizeBound_le_of_order_and_height_bounds
    {a n r H M p : ℕ} (ha : a ≤ M) (hn : n ≤ M) (hr : r ≤ M)
    (hH : H ≤ 2 ^ p) :
    compressedSDPInputBitSizeBound a n r H ≤
      2 * (M ^ 3 + 2 * M ^ 2 + 2) * (p + 1) := by
  exact (compressedSDPInputBitSizeBound_le_of_height_le_two_pow a n r H p hH).trans
    (Nat.mul_le_mul_right (p + 1)
      (compressedSDPInputRationalCoordinateCount_le_of_order_bounds ha hn hr))

/-- Rational scalar-coordinate count for the structured compressed input.  The support
isometry is encoded by its `n m |S|` expansion coefficients rather than by all of its
ambient matrix entries. -/
def structuredCompressedSDPInputRationalCoordinateCount
    (S : Finset (LeftBlockVector L q k)) (m n r : ℕ) : ℕ :=
  2 * (boundarySupportCoordinateCoefficientCount S m n + n ^ 2 + r ^ 2 + 2)

/-- Bit-size bound for a structured compressed input whose rational coordinates have
common height at most `H`. -/
def structuredCompressedSDPInputBitSizeBound
    (S : Finset (LeftBlockVector L q k)) (m n r H : ℕ) : ℕ :=
  structuredCompressedSDPInputRationalCoordinateCount S m n r * (Nat.log2 H + 1)

/-- A rational encoding of the compressed input in support coordinates.  The ambient
isometry is represented by the coefficients of its bond slices in the retained family
`S`; the remaining data are the objective, boundary center, and two spectral shifts.

This is the arithmetic datum implicit in LVV13, `algo53.tex`, equation `eq:conv`,
lines 472--476.  Its height is kept explicit because a finite spanning family alone does
not control the conditioning of its coordinate map. -/
structure RationalStructuredCompressedSDPInputEncoding
    (S : Finset (LeftBlockVector L q k)) (m n r : ℕ)
    (c : Fin n → Fin m → S → ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin r) (Fin r) ℂ) (ε εb : ℝ) where
  height : ℕ
  coefficient_height : ∀ j a s, HasRationalComplexCoordinatesOfHeight height (c j a s)
  objective_height : Matrix.HasRationalEntriesOfHeight height K
  boundary_height : Matrix.HasRationalEntriesOfHeight height X
  densityShift_height : HasRationalComplexCoordinatesOfHeight height (ε : ℂ)
  boundaryShift_height : HasRationalComplexCoordinatesOfHeight height (εb : ℂ)

/-- Canonical common height obtained from separate bounds on the five parts of a
structured compressed input. -/
def rationalStructuredCompressedSDPInputHeight
    (Hc HK HX Hε Hεb : ℕ) : ℕ :=
  max Hc (max HK (max HX (max Hε Hεb)))

/-- A common exponential bound on the five component heights bounds their canonical
maximum by the same exponential. -/
theorem rationalStructuredCompressedSDPInputHeight_le_two_pow
    {Hc HK HX Hε Hεb p : ℕ} (hc : Hc ≤ 2 ^ p) (hK : HK ≤ 2 ^ p)
    (hX : HX ≤ 2 ^ p) (hε : Hε ≤ 2 ^ p) (hεb : Hεb ≤ 2 ^ p) :
    rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb ≤ 2 ^ p := by
  simp only [rationalStructuredCompressedSDPInputHeight, max_le_iff]
  exact ⟨hc, hK, hX, hε, hεb⟩

/-- Separate rational-height bounds assemble into a structured compressed-input
encoding at their canonical common maximum. -/
def rationalStructuredCompressedSDPInputEncodingOfHeightBounds
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    (c : Fin n → Fin m → S → ℂ) (K : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin r) (Fin r) ℂ) (ε εb : ℝ)
    {Hc HK HX Hε Hεb : ℕ}
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight Hc (c j a s))
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ)) :
    RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb where
  height := rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb
  coefficient_height j a s := (hc j a s).mono (le_max_left _ _)
  objective_height := hK.mono <| (le_max_left _ _).trans (le_max_right _ _)
  boundary_height := hX.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
  densityShift_height := hε.mono <|
    (le_max_left _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)
  boundaryShift_height := hεb.mono <|
    (le_max_right _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _)

end TNLean.MPS.AreaLaw
