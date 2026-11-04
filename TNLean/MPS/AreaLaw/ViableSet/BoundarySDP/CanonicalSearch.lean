/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SearchSoundness

/-!
# Canonical rational search with explicit error and cost

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

namespace IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

set_option maxHeartbeats 400000 in
-- Elaborating the explicit cost inequality unfolds several nested cardinality bounds.
/-- Completeness after rational approximation of all fixed data, paired with the
schoolbook bit-cost bound for the same executable search.  The operand length is the
canonical height determined by the three input codes and the two cone shifts. -/
theorem exists_approx_data_search_result_and_cost_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (QZ : RationalRectMatrixCode ((a × s) × b) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode (s × b) (s × b))
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ Et Dt : ℚ} {θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ) (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j, ‖(K - QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (hEt : let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK ≤ (Et : ℝ))
    (hDt : let r := Fintype.card (s × b)
      let C := approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ)
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    let r := Fintype.card (s × b)
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let bitLength := rationalCertificateOperandBitLength (Fintype.card a) (s × b)
      n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
        (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb)
        ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
        ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    (∃ c, searchRationalCertificateCodeGridOfTolerances
      η κ ε εb ρ QZ QK QX ε εb
      (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
    uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
      uniformCertificateSearchCardBound (s × b)
          n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
        ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
          (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
            (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
              (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
          rationalSchoolbookOperationCost bitLength := by
  dsimp only
  constructor
  · exact h.exists_approx_data_search_result QZ QK QX hZ hρ hθZ
      hZclose hKclose hXclose hEt hDt
  · exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
      (Fintype.card a) _
      (s × b) n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)

set_option maxHeartbeats 400000 in
-- The conclusion retains the complete explicit cost expression for the selected codes.
/-- End-to-end selection of rational fixed-data codes.  Bounded exact data determine
codes at the prescribed meshes; their canonical common height has the explicit grid
bound, and the resulting executable search succeeds with its schoolbook cost bound. -/
theorem exists_fixed_data_codes_search_result_and_cost_le
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ Et Dt : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (hEt : let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK ≤ (Et : ℝ))
    (hDt : let r := Fintype.card (s × b)
      let C := (approxSDPDensityEntryBound n ((κ + ρ : ℚ) : ℝ)
        ((ε + ρ : ℚ) : ℝ))
      (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 * (Fintype.card a * (n : ℝ) ^ 2 * θZ * C * (2 + θZ)) ≤
          (Dt : ℝ)) :
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
              rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
          let r := Fintype.card (s × b)
          let θA := rationalUniformCertificateRoundingMesh n ρ
          let θb := rationalUniformCertificateRoundingMesh r ρ
          let bitLength := rationalCertificateOperandBitLength
            (Fintype.card a) (s × b)
            n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
              (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
              ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          (∃ c, searchRationalCertificateCodeGridOfTolerances
            η κ ε εb ρ QZ QK QX ε εb
            (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
          uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
              n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
            uniformCertificateSearchCardBound (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
              ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                  (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                    (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                rationalSchoolbookOperationCost bitLength := by
  obtain ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose⟩ :=
    exists_rational_fixed_data_codes_with_common_height
      Z hZ K X ε εb hRK hRX hθZ hθK hθX hK hX
  refine ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose, ?_⟩
  dsimp only
  constructor
  · exact h.exists_approx_data_search_result QZ QK QX hZ hρ hθZ.le
      hZclose hKclose hXclose hEt hDt
  · exact uniformCertificateSearchSchoolbookBitCost_le_uniformOperandBound
      (Fintype.card a) _
      (s × b) n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)

set_option maxHeartbeats 400000 in
-- The explicit search-and-cost conclusion contains several nested cardinality bounds.
/-- The end-to-end fixed-data search with no external threshold choices.  The objective
and boundary thresholds are the canonical rational ceilings of their exact real loss
expressions. -/
theorem exists_fixed_data_codes_search_result_and_cost_le_canonical_thresholds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    let r := Fintype.card (s × b)
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card a) n r δ κ ε ρ θZ θX
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
              rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
          (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
          (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
          (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
          let θA := rationalUniformCertificateRoundingMesh n ρ
          let θb := rationalUniformCertificateRoundingMesh r ρ
          let bitLength := rationalCertificateOperandBitLength
            (Fintype.card a) (s × b)
            n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
              (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
              ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          (∃ c, searchRationalCertificateCodeGridOfTolerances
            η κ ε εb ρ QZ QK QX ε εb
            (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c) ∧
          uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
              n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
            uniformCertificateSearchCardBound (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
              ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                  (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                    (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                rationalSchoolbookOperationCost bitLength := by
  dsimp only
  apply h.exists_fixed_data_codes_search_result_and_cost_le hZ hρ hRK hRX
    hθZ hθK hθX hK hX
  · exact le_rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  · exact le_rationalApproxDataBoundaryThreshold
      (Fintype.card a) n (Fintype.card (s × b)) δ κ ε ρ θZ θX

/-- Compact canonical-search package for downstream physical soundness.  It retains the
selected fixed-data codes, their common height bound, all three approximation witnesses,
the returned certificate code, the exact executable search equation, and the schoolbook
bit-cost bound for that same search. -/
theorem exists_fixed_data_codes_and_search_result_canonical_thresholds
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Encodable (s × b)] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hZ : Zᴴ * Z = 1) (hρ : 0 < ρ)
    (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j, ‖K i j‖ ≤ RK) (hX : ∀ i j, ‖X i j‖ ≤ RX) :
    let r := Fintype.card (s × b)
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card a) n r δ κ ε ρ θZ θX
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let bitLength := rationalCertificateOperandBitLength
      (Fintype.card a) (s × b) n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
      ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    ∃ QZ : RationalRectMatrixCode ((a × s) × b) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode (s × b) (s × b),
          ∃ c : RationalCertificateCode (s × b) n,
            rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
                rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb ∧
            (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
            (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
            (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
            searchRationalCertificateCodeGridOfTolerances
              η κ ε εb ρ QZ QK QX ε εb
              (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c ∧
            uniformCertificateSearchSchoolbookBitCost (Fintype.card a) (s × b)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
              uniformCertificateSearchCardBound (s × b)
                  n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
                ((n ^ 2 + 3 * Fintype.card (s × b) ^ 2 + 3) +
                  (2 * n ^ 3 + 2 * Fintype.card (s × b) ^ 3 +
                    (Fintype.card a * Fintype.card (s × b)) * n ^ 2 +
                      (Fintype.card a * Fintype.card (s × b)) ^ 2 * n)) *
                  rationalSchoolbookOperationCost bitLength := by
  dsimp only
  obtain ⟨QZ, QK, QX, hheight, hZclose, hKclose, hXclose, hsearch, hcost⟩ :=
    h.exists_fixed_data_codes_search_result_and_cost_le_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX hK hX
  obtain ⟨c, hfind⟩ := hsearch
  exact ⟨QZ, QK, QX, c, hheight, hZclose, hKclose, hXclose, hfind, hcost⟩

end IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy

end TNLean.MPS.AreaLaw
