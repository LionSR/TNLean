/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNet
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNetPolynomial
import TNLean.MPS.AreaLaw.ViableSet.FiniteBoundarySelection
import TNLean.MPS.AreaLaw.ViableSet.BoundaryTraceNormSDP
import TNLean.MPS.AreaLaw.ViableSet.LeadingPower
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingBounds
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.RationalSearch

/-!
# Canonical rational search and its overlap reserve

Canonical approximation thresholds leave a specified overlap reserve for rationalizing
the selected columns. The search therefore yields rational viable matrix product data.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–478, Lemmas `l:leading` and `l:within`, lines 493–515, and Claim `c:2`,
lines 520–527.

**Scope restriction (physical viability applications):** The size-trimming viability
conclusions for physical chains assume `0 < L` and `2 ≤ q`, as recorded in
`docs/paper-gaps/lvv13_nontrivial_chain.tex`, and use the library's
uniform cut bound rather than the sharper AKLV dependence; see
`docs/paper-gaps/lvv13_constant_bond.tex`. Taking the union over actual bond dimensions
avoids extending a bond isometry beyond the dimension of the right physical space.
The boundary nets use the corrected matrix-space exponent recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_trace_norm_net.pdf.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The canonical approximate-certificate thresholds leave enough of the sharp LVV
overlap margin to rationalize the selected columns with parameter `1 / 16224`.
For normalized range-one chains the required gap bound `Δ ≤ 4` follows from the
Hamiltonian norm estimate. -/
theorem canonical_search_rationalization_overlap_budget
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hΔ : 0 < Δ) (hΔ₄ : Δ ≤ 4)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    let repair := κ + 2 * n * ε
    let boundaryError := eη + 2 * r * εb + δ + repair
    2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
        2 * (1 / 16224) ≤ 1 / 12 := by
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * r * εb + δ + repair
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hcr : 2 * (Δ / 169) ^ 2 ≤ Δ / 169 := by
    nlinarith only [mul_nonneg hΔ.le (sub_nonneg.mpr hΔ₄), hΔ]
  have hbase : 2 * (6 * (Δ / 169) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)))) ≤ 14 * (Δ / 169) := by
    have heq : 2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L))) =
        2 * (Δ / 169) ^ 2 := by field_simp [hL0]
    rw [heq]
    linarith only [hcr]
  have herr := fullyApproxSDP_errors_with_trace_energy_slack_fit_rationalization_margin
    hL hκ hε hεb hδ heη heK
  have htotal : 2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) ≤
      14 * (Δ / 169) + Δ / 2704 := by
    calc
      2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) =
          2 * (6 * (Δ / 169) +
            2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)))) +
          2 * ((4 * L * repair + eK) + 2 * L * boundaryError) := by ring
      _ ≤ 14 * (Δ / 169) + Δ / 2704 := add_le_add hbase (by
        simpa only [repair, boundaryError, add_assoc] using herr)
  have hscaled := div_le_div_of_nonneg_right htotal hΔ.le
  have hleft : (2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
      2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError))) / Δ ≤
      (14 * (Δ / 169) + Δ / 2704) / Δ := by
    exact hscaled
  have hright : (14 * (Δ / 169) + Δ / 2704) / Δ +
      2 * (1 / 16224) = 1 / 12 := by
    field_simp [ne_of_gt hΔ]
    ring
  calc
    2 * (6 * (Δ / 169) + (4 * L * repair + eK) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
        2 * (1 / 16224) ≤
        (14 * (Δ / 169) + Δ / 2704) / Δ + 2 * (1 / 16224) :=
      add_le_add_left hleft _
    _ = 1 / 12 := hright

/-- Exact feasible compressed data, bounded fixed matrices, and positive rationalization
meshes determine an executable rational search whose returned code produces the physical
LVV viable vector.  The objective and boundary thresholds are chosen canonically, and
the conclusion retains the selected rational codes, their height and approximation
bounds, the returned certificate, exact search equation, decoded exact-data feasibility
certificate, the comparison between actual and canonical operand lengths, and the
resulting comparison between actual and canonical schoolbook costs, together with the
direct explicit bit-cost bound and canonical compressed-input bit-size bound for the
selected codes. -/
theorem ChainHamiltonian.exists_viable_vector_of_canonical_rational_search
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ) {S : Set (LeftBlockVector L q k)}
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    let r := Fintype.card (CutSite L q k × Fin m)
    let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
    let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
    let Dt := rationalApproxDataBoundaryThreshold
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
    let θA := rationalUniformCertificateRoundingMesh n ρ
    let θb := rationalUniformCertificateRoundingMesh r ρ
    let inputBitSizeBound := compressedSDPInputBitSizeBound
      (Fintype.card (CutLeft L q k)) n r
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
    let bitLength := rationalCertificateOperandBitLength
      (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
      (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
      (rationalCompressedSDPApproximationCodeHeight RK RX θZ θK θX ε εb)
      ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
    let costBound := uniformCertificateSearchCardBound (CutSite L q k × Fin m)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) *
      ((n ^ 2 + 3 * r ^ 2 + 3) +
        (2 * n ^ 3 + 2 * r ^ 3 +
          (Fintype.card (CutLeft L q k) * r) * n ^ 2 +
            (Fintype.card (CutLeft L q k) * r) ^ 2 * n)) *
        rationalSchoolbookOperationCost bitLength
    uniformCertificateSearchSchoolbookBitCost
        (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
        n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ≤
      costBound ∧
    ∃ QZ : RationalRectMatrixCode
        ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n),
      ∃ QK : RationalRectMatrixCode (Fin n) (Fin n),
        ∃ QX : RationalRectMatrixCode
            (CutSite L q k × Fin m) (CutSite L q k × Fin m),
          let actualBitLength := rationalCertificateOperandBitLength
            (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
            (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
            (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb)
            ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
            ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb)
          ∃ c : RationalCertificateCode (CutSite L q k × Fin m) n,
            actualBitLength ≤ bitLength ∧
            uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) actualBitLength ≤
              uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) bitLength ∧
            uniformCertificateSearchSchoolbookBitCost
                (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m)
                n (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) actualBitLength ≤
              costBound ∧
            compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q k)) n r
                (rationalCompressedSDPInputCodeHeight QZ QK QX ε εb) ≤
              inputBitSizeBound ∧
            rationalCompressedSDPInputCodeHeight QZ QK QX ε εb ≤
                rationalCompressedSDPApproximationCodeHeight
                  RK RX θZ θK θX ε εb ∧
            (∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ) ∧
            (∀ i j, ‖(K - QK.decode) i j‖ ≤ θK) ∧
            (∀ i j, ‖(X - QX.decode) i j‖ ≤ θX) ∧
            searchRationalCertificateCodeGridOfTolerances η κ ε εb ρ
              QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
              ((r : ℚ) ^ 2 * Dt) Dt (2 * θA) (2 * θb) (2 * θb) = some c ∧
            IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
              (((η + ρ : ℚ) : ℝ))
              ((Et : ℝ) + (n : ℝ) ^ 2 *
                approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
                  (((ε + ρ : ℚ) : ℝ)) * θK)
              (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
              (((εb + ρ : ℚ) : ℝ))
              (((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
                (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 *
                  θZ * approxSDPDensityEntryBound n
                    (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)))
              c.1.decode c.2.1.decode c.2.2.1.decode ∧
            ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
              ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
              (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
              1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, hheight, hZclose, hKclose, hXclose, hfind, hcost⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hbudget := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
      ((r : ℚ) ^ 2 * Dt) Dt
      (2 * rationalUniformCertificateRoundingMesh n ρ)
      (2 * rationalUniformCertificateRoundingMesh r ρ)
      (2 * rationalUniformCertificateRoundingMesh r ρ) hfind Z K X hZ hθZ.le
      hZclose (by simpa only [K] using hKclose) hXclose
  have hbitLength := rationalCertificateOperandBitLength_mono_height
    (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
    (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ)
    ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hheight
  have hactualCost := uniformCertificateSearchSchoolbookBitCost_mono_operand
    (Fintype.card (CutLeft L q k)) (CutSite L q k × Fin m) n
    (η : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (ρ : ℝ) hbitLength
  have hactualBound := hactualCost.trans hcost
  have hinputSize := compressedSDPInputBitSizeBound_mono_height
    (Fintype.card (CutLeft L q k)) n r hheight
  refine ⟨?_, QZ, QK, QX, c, ?_, ?_, ?_, ?_, hheight, hZclose, ?_, hXclose,
    ?_, ?_, ?_⟩
  · simpa only [r, K, Et, Dt] using hcost
  · simpa only [r, K, Et, Dt] using hbitLength
  · simpa only [r, K, Et, Dt] using hactualCost
  · simpa only [r, K, Et, Dt] using hactualBound
  · simpa only [r] using hinputSize
  · simpa only [K] using hKclose
  · simpa only [r, K, Et, Dt] using hfind
  · simpa only [r, K, Et, Dt] using hexact
  apply h.exists_viable_vector_of_rational_search_result hL hq hΔ HL B hsplit
    hHL hBS hBn hgs W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
  simpa only [r, K, Et, Dt] using hbudget

/-- The canonical executable rational search directly returns compact rational
one-twelfth-viable MPS data when the retained finite family already has rational MPS
representations.  The canonical numerical thresholds leave rationalization share
one over 16224.  This is the rational-output form of LVV13, algo53.tex,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_canonical_rational_search
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (S : Finset (LeftBlockVector L q k)) {b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 16224 : ℝ) / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m coeff)) := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, -, hZclose, hKclose, hXclose, hfind, -⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hleading := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hΔ₄ : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hrational := canonical_search_rationalization_overlap_budget hL hΔ hΔ₄
    hκfit hεfit hεbfit hδfit' heηfit heKfit'
  apply h.exists_rationalViableMPSData_of_rational_search_result hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
    (by simpa only [r, K, Et, Dt] using hleading)
    (by norm_num : (0 : ℝ) < 1 / 16224) (by norm_num : (1 : ℝ) / 16224 < 1)
  convert hrational using 1
  simp only [r, K, Et, Dt]
  ring_nf

/-- The canonical executable rational search transports the compact coordinate-rational
invariant from one LVV cut to the next, with the canonical rationalization share
`1 / 16224`.  This is the successive-iteration form of LVV13, `algo53.tex`,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_canonical_rational_search
    {L q k : ℕ} [NeZero q] (h : ChainHamiltonian L q 1 1) (hL : 0 < L) (hq : 2 ≤ q)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsplit : h.operator = HL + B)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hBS : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (leftBlock L (k - 1))ᶜ)
    (hBn : ‖B‖ ≤ 2 * L) {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState h.operator E₀ Γ Δ)
    (S : Finset (LeftBlockVector L q k)) {s₀ b Hv : ℕ} {δin : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δin S)
    {m n : ℕ} [Nonempty (Fin n)] [Nonempty (CutSite L q k × Fin m)]
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (x : (CutLeft L q k × CutSite L q k) × Fin m → ℂ)
    {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hwx : WithLp.ofLp w ∘ (gluingCut L q k).symm =
      ((1 : Matrix (CutLeft L q k × CutSite L q k)
        (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ x)
    (hwE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + 6 * √((Δ / 169) ^ 2))
    (X : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hXphysical : rectangularTraceNorm
      (partialTraceFirst (vecMulVec x (star x)) - X) ≤ ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {η E κ ε εb δ ρ : ℚ} {RK RX θZ θK θX : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (η : ℝ) (E : ℝ) (κ : ℝ) (ε : ℝ) (εb : ℝ) (δ : ℝ) A P N)
    (hρ : 0 < ρ) (hRK : 0 ≤ RK) (hRX : 0 ≤ RX)
    (hθZ : 0 < θZ) (hθK : 0 < θK) (hθX : 0 < θX)
    (hK : ∀ i j,
      ‖(Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) i j‖ ≤ RK)
    (hX : ∀ i j, ‖X i j‖ ≤ RX)
    (heη : 0 ≤ (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L))
    (hκfit : (((κ + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεfit : 2 * n * (((ε + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (hεbfit : 2 * Fintype.card (CutSite L q k × Fin m) *
      (((εb + ρ : ℚ) : ℝ)) ≤ Δ / (129792 * L))
    (heηfit : (((η + ρ : ℚ) : ℝ)) - ((Δ / 169) ^ 2) / (2 * L) ≤
      Δ / (259584 * L))
    (heKfit : let K := Zᴴ *
        (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      max ((E : ℝ) + ‖K‖ * (ρ : ℝ) + (n : ℝ) ^ 2 * C * θK) 0 + (ρ : ℝ) -
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * C * θK ≤ Δ / 16224)
    (hδfit : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n
        (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ))
      (r : ℝ) ^ 2 * ((δ : ℝ) + 3 * (ρ : ℝ) + (((r : ℝ) ^ 2 + 1) * θX) +
        ((r : ℝ) ^ 2 + 1) *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))) ≤
        Δ / (259584 * L)) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := (1 / 16224 : ℝ) / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12)
          (spanColumnFamily S m coeff)) := by
  let r := Fintype.card (CutSite L q k × Fin m)
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Et := rationalApproxDataEnergyThreshold n E κ ε ρ K θK
  let Dt := rationalApproxDataBoundaryThreshold
    (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
  obtain ⟨QZ, QK, QX, c, -, hZclose, hKclose, hXclose, hfind, -⟩ :=
    hcert.exists_fixed_data_codes_and_search_result_canonical_thresholds
      hZ hρ hRK hRX hθZ hθK hθX (by simpa only [K] using hK) hX
  have heKfit' : (Et : ℝ) -
      (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re +
        (n : ℝ) ^ 2 * approxSDPDensityEntryBound n
          (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) * θK ≤ Δ / 16224 :=
    (rationalApproxDataEnergyThreshold_sub_add_error_le_max n E κ ε ρ K θK _
      (by exact_mod_cast hρ)).trans
        (by simpa only [K] using heKfit)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hεplus : 0 ≤ (((ε + ρ : ℚ) : ℝ)) := by
    have hεnonneg : 0 ≤ (ε : ℝ) := hcert.hε
    have hρnonneg : 0 ≤ (ρ : ℝ) := by exact_mod_cast hρ.le
    norm_num only [Rat.cast_add]
    positivity
  have hCpos : 0 < approxSDPDensityEntryBound n
      (((κ + ρ : ℚ) : ℝ)) (((ε + ρ : ℚ) : ℝ)) :=
    approxSDPDensityEntryBound_pos hn hεplus
  have hδnonneg : 0 ≤ (δ : ℝ) :=
    (rectangularTraceNorm_nonneg _).trans hcert.hresidual
  have hboundaryNonneg : 0 ≤ (δ : ℝ) + 2 * (ρ : ℝ) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) := by
    have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    positivity
  have hδfit' : ((((r : ℚ) ^ 2 * Dt : ℚ) : ℝ)) + (r : ℝ) ^ 2 * θX +
      (r : ℝ) ^ 2 * (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ *
        approxSDPDensityEntryBound n (((κ + ρ : ℚ) : ℝ))
          (((ε + ρ : ℚ) : ℝ)) * (2 + θZ)) ≤ Δ / (259584 * L) :=
    (rationalApproxDataBoundaryTotalError_le
      (Fintype.card (CutLeft L q k)) n r δ κ ε ρ θZ θX
      (by exact_mod_cast hρ) hboundaryNonneg).trans
        (by simpa only [r] using hδfit)
  have hleading := fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    hL hΔ.le hκfit hεfit hεbfit hδfit' heηfit heKfit'
  have hΔ₄ : Δ ≤ 4 := by
    simpa only [mul_one] using h.gap_le_four_mul_of_range_one hL hq hgs
  have hrational := canonical_search_rationalization_overlap_budget hL hΔ hΔ₄
    hκfit hεfit hεbfit hδfit' heηfit heKfit'
  apply h.exists_rationalCoordinateData_of_rational_search_result hL hq hΔ
    HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hXphysical Z hZ hZZ
    η κ ε εb ρ QZ QK QX ε εb (η + ρ) Et (κ + ρ) (ε + ρ) (εb + ρ)
    ((r : ℚ) ^ 2 * Dt) Dt
    (2 * rationalUniformCertificateRoundingMesh n ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ)
    (2 * rationalUniformCertificateRoundingMesh r ρ) hfind hθZ.le hZclose
    (by simpa only [K] using hKclose) hXclose heη
    (by simpa only [r, K, Et, Dt] using hleading)
    (by norm_num : (0 : ℝ) < 1 / 16224) (by norm_num : (1 : ℝ) / 16224 < 1)
  convert hrational using 1
  simp only [r, K, Et, Dt]
  ring_nf


end TNLean.MPS.AreaLaw
