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
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.ApproximateCertificates

/-!
# Viability from finite rational certificate search

A returned rational certificate gives a viable physical vector when its approximation
errors fit the available spectral margin. Coordinate-height bounds record its finite size.

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

/-- A code returned by the executable rational search yields the physical LVV viable
vector once its exact-data error budget fits the available margin.  The differences
between the rational trace and energy thresholds and their physical targets are charged
as `eη` and `eK`. -/
theorem ChainHamiltonian.exists_viable_vector_of_rational_search_result
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
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection S) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hbudget : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  let K := Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
  let Ephys := (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
    (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, δ', r, C] <;> ring
  apply h.exists_viable_vector_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ hcert
  · exact heη
  · simpa only [eη, eK, Ephys, δ', r, C, K] using hbudget

/-- A code returned by the executable rational certificate search directly produces
compact rational viable MPS data.  Besides the ordinary repaired-certificate margin,
the sharp overlap budget reserves `2 * ξrat` for rationalizing the physical left columns.
This is the executable rational-output step of LVV13, `algo53.tex`, lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_rational_search_result
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
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX ξrat : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hleading : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
      let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
      2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m coeff)) := by
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let Ephys := (vecMulVec x (star x) * Hleft).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
  let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K, Hleft] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, Hleft, δ', r, C] <;> ring
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    exact add_nonneg ((abs_nonneg _).trans hcert.htrace)
      (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    exact add_nonneg
      (add_nonneg
        (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb))
        ((rectangularTraceNorm_nonneg _).trans hcert.hresidual))
      hrepair0
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have hleadingExact :
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 := by
    calc
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
          2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by gcongr
      _ ≤ Δ / 2028 := by
        convert hleading using 1
        simp only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError]
        ring
  have hrationalExact :
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12 := by
    have hinner : 6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) ≤
        6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) := by
      gcongr
    have hscaled := div_le_div_of_nonneg_right hinner hΔ.le
    have hrational' :
        2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat ≤ 1 / 12 := by
      simpa only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError] using hrational
    calc
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat =
          2 * ((6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
            (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
              2 * ξrat := by ring
      _ ≤ 2 * ((6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
            2 * ξrat := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2))
                (2 * ξrat)
      _ = 2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat := by ring
      _ ≤ 1 / 12 := hrational'
  apply h.exists_rationalViableMPSData_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hX Z hZ hZZ
      hcert hleadingExact hξrat hξrat1
  simpa only [K, Hleft, repair, boundaryError] using hrationalExact

/-- A code returned by the executable rational certificate search transports the
coordinate-rational viable-MPS invariant through the repaired certificate and column
rationalization.  This is the successive-iteration form of LVV13, `algo53.tex`,
lines 493--527. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_rational_search_result
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
    (hX : rectangularTraceNorm (partialTraceFirst (vecMulVec x (star x)) - X) ≤
      ((Δ / 169) ^ 2) / (2 * L))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (gridη gridκ gridε gridεb gridω : ℚ)
    (QZ : RationalRectMatrixCode
      ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n))
    (QK : RationalRectMatrixCode (Fin n) (Fin n))
    (QX : RationalRectMatrixCode
      (CutSite L q k × Fin m) (CutSite L q k × Fin m))
    (εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN : ℚ)
    {c : RationalCertificateCode (CutSite L q k × Fin m) n}
    (hfind : searchRationalCertificateCodeGridOfTolerances
      gridη gridκ gridε gridεb gridω QZ QK QX
      εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN = some c)
    {θZ θK θX ξrat : ℝ} (hθZ : 0 ≤ θZ)
    (hZclose : ∀ i j, ‖(Z - QZ.decode) i j‖ ≤ θZ)
    (hKclose : ∀ i j,
      ‖((Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) -
        QK.decode) i j‖ ≤ θK)
    (hXclose : ∀ i j, ‖(X - QX.decode) i j‖ ≤ θX)
    (heη : 0 ≤ (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L))
    (hleading : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      2 * ((4 * L * ((κ : ℝ) + 2 * n * (ε : ℝ)) + eK) +
        2 * L * ((eη + 2 * r * (εb : ℝ) + δ') +
          ((κ : ℝ) + 2 * n * (ε : ℝ)))) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let r := Fintype.card (CutSite L q k × Fin m)
      let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
      let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
      let eK := (E : ℝ) -
        (vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + (n : ℝ) ^ 2 * C * θK
      let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
        (r : ℝ) ^ 2 *
          (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
      let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
      let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
      2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
        2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ coeff : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (coeff j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12)
          (spanColumnFamily S m coeff)) := by
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let Ephys := (vecMulVec x (star x) * Hleft).trace.re
  let r := Fintype.card (CutSite L q k × Fin m)
  let C := approxSDPDensityEntryBound n (κ : ℝ) (ε : ℝ)
  let eη := (η : ℝ) - ((Δ / 169) ^ 2) / (2 * L)
  let eK := (E : ℝ) - Ephys + (n : ℝ) ^ 2 * C * θK
  let δ' := (δ : ℝ) + (r : ℝ) ^ 2 * θX +
    (r : ℝ) ^ 2 *
      (Fintype.card (CutLeft L q k) * (n : ℝ) ^ 2 * θZ * C * (2 + θZ))
  let repair := (κ : ℝ) + 2 * n * (ε : ℝ)
  let boundaryError := eη + 2 * r * (εb : ℝ) + δ' + repair
  have hexact := searchRationalCertificateCodeGridOfTolerances_exact_data_sdp_sound
    gridη gridκ gridε gridεb gridω QZ QK QX
    εA₀ εb₀ η E κ ε εb δ ζ ζA ζP ζN hfind Z K X hZ hθZ
      hZclose (by simpa only [K, Hleft] using hKclose) hXclose
  have hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z K X
      (((Δ / 169) ^ 2) / (2 * L) + eη) (Ephys + eK)
      (κ : ℝ) (ε : ℝ) (εb : ℝ) δ'
      c.1.decode c.2.1.decode c.2.2.1.decode := by
    convert hexact using 1 <;> dsimp [eη, eK, Ephys, Hleft, δ', r, C] <;> ring
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    exact add_nonneg ((abs_nonneg _).trans hcert.htrace)
      (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    exact add_nonneg
      (add_nonneg
        (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb))
        ((rectangularTraceNorm_nonneg _).trans hcert.hresidual))
      hrepair0
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have hleadingExact :
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 := by
    calc
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
          2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by gcongr
      _ ≤ Δ / 2028 := by
        convert hleading using 1
        simp only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError]
        ring
  have hrationalExact :
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
          2 * ξrat ≤ 1 / 12 := by
    have hinner : 6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) ≤
        6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError) := by
      gcongr
    have hscaled := div_le_div_of_nonneg_right hinner hΔ.le
    have hrational' :
        2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat ≤ 1 / 12 := by
      simpa only [eη, eK, Ephys, Hleft, δ', r, C, repair, boundaryError] using hrational
    calc
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
          (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat =
          2 * ((6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
            (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
              2 * ξrat := by ring
      _ ≤ 2 * ((6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ) +
            2 * ξrat := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2))
                (2 * ξrat)
      _ = 2 * (6 * (Δ / 169) + (eK + 4 * L * repair) +
          2 * L * (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ +
            2 * ξrat := by ring
      _ ≤ 1 / 12 := hrational'
  apply h.exists_rationalCoordinateData_of_approx_sdp_error_budget_with_trace_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hX Z hZ hZZ
      hcert hleadingExact hξrat hξrat1
  simpa only [K, Hleft, repair, boundaryError] using hrationalExact


/-- For the physical cut coordinates, the explicit coordinate map contributes two
rational scalars for each of its `q ^ |leftBlock L (k - 1)| * r * n` complex entries.
Thus the ambient factor in the encoding obstruction is the full left-block Hilbert-space
dimension, rather than the compressed order `n`. -/
theorem cutLeft_coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
    (L q k n r H : ℕ) :
    2 * (((q ^ min L (k - 1)) * r) * n) ≤
      compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q k)) n r H := by
  rw [card_cutLeft]
  exact coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound _ _ _ _

/-- At the last cut of a chain with local dimension at least two, the explicit
coordinate-map encoding bound already contains a factor `2 ^ (L - 1)`. -/
theorem twoPow_mul_le_cutLeft_compressedSDPInputBitSizeBound
    (L q n r H : ℕ) (hq : 2 ≤ q) :
    2 * (((2 ^ (L - 1)) * r) * n) ≤
      compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H := by
  calc
    2 * (((2 ^ (L - 1)) * r) * n) ≤ 2 * (((q ^ (L - 1)) * r) * n) := by
      gcongr
    _ = 2 * (((q ^ min L (L - 1)) * r) * n) := by
      rw [min_eq_right (Nat.sub_le L 1)]
    _ ≤ compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H :=
      cutLeft_coordinateMapRationalCoordinateCount_le_compressedSDPInputBitSizeBound
        L q L n r H

/-- For positive compressed and boundary orders, the explicit last-cut input has bit-size
at least `2 ^ L`.  This is the direct exponential obstruction for the ambient-coordinate
encoding used by the rational search. -/
theorem twoPow_le_cutLeft_compressedSDPInputBitSizeBound
    (L q n r H : ℕ) (hL : 0 < L) (hq : 2 ≤ q) (hn : 0 < n) (hr : 0 < r) :
    2 ^ L ≤ compressedSDPInputBitSizeBound (Fintype.card (CutLeft L q L)) n r H := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  calc
    2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; omega
    _ ≤ 2 * (((2 ^ L) * r) * n) := by
      calc
        2 * 2 ^ L = (2 * 2 ^ L) * 1 := by omega
        _ ≤ (2 * 2 ^ L) * (r * n) :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr.ne' hn.ne'))
        _ = 2 * (((2 ^ L) * r) * n) := by ring
    _ ≤ compressedSDPInputBitSizeBound
        (Fintype.card (CutLeft (L + 1) q (L + 1))) n r H :=
      twoPow_mul_le_cutLeft_compressedSDPInputBitSizeBound (L + 1) q n r H hq

end TNLean.MPS.AreaLaw
