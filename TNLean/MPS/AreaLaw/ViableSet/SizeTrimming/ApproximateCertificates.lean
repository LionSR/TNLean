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
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming.CompressedSolutions

/-!
# Approximate semidefinite certificates and viable vectors

Approximate positivity, trace and boundary constraints are repaired at explicit cost.
The resulting density determines viable vectors and rational matrix product data.

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

/-- A fully approximate numerical semidefinite certificate, at the independent precision
targets of `fullyApproxSDP_errors_fit_lvv_margin`, produces the physical LVV viable
vector.  This composes spectral repair of all cone variables, trace repair, the inexact
boundary equation, support expansion, and the leading-vector argument. -/
theorem ChainHamiltonian.exists_viable_vector_of_all_spectral_approx_sdp_certificate
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
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ)
    (hP : P.IsHermitian) (hN : N.IsHermitian)
    {κ ε εb δ : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hεb : 0 ≤ εb) (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ ((Δ / 169) ^ 2) / (2 * L))
    (henergy : (A * (Zᴴ *
      (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z)).trace.re ≤
        (vecMulVec x (star x) *
          (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re)
    (hκbound : κ ≤ Δ / (64896 * L))
    (hεbound : 2 * n * ε ≤ Δ / (64896 * L))
    (hεbbound : 2 * Fintype.card (CutSite L q k × Fin m) * εb ≤
      Δ / (64896 * L))
    (hδbound : δ ≤ Δ / (64896 * L)) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ :=
    exists_density_of_all_spectral_approx_sdp_certificate
      Z hZ K X hA hP hN htrace hε hmin hPmin hNmin hresidual htraces henergy
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans htrace
  have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hresidual
  have hrepair0 : 0 ≤ repair := by dsimp only [repair]; positivity
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    positivity
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have harith := fullyApproxSDP_errors_fit_lvv_margin hL
    hκbound hεbound hεbbound hδbound
  have hnum : 2 * (‖K‖ * repair + ‖B‖ * boundaryError) ≤
      2 * (4 * L * repair + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * (‖K‖ * repair + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by simpa only [repair, boundaryError, add_assoc] using harith)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- A unified approximate certificate yields the physical LVV viable vector whenever
its total repaired energy and boundary error fits the available margin.  This form is
suited to certificates transferred from rational approximations of the fixed matrices,
whose rounding losses need not be assigned to one of the four original tolerances. -/
theorem ChainHamiltonian.exists_viable_vector_of_approx_sdp_error_budget
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
    {κ ε εb δ eK : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L))
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hbudget : 2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((2 * Fintype.card (CutSite L q k × Fin m) * εb + δ) +
        (κ + 2 * n * ε))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hcert.htrace
    exact add_nonneg hκ0 (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hcert.hresidual
    exact add_nonneg
      (add_nonneg (mul_nonneg (by positivity) hcert.hεb) hδ0) hrepair0
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have hnum : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
      2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by
      convert hbudget using 1
      simp only [repair, boundaryError]
      ring)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- The error-budget theorem with an additional auxiliary-trace allowance.  A
certificate with trace budget `η + eη` incurs the extra boundary error `eη`; this is the
form needed for certificates obtained by finite rational search. -/
theorem ChainHamiltonian.exists_viable_vector_of_approx_sdp_error_budget_with_trace_slack
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
    {κ ε εb δ eK eη : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (heη : 0 ≤ eη)
    (hbudget : 2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ) +
        (κ + 2 * n * ε))) ≤ Δ / 2028) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q),
      ‖v‖ = 1 ∧ v ∈ leftSupportSubmodule S ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + Δ / 12 ∧
      1 - 1 / 12 ≤ ‖⟪Γ, v⟫_ℂ‖ := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  have hrepair0 : 0 ≤ repair := by
    dsimp only [repair]
    have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hcert.htrace
    exact add_nonneg hκ0 (mul_nonneg (by positivity) hcert.hε)
  have hboundaryError0 : 0 ≤ boundaryError := by
    dsimp only [boundaryError]
    have hδ0 : 0 ≤ δ := (rectangularTraceNorm_nonneg _).trans hcert.hresidual
    exact add_nonneg
      (add_nonneg (add_nonneg heη (mul_nonneg (by positivity) hcert.hεb)) hδ0)
      hrepair0
  have hHleft : ‖Hleft‖ ≤ 4 * L :=
    (h.leftObjective_norm_bounds HL B hsplit hHL hBn).2
  have hKn : ‖K‖ ≤ 4 * L :=
    (l2_opNorm_isometricCompression_le Z hZ Hleft).trans hHleft
  have hnum : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤
      2 * ((eK + 4 * L * repair) + 2 * L * boundaryError) := by
    gcongr
  have herr : 2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028 :=
    hnum.trans (by
      convert hbudget using 1
      simp only [repair, boundaryError]
      ring)
  apply h.exists_viable_vector_of_compressed_boundary_solution_with_slack hL hq hΔ
    HL B hsplit hHL hBS hBn hgs W hW x hwx hwE X hX Z hZ hZZ σ hσ hσtrace
    (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · exact herr

/-- A repaired approximate semidefinite certificate produces rational viable MPS data
once the sharp leading-vector deficit and the rationalization reserve fit the target.
The statement includes the auxiliary trace slack used by the executable rational search.
It is the certificate-level rational-output step of LVV13, `algo53.tex`, lines 493--527. -/
theorem ChainHamiltonian.exists_rationalViableMPSData_of_approx_sdp_error_budget_with_trace_slack
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
    {κ ε εb δ eK eη ξrat : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hleading : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (1 / 12) S (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  apply h.exists_rationalViableMPSData_of_compressed_boundary_solution_with_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S hS W hW x hwx hwE X hX Z hZ hZZ
      σ hσ hσtrace (hξrat := hξrat) (hξrat1 := hξrat1)
      (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · simpa only [K, Hleft, repair, boundaryError] using hleading
  · simpa only [K, Hleft, repair, boundaryError] using hrational

/-- A repaired approximate semidefinite certificate transports the compact
coordinate-rational invariant from one LVV iteration to the next. -/
theorem ChainHamiltonian.exists_rationalCoordinateData_of_approx_sdp_error_budget_with_trace_slack
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
    {κ ε εb δ eK eη ξrat : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (CutSite L q k × Fin m) (CutSite L q k × Fin m) ℂ}
    (hcert : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy Z
      (Zᴴ * (leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * Z) X
      (((Δ / 169) ^ 2) / (2 * L) + eη)
      ((vecMulVec x (star x) * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))).trace.re + eK) κ ε εb δ A P N)
    (hleading : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * ((eK + ‖K‖ * repair) + ‖B‖ * boundaryError) ≤ Δ / 2028)
    (hξrat : 0 < ξrat) (hξrat1 : ξrat < 1)
    (hrational : let repair := κ + 2 * n * ε
      let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
      let K := Zᴴ * (leftCutOperator k HL ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) * Z
      2 * (6 * (Δ / 169) + (eK + ‖K‖ * repair) + ‖B‖ *
        (2 * (((Δ / 169) ^ 2) / (2 * L)) + boundaryError)) / Δ + 2 * ξrat ≤ 1 / 12) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A₀ := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξrat / (1 + A₀)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (1 / 12) (spanColumnFamily S m c)) := by
  classical
  let Hleft := leftCutOperator k HL ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := Zᴴ * Hleft * Z
  let η := ((Δ / 169) ^ 2) / (2 * L)
  let repair := κ + 2 * n * ε
  let boundaryError := eη + 2 * Fintype.card (CutSite L q k × Fin m) * εb + δ + repair
  obtain ⟨σ, hσ, hσtrace, _hclose, hσboundary, hσenergy⟩ := hcert.exists_density hZ
  apply h.exists_rationalCoordinateData_of_compressed_boundary_solution_with_slack
    hL hq hΔ HL B hsplit hHL hBS hBn hgs S D W hW x hwx hwE X hX Z hZ hZZ
      σ hσ hσtrace (hξrat := hξrat) (hξrat1 := hξrat1)
      (ξ := eK + ‖K‖ * repair) (δ := boundaryError)
  · simpa only [K, Hleft, repair, add_assoc] using hσenergy
  · simpa only [η, boundaryError, repair, add_assoc] using hσboundary
  · simpa only [K, Hleft, repair, boundaryError] using hleading
  · simpa only [K, Hleft, repair, boundaryError] using hrational

end TNLean.MPS.AreaLaw
