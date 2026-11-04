/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ApproximateCertificates

/-!
# Density repair and the LVV numerical error budget

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Every exact feasible compressed SDP point is a fully approximate feasible point with
all four error parameters equal to zero. -/
theorem IsCompressedBoundarySDPFeasibleAtEnergy.toAllSpectralApprox
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ}
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsCompressedBoundarySDPFeasibleAtEnergy Z K X η E A P N) :
    IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E 0 0 0 0 A P N := by
  rcases h with ⟨hA, hAtrace, hP, hN, hsub, htraces, henergy⟩
  have hAmin : 0 ≤ minEigenvalue hA.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hA.isHermitian
    rw [← hi]
    exact hA.eigenvalues_nonneg i
  have hPmin : 0 ≤ minEigenvalue hP.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hP.isHermitian
    rw [← hi]
    exact hP.eigenvalues_nonneg i
  have hNmin : 0 ≤ minEigenvalue hN.isHermitian := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hN.isHermitian
    rw [← hi]
    exact hN.eigenvalues_nonneg i
  refine ⟨hA.isHermitian, hP.isHermitian, hN.isHermitian, ?_, by norm_num,
    ?_, by norm_num, ?_, ?_, ?_, htraces, henergy⟩
  · rw [hAtrace]
    norm_num
  · simpa only [neg_zero] using hAmin
  · simpa only [neg_zero] using hPmin
  · simpa only [neg_zero] using hNmin
  · rw [hsub, sub_self, rectangularTraceNorm_zero]

/-- An exact feasible density produces auxiliary matrices satisfying the unified
finite-precision feasibility statement with every error parameter equal to zero. -/
theorem exists_allSpectralApproxCompressedBoundarySDPFeasibleAtEnergy_zero
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    (hX : X.IsHermitian) {η E : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hAtrace : A.trace = 1)
    (hAboundary : rectangularTraceNorm (compressedBoundaryLM Z A - X) ≤ η)
    (hAenergy : (A * K).trace.re ≤ E) :
    ∃ P N : Matrix (s × b) (s × b) ℂ,
      IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
        Z K X η E 0 0 0 0 A P N := by
  obtain ⟨P, N, hP, hN, hsub, htraces⟩ :=
    (compressedBoundary_rectangularTraceNorm_le_iff_exists_posSemidef_sub
      Z hA.isHermitian X hX η).mp hAboundary
  exact ⟨P, N,
    IsCompressedBoundarySDPFeasibleAtEnergy.toAllSpectralApprox
      ⟨hA, hAtrace, hP, hN, hsub, htraces, hAenergy⟩⟩

/-- A numerical semidefinite certificate may also violate positivity of the auxiliary
boundary matrices by `εb`.  Repairing both by the same shift preserves their difference
and adds only `2 r εb` to the boundary trace budget. -/
theorem exists_density_of_all_spectral_approx_sdp_certificate
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    (Z : Matrix ((a × s) × b) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (s × b) (s × b) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {P N : Matrix (s × b) (s × b) ℂ} (hP : P.IsHermitian) (hN : N.IsHermitian)
    {η E δ κ ε εb : ℝ} (htrace : |1 - A.trace.re| ≤ κ)
    (hε : 0 ≤ ε) (hmin : -ε ≤ minEigenvalue hA)
    (hPmin : -εb ≤ minEigenvalue hP)
    (hNmin : -εb ≤ minEigenvalue hN)
    (hresidual : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P - N)) ≤ δ)
    (htraces : P.trace.re + N.trace.re ≤ η)
    (henergy : (A * K).trace.re ≤ E) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        (η + 2 * Fintype.card (s × b) * εb) + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  obtain ⟨P₀, N₀, hP₀, hN₀, hsub, htrace₀⟩ :=
    exists_posSemidef_pair_same_sub_of_neg_le_minEigenvalue
      hP hN hPmin hNmin
  have hresidual₀ : rectangularTraceNorm
      ((compressedBoundaryLM Z A - X) - (P₀ - N₀)) ≤ δ := by
    rwa [hsub]
  have htraces₀ : P₀.trace.re + N₀.trace.re ≤
      η + 2 * Fintype.card (s × b) * εb := by
    rw [htrace₀]
    linarith
  exact exists_density_of_fully_approx_sdp_certificate
    Z hZ K X hA hP₀ hN₀ htrace hε hmin hresidual₀ htraces₀ henergy

/-- Every fully approximate feasible certificate repairs to an exact density with the
explicit trace-norm, boundary, and objective losses. -/
theorem IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy.exists_density
    {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
    [DecidableEq s] [DecidableEq b] [Nonempty (s × b)]
    {n : ℕ} [Nonempty (Fin n)]
    {Z : Matrix ((a × s) × b) (Fin n) ℂ} (hZ : Zᴴ * Z = 1)
    {K : Matrix (Fin n) (Fin n) ℂ} {X : Matrix (s × b) (s × b) ℂ}
    {η E κ ε εb δ : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    {P N : Matrix (s × b) (s × b) ℂ}
    (h : IsAllSpectralApproxCompressedBoundarySDPFeasibleAtEnergy
      Z K X η E κ ε εb δ A P N) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℂ,
      A₀.PosSemidef ∧ A₀.trace = 1 ∧
      rectangularTraceNorm (A₀ - A) ≤ κ + 2 * n * ε ∧
      rectangularTraceNorm (compressedBoundaryLM Z A₀ - X) ≤
        (η + 2 * Fintype.card (s × b) * εb) + δ + (κ + 2 * n * ε) ∧
      (A₀ * K).trace.re ≤ E + ‖K‖ * (κ + 2 * n * ε) := by
  rcases h with ⟨hA, hP, hN, htrace, hε, hmin, _hεb, hPmin, hNmin,
    hresidual, htraces, henergy⟩
  exact exists_density_of_all_spectral_approx_sdp_certificate
    Z hZ K X hA hP hN htrace hε hmin hPmin hNmin hresidual htraces henergy

/-- Equal independent precision targets for the four scalar losses in the fully
approximate semidefinite certificate fit inside the unused LVV margin.  Here `n` is
the compressed density dimension and `r` is the boundary-matrix dimension. -/
theorem fullyApproxSDP_errors_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden).1 hκ
  have hε' := (le_div_iff₀ hden).1 hε
  have hεb' := (le_div_iff₀ hden).1 hεb
  have hδ' := (le_div_iff₀ hden).1 hδ
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2028)).2
  nlinarith only [hκ', hε', hεb', hδ']

/-- The same independent precision target also absorbs rational approximation of the
coordinate isometry.  The fifth loss `ω` is added only to the boundary-equation error,
while physical expansion continues to use the exact isometry. -/
theorem fullyApproxSDP_errors_with_coordinate_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ ω : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδω : δ + ω ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * (((2 * r * εb + δ) + ω) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  simpa only [add_assoc] using
    fullyApproxSDP_errors_fit_lvv_margin hL hκ hε hεb hδω

/-- Splitting the former boundary-equation precision target equally between solver
residual and coordinate-map approximation gives explicit independent targets for all
five losses. -/
theorem fullyApproxSDP_errors_with_coordinate_fit_lvv_margin_of_split
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ ω : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : 2 * n * ε ≤ Δ / (64896 * L))
    (hεb : 2 * r * εb ≤ Δ / (64896 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (hω : ω ≤ Δ / (129792 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * (((2 * r * εb + δ) + ω) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  apply fullyApproxSDP_errors_with_coordinate_fit_lvv_margin hL hκ hε hεb
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden : (129792 : ℝ) * L ≠ 0 := (mul_pos (by norm_num) hLreal).ne'
  calc
    δ + ω ≤ Δ / (129792 * L) + Δ / (129792 * L) := add_le_add hδ hω
    _ = Δ / (64896 * L) := by field_simp; ring

/-- Independent precision targets that also absorb rational approximation of the
objective matrix and boundary-net center.  The four original spectral and residual
losses use one half of the LVV margin.  The other half is divided between the
objective error `eK`, which enters the energy directly, and the two boundary errors
`eX` and `ω`, which enter after multiplication by the Hamiltonian norm bound. -/
theorem fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eK eX ω : ℝ}
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (heK : eK ≤ Δ / 16224)
    (heX : eX ≤ Δ / (64896 * L))
    (hω : ω ≤ Δ / (64896 * L)) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((((2 * r * εb + δ) + eX) + ω) + (κ + 2 * n * ε))) ≤
        Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden₁ : 0 < (129792 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hden₂ : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden₁).1 hκ
  have hε' := (le_div_iff₀ hden₁).1 hε
  have hεb' := (le_div_iff₀ hden₁).1 hεb
  have hδ' := (le_div_iff₀ hden₁).1 hδ
  have heK' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16224)).1 heK
  have heX' := (le_div_iff₀ hden₂).1 heX
  have hω' := (le_div_iff₀ hden₂).1 hω
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2028)).2
  nlinarith only [hκ', hε', hεb', hδ', heK', heX', hω']

/-- Independent bounds for a numerical certificate with both energy-threshold slack and
auxiliary-trace slack.  The residual and trace slack split one boundary-error share. -/
theorem fullyApproxSDP_errors_with_trace_energy_slack_fit_lvv_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hΔ : 0 ≤ Δ)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hδ' : eη + δ ≤ Δ / (129792 * L) := by
    have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
    have hden : (259584 : ℝ) * L ≠ 0 := (mul_pos (by norm_num) hLreal).ne'
    calc
      eη + δ ≤ Δ / (259584 * L) + Δ / (259584 * L) := add_le_add heη hδ
      _ = Δ / (129792 * L) := by field_simp; ring
  have hfit := fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin hL hκ hε hεb
    hδ' heK (by positivity) (by positivity)
  convert hfit using 1
  all_goals ring

/-- The canonical trace-, spectral-, boundary-, and energy-slack thresholds in fact use
only three quarters of the final LVV margin.  The remaining quarter is available for
rationalizing the selected physical columns. -/
theorem fullyApproxSDP_errors_with_trace_energy_slack_fit_rationalization_margin
    {L n r : ℕ} (hL : 0 < L) {Δ κ ε εb δ eη eK : ℝ}
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (259584 * L))
    (heη : eη ≤ Δ / (259584 * L))
    (heK : eK ≤ Δ / 16224) :
    2 * ((4 * L * (κ + 2 * n * ε) + eK) +
      2 * L * ((eη + 2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2704 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hden₁ : 0 < (129792 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hden₂ : 0 < (259584 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hκ' := (le_div_iff₀ hden₁).1 hκ
  have hε' := (le_div_iff₀ hden₁).1 hε
  have hεb' := (le_div_iff₀ hden₁).1 hεb
  have hδ' := (le_div_iff₀ hden₂).1 hδ
  have heη' := (le_div_iff₀ hden₂).1 heη
  have heK' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16224)).1 heK
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2704)).2
  nlinarith only [hκ', hε', hεb', hδ', heη', heK']

/-- Entrywise mesh target for rational approximation of the compressed objective.
The added `1` makes the target meaningful without a separate nonvanishing assumption
on the matrix order or candidate entry bound. -/
noncomputable def rationalObjectiveApproximationTarget (n : ℕ) (C Δ : ℝ) : ℝ :=
  Δ / (16224 * ((n : ℝ) ^ 2 * C + 1))

/-- Entrywise mesh target for rational approximation of the boundary-net center.  Its
dependence on `L` reflects the Hamiltonian norm factor in the LVV energy estimate. -/
noncomputable def rationalBoundaryCenterApproximationTarget (L r : ℕ) (Δ : ℝ) : ℝ :=
  Δ / (64896 * L * ((r : ℝ) ^ 2 + 1))

theorem rationalObjectiveApproximationTarget_pos
    {n : ℕ} {C Δ : ℝ} (hC : 0 ≤ C) (hΔ : 0 < Δ) :
    0 < rationalObjectiveApproximationTarget n C Δ := by
  unfold rationalObjectiveApproximationTarget
  positivity

theorem rationalBoundaryCenterApproximationTarget_pos
    {L r : ℕ} (hL : 0 < L) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < rationalBoundaryCenterApproximationTarget L r Δ := by
  unfold rationalBoundaryCenterApproximationTarget
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  positivity

/-- The objective mesh target makes the energy loss fit its allocated part of the LVV
margin. -/
theorem objective_approximation_error_le_lvv_target
    {n : ℕ} {C Δ θ : ℝ} (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hmesh : θ ≤ rationalObjectiveApproximationTarget n C Δ) :
    (n : ℝ) ^ 2 * C * θ ≤ Δ / 16224 := by
  have hfactor : 0 ≤ (n : ℝ) ^ 2 * C := mul_nonneg (sq_nonneg _) hC
  calc
    (n : ℝ) ^ 2 * C * θ ≤
        (n : ℝ) ^ 2 * C * rationalObjectiveApproximationTarget n C Δ :=
      mul_le_mul_of_nonneg_left hmesh hfactor
    _ ≤ Δ / 16224 := by
      unfold rationalObjectiveApproximationTarget
      have hden : 0 < 16224 * ((n : ℝ) ^ 2 * C + 1) := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      field_simp
      nlinarith

/-- The boundary-center mesh target makes its trace-norm loss fit its allocated part
of the LVV margin. -/
theorem boundaryCenter_approximation_error_le_lvv_target
    {L r : ℕ} (hL : 0 < L) {Δ θ : ℝ} (hΔ : 0 ≤ Δ)
    (hmesh : θ ≤ rationalBoundaryCenterApproximationTarget L r Δ) :
    (r : ℝ) ^ 2 * θ ≤ Δ / (64896 * L) := by
  have hr : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
  calc
    (r : ℝ) ^ 2 * θ ≤
        (r : ℝ) ^ 2 * rationalBoundaryCenterApproximationTarget L r Δ :=
      mul_le_mul_of_nonneg_left hmesh hr
    _ ≤ Δ / (64896 * L) := by
      unfold rationalBoundaryCenterApproximationTarget
      have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
      have hden : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
      have hplus : 0 < (r : ℝ) ^ 2 + 1 := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (mul_pos hden hplus)).2
      field_simp
      nlinarith [mul_nonneg hΔ hr]

/-- The canonical objective and boundary-center meshes, together with the allocated
spectral, residual, and coordinate tolerances, imply the complete LVV margin bound. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_fixed_data_meshes
    {L n r : ℕ} (hL : 0 < L) {Δ C κ ε εb δ θK θX ω : ℝ}
    (hΔ : 0 ≤ Δ) (hC : 0 ≤ C)
    (hκ : κ ≤ Δ / (129792 * L))
    (hε : 2 * n * ε ≤ Δ / (129792 * L))
    (hεb : 2 * r * εb ≤ Δ / (129792 * L))
    (hδ : δ ≤ Δ / (129792 * L))
    (hθK : θK ≤ rationalObjectiveApproximationTarget n C Δ)
    (hθX : θX ≤ rationalBoundaryCenterApproximationTarget L r Δ)
    (hω : ω ≤ Δ / (64896 * L)) :
    2 * ((4 * L * (κ + 2 * n * ε) + (n : ℝ) ^ 2 * C * θK) +
      2 * L * ((((2 * r * εb + δ) + (r : ℝ) ^ 2 * θX) + ω) +
        (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  apply fullyApproxSDP_errors_with_fixed_data_fit_lvv_margin hL hκ hε hεb hδ
  · exact objective_approximation_error_le_lvv_target hC hΔ hθK
  · exact boundaryCenter_approximation_error_le_lvv_target hL hΔ hθX
  · exact hω

/-- Explicit tolerances on the two spectral errors imply the four independent loss
bounds used in `fullyApproxSDP_errors_fit_lvv_margin`.  The required inverse tolerances
are linear in the matrix orders `n`, `r` and in the chain length `L` (and inverse-linear
in the gap `Δ`).  This quantifies the numerical precision required by the finite LVV
semidefinite program without selecting a particular numerical solver. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_tolerances
    {L n r : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    {Δ κ ε εb δ : ℝ}
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * n))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * r))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hdenL : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hdenN : 0 < (129792 : ℝ) * L * n :=
    mul_pos (mul_pos (by norm_num) hLreal) hnreal
  have hdenR : 0 < (129792 : ℝ) * L * r :=
    mul_pos (mul_pos (by norm_num) hLreal) hrreal
  have hε' : 2 * n * ε ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεmul := (le_div_iff₀ hdenN).1 hε
    nlinarith only [hεmul]
  have hεb' : 2 * r * εb ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεbmul := (le_div_iff₀ hdenR).1 hεb
    nlinarith only [hεbmul]
  exact fullyApproxSDP_errors_fit_lvv_margin hL hκ hε' hεb' hδ

/-- Tolerances chosen from upper bounds on the two cone orders imply the corresponding
realized spectral-error bounds. -/
theorem fullyApproxSDP_scaled_errors_of_order_bounds
    {L n r nMax rMax : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hnMax : n ≤ nMax) (hrMax : r ≤ rMax)
    {Δ ε εb : ℝ} (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * nMax))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * rMax)) :
    2 * n * ε ≤ Δ / (64896 * L) ∧
      2 * r * εb ≤ Δ / (64896 * L) := by
  have hnMaxpos : 0 < nMax := hn.trans_le hnMax
  have hrMaxpos : 0 < rMax := hr.trans_le hrMax
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnMaxreal : 0 < (nMax : ℝ) := by exact_mod_cast hnMaxpos
  have hrMaxreal : 0 < (rMax : ℝ) := by exact_mod_cast hrMaxpos
  have hdenL : 0 < (64896 : ℝ) * L := mul_pos (by norm_num) hLreal
  have hdenN : 0 < (129792 : ℝ) * L * nMax :=
    mul_pos (mul_pos (by norm_num) hLreal) hnMaxreal
  have hdenR : 0 < (129792 : ℝ) * L * rMax :=
    mul_pos (mul_pos (by norm_num) hLreal) hrMaxreal
  have hεMax : 2 * nMax * ε ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεmul := (le_div_iff₀ hdenN).1 hε
    nlinarith only [hεmul]
  have hεbMax : 2 * rMax * εb ≤ Δ / (64896 * L) := by
    apply (le_div_iff₀ hdenL).2
    have hεbmul := (le_div_iff₀ hdenR).1 hεb
    nlinarith only [hεbmul]
  have hε' : 2 * n * ε ≤ Δ / (64896 * L) := by
    refine le_trans ?_ hεMax
    gcongr
  have hεb' : 2 * r * εb ≤ Δ / (64896 * L) := by
    refine le_trans ?_ hεbMax
    gcongr
  exact ⟨hε', hεb'⟩

/-- A priori upper bounds for the two matrix orders give uniform solver tolerances.
Consequently the numerical precision can be fixed before the support coordinates and
the actual boundary order are constructed. -/
theorem fullyApproxSDP_errors_fit_lvv_margin_of_order_bounds
    {L n r nMax rMax : ℕ} (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hnMax : n ≤ nMax) (hrMax : r ≤ rMax)
    {Δ κ ε εb δ : ℝ} (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * nMax))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * rMax))
    (hδ : δ ≤ Δ / (64896 * L)) :
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  obtain ⟨hε', hεb'⟩ := fullyApproxSDP_scaled_errors_of_order_bounds
    hL hn hr hnMax hrMax hεnonneg hεbnonneg hε hεb
  exact fullyApproxSDP_errors_fit_lvv_margin hL hκ hε' hεb' hδ

/-- Chain specialization of the uniform tolerance theorem.  The density tolerance is
chosen from the retained-support bound `|S| m`, and the auxiliary-matrix tolerance from
the boundary bound `q m`; neither depends on the subsequently constructed coordinate
isometry. -/
theorem chain_fullyApproxSDP_errors_fit_lvv_margin_of_support_bounds
    {L q k m n : ℕ} (S : Finset (LeftBlockVector L q k))
    (hL : 0 < L) (hq : 1 ≤ q) (hnpos : 0 < n)
    (hrpos : 0 < Fintype.card (CutSite L q k × Fin m))
    (hn : n ≤ S.card * m) {Δ κ ε εb δ : ℝ}
    (hεnonneg : 0 ≤ ε) (hεbnonneg : 0 ≤ εb)
    (hκ : κ ≤ Δ / (64896 * L))
    (hε : ε ≤ Δ / ((129792 : ℝ) * L * (S.card * m)))
    (hεb : εb ≤ Δ / ((129792 : ℝ) * L * (q * m)))
    (hδ : δ ≤ Δ / (64896 * L)) :
    let r := Fintype.card (CutSite L q k × Fin m)
    2 * (4 * L * (κ + 2 * n * ε) +
      2 * L * ((2 * r * εb + δ) + (κ + 2 * n * ε))) ≤ Δ / 2028 := by
  classical
  intro r
  have hr : r ≤ q * m := by
    simpa only [r, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul (card_cutSite_le (L := L) (k := k) hq) (Nat.le_refl m)
  apply fullyApproxSDP_errors_fit_lvv_margin_of_order_bounds
    hL hnpos hrpos hn hr hεnonneg hεbnonneg hκ
  · simpa only [Nat.cast_mul] using hε
  · simpa only [Nat.cast_mul] using hεb
  · exact hδ

end TNLean.MPS.AreaLaw
