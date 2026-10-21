/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.LocalizationParameters
import TNLean.PEPS.Approximation.SwappedLocalHamiltonian
import TNLean.Lattice.RegionalReset

/-!
# The supported unitary of the information reset at interaction range `R`

Let `Ω` be a gapped ground state of a Hamiltonian of interaction range `R` and term bound `J` on
a finite domain `Λ` with at most `L²` sites, and let `A, C` be disjoint sets of sites with
`I_Ω(A : C) ≤ b`. On two replicas put `Ψ = Ω ⊗ Ω` and `Φ = F_A Ψ`, where `F_A` exchanges the
replicas on `A`. With `B = 1 + b + log L`, this module constructs a unitary `U` on the doubled
system acting on the graph neighbourhood of radius `⌈K B⌉` of the buffer `(A ∪ C)ᶜ` and of the
sites of the supports crossing `A`, with `‖U Ψ - Φ‖ ≤ C L^(-r)`.

The constants are named and depend only on `R, J, Δ, r`:

* `rangeResetRadius R J Δ r = (v T₀ + 15 + r) / (1/2)`, with the graph-ball velocity
  `v = v(R, 2J)` of the doubled Hamiltonian and the cutoff `T₀ = resetCutoff Δ r`;
* `rangeResetFilterPrefactor R J Δ r = 2 C₀(R) (1 + 4 μ_R J) (1 + T₀) + 3`;
* `rangeResetUnitaryPrefactor R J Δ r = 2 rangeResetFilterPrefactor R J Δ r`.

The polynomial-PEPS manuscript treats only site and nearest-neighbour terms on the open square,
which is range one; the statements here extend its reset to range `R`. The range-one
statements on the open square, `SquareHamiltonian.reset_localized_filter` and
`SquareHamiltonian.reset_unitary` with `resetRadius` and `resetUnitaryPrefactor`, are
unchanged.

## Main statements

* `TNLean.Lattice.LocalHamiltonian.reset_localized_filter`: the localized two-sided filter of
  `eq:info-local-two-sided` at range `R`.
* `TNLean.Lattice.LocalHamiltonian.reset_unitary`: the unitary of `eq:info-reset-unitary` at
  range `R`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`,
  lines 355–599, equations `eq:info-local-two-sided`, `eq:info-reset-polar-errors` and
  `eq:info-reset-unitary`, with `K_loc` at lines 551–554.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.Approximation

open TNLean.Lattice

/-! ### The constants of the information reset at range `R` -/

/-- The localization radius coefficient `K = (v T₀ + 15 + r) / μ` of the information reset at
range `R`, with the graph-ball velocity `v = v(R, 2J)` of the doubled Hamiltonian, the decay
rate `μ = 1/2` and the cutoff `T₀ = resetCutoff Δ r`. The range-one coefficient on the open
square is `resetRadius J Δ r`.
Source: `K_loc` of `02-information.tex`, lines 551–554, at range `R`. -/
def rangeResetRadius (R : ℕ) (J Δ r : ℝ) : ℝ :=
  (AreaLaw.graphBallLocalizationVelocity R (2 * J) * resetCutoff Δ r + 15 + r) / (1 / 2)

/-- The prefactor `2 C₀(R) (1 + 4 μ_R J) (1 + T₀) + 3` of the two residuals of the localized
filter of the information reset at range `R`. The summand `3` bounds the Gaussian and
truncation errors, the rest the localization error.
Source: `02-information.tex`, lines 551–562, equation `eq:info-local-two-sided`, at range `R`. -/
def rangeResetFilterPrefactor (R : ℕ) (J Δ r : ℝ) : ℝ :=
  2 * AreaLaw.graphBallLocalizationPrefactor R * (1 + swapBoundaryCoefficient R * J) *
    (1 + resetCutoff Δ r) + 3

/-- The prefactor `2 C` of the error `‖U Ψ - Φ‖ ≤ 2 C L^(-r)` of the unitary of the information
reset at range `R`, with `C = rangeResetFilterPrefactor R J Δ r`.
Source: `02-information.tex`, lines 563–599, at range `R`. -/
def rangeResetUnitaryPrefactor (R : ℕ) (J Δ r : ℝ) : ℝ := 2 * rangeResetFilterPrefactor R J Δ r

theorem rangeResetRadius_pos (R : ℕ) {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < rangeResetRadius R J Δ r := by
  have := AreaLaw.graphBallLocalizationVelocity_nonneg R (by linarith : (0 : ℝ) ≤ 2 * J)
  have := resetCutoff_pos hΔ hr
  unfold rangeResetRadius; positivity

theorem rangeResetFilterPrefactor_pos (R : ℕ) {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hr : 0 ≤ r) : 0 < rangeResetFilterPrefactor R J Δ r := by
  have := AreaLaw.graphBallLocalizationPrefactor_pos R
  have := resetCutoff_pos hΔ hr
  have := swapBoundaryCoefficient_nonneg R
  unfold rangeResetFilterPrefactor; positivity

theorem rangeResetUnitaryPrefactor_pos (R : ℕ) {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hr : 0 ≤ r) : 0 < rangeResetUnitaryPrefactor R J Δ r :=
  mul_pos two_pos (rangeResetFilterPrefactor_pos R hJ hΔ hr)

end TNLean.PEPS.Approximation

namespace TNLean.Lattice.LocalHamiltonian

open TNLean.PEPS.Approximation

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **The localized two-sided filter of the information reset at range `R`, with explicit
constants.** Let `Ω` be a gapped ground state of a Hamiltonian `h` of range `R` and term bound
`J ≥ 0` on a finite domain with at most `L²` sites, and let `A, C` be disjoint with
`I_Ω(A : C) ≤ b`. With `B = 1 + b + log L`, put `Ψ = Ω ⊗ Ω` and `Φ = F_A Ψ` on paired sites.
Then there are a real `z ≥ exp (-2 b)` and a contraction `M` acting on the graph neighbourhood
of radius `⌈K B⌉` of the buffer `(A ∪ C)ᶜ` and of the sites of the supports crossing `A`, with
`‖M Ψ - z Φ‖` and `‖Mᴴ Φ - z Ψ‖` at most `C exp (-10 b) L^(-r)`, for
`K = rangeResetRadius R J Δ r` and `C = rangeResetFilterPrefactor R J Δ r`.

The manuscript treats range one only; this extends its estimate to range `R`.
Source: `02-information.tex`, lines 355–562, with `K_loc` at lines 551–554. -/
theorem reset_localized_filter (hq : 1 ≤ q) (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ)
    (hr : 0 ≤ r) {L : ℕ} (hL : 1 ≤ L) (hΛ : Λ.card ≤ L ^ 2) (h : LocalHamiltonian Λ q R J)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    (A C : Finset (Site Λ)) (hAC : Disjoint A C) (b : ℝ) (hb : 0 ≤ b)
    (hI : FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A C ≤ b) :
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let F := reindex p p (sheetSwapOp q A)
    let ψ : Configuration Λ (q * q) → ℂ := fun c ↦ Ω (p.symm c).1 * Ω (p.symm c).2
    let B := graphNeighborhood Λ ⌈rangeResetRadius R J Δ r * (1 + b + Real.log L)⌉₊
      ((A ∪ C)ᶜ ∪ crossingSites Λ R A)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
    ∃ (z : ℝ) (M : Matrix (Configuration Λ (q * q)) (Configuration Λ (q * q)) ℂ),
      Real.exp (-2 * b) ≤ z ∧
      M ∈ supportedOperators (q * q) (B : Set (Site Λ)) ∧ ‖M‖ ≤ 1 ∧
      ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
        rangeResetFilterPrefactor R J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
      ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
        rangeResetFilterPrefactor R J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
  intro p F ψ B
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set Cg := 2 * PEPS.AreaLaw.graphBallLocalizationPrefactor R with hCgdef
  set v := PEPS.AreaLaw.graphBallLocalizationVelocity R (2 * J) with hvdef
  set T₀ := resetCutoff Δ r with hT₀def
  set K := rangeResetRadius R J Δ r with hKdef
  set c := swapBoundaryCoefficient R with hcdef
  have hcoef : v * T₀ + 15 + r ≤ 1 / 2 * K := by
    rw [hKdef, rangeResetRadius]; apply le_of_eq; ring
  have hCg : 0 < Cg := mul_pos two_pos (PEPS.AreaLaw.graphBallLocalizationPrefactor_pos R)
  have hT₀ : 0 < T₀ := resetCutoff_pos hΔ hr
  have hc : 0 ≤ c := swapBoundaryCoefficient_nonneg R
  have hcJ : 0 ≤ c * J := mul_nonneg hc hJ
  obtain ⟨hψn, hφn, W, z, hW, hz, hfil⟩ :=
    regional_physicalBuffer_filter.{0, 0} hΔ hr q A C hAC p h.operator E₀ Ω b hgs hb hI
  obtain ⟨hT, hfwd, hrev⟩ := hfil L hL1
  obtain ⟨U, -, -, -, -, hM⟩ :=
    h.supported_buffer_gaussian_integral hq hJ A C hAC W ⌈K * (1 + b + Real.log L)⌉₊
  obtain ⟨hMsupp, hMnorm, hMerr⟩ := hM (Real.toNNReal (resetVariance Δ r * (1 + b + Real.log L)))
    (T₀ * (1 + b + Real.log L)) hT
  have hlocb := GaussianFilter.localization_error_bound_of_parameter_constant (L := (L : ℝ))
    (C := Cg * (1 + c * J)) hT₀.le (by norm_num : (0 : ℝ) ≤ 1 / 2) hr hcoef hb hL1
    (by positivity)
  have hT₀B : 0 ≤ 1 + b + Real.log L := by
    have := Real.log_nonneg hL1
    linarith
  have hcard : (Λ.card : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast hΛ
  have hδ : ‖W‖ * Cg * (Λ.card : ℝ) * (1 + c * J * (Λ.card : ℝ) * (T₀ * (1 + b + Real.log L))) *
      Real.exp (v * (T₀ * (1 + b + Real.log L)) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) ≤
      Cg * (1 + c * J) * (1 + T₀) * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
    refine le_trans ?_ hlocb
    set T' := T₀ * (1 + b + Real.log L)
    have hTB : 0 ≤ T' := mul_nonneg hT₀.le hT₀B
    have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    have hpoly : (Λ.card : ℝ) * (1 + c * J * (Λ.card : ℝ) * T') ≤
        (1 + c * J) * (L : ℝ) ^ 4 * (1 + T') := by
      have hn : (0 : ℝ) ≤ Λ.card := Nat.cast_nonneg _
      have hsq : (Λ.card : ℝ) * Λ.card ≤ (L : ℝ) ^ 4 := by
        rw [show (L : ℝ) ^ 4 = (L : ℝ) ^ 2 * (L : ℝ) ^ 2 by ring]
        exact mul_le_mul hcard hcard hn (by positivity)
      have h₁ : (Λ.card : ℝ) ≤ (L : ℝ) ^ 4 * (1 + T') := by
        have : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := by
          rw [show (L : ℝ) ^ 4 = (L : ℝ) ^ 2 * (L : ℝ) ^ 2 by ring]
          exact le_mul_of_one_le_right (by positivity) hL2
        exact hcard.trans (this.trans (le_mul_of_one_le_right (by positivity) (by linarith)))
      have h₂ : c * J * ((Λ.card : ℝ) * Λ.card) * T' ≤ c * J * (L : ℝ) ^ 4 * (1 + T') := by
        have := mul_le_mul_of_nonneg_left hsq hcJ
        nlinarith
      calc (Λ.card : ℝ) * (1 + c * J * (Λ.card : ℝ) * T')
          = (Λ.card : ℝ) + c * J * ((Λ.card : ℝ) * Λ.card) * T' := by ring
        _ ≤ (L : ℝ) ^ 4 * (1 + T') + c * J * (L : ℝ) ^ 4 * (1 + T') := add_le_add h₁ h₂
        _ = (1 + c * J) * (L : ℝ) ^ 4 * (1 + T') := by ring
    rw [show v * T' = v * T₀ * (1 + b + Real.log L) by ring]
    calc ‖W‖ * Cg * (Λ.card : ℝ) * (1 + c * J * (Λ.card : ℝ) * T') *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊)
        = ‖W‖ * Cg * ((Λ.card : ℝ) * (1 + c * J * (Λ.card : ℝ) * T')) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          ring
      _ ≤ 1 * Cg * ((1 + c * J) * (L : ℝ) ^ 4 * (1 + T')) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          gcongr
      _ = Cg * (1 + c * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          ring
  obtain ⟨h₁, h₂⟩ := norm_two_sided_le_of_norm_sub_le hψn hφn (hMerr.trans hδ) hfwd hrev
  refine ⟨hψn, hφn, z, _, hz, hMsupp, hMnorm.trans hW, h₁.trans_eq ?_, h₂.trans_eq ?_⟩ <;>
    rw [rangeResetFilterPrefactor, ← hCgdef, ← hT₀def, ← hcdef] <;> ring

/-- **The unitary of the information reset at range `R`, with explicit constants.** In the
setting of `reset_localized_filter`, there is a unitary `U` acting on the graph neighbourhood
of radius `⌈K B⌉` of the buffer `(A ∪ C)ᶜ` and of the sites of the supports crossing `A`, with
`‖U Ψ - Φ‖ ≤ C L^(-r)` for `K = rangeResetRadius R J Δ r` and
`C = rangeResetUnitaryPrefactor R J Δ r`. It is the polar factor of `M / z` on the same support.

The manuscript treats range one only; this extends its reset to range `R`.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem reset_unitary (hq : 1 ≤ q) (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r)
    {L : ℕ} (hL : 1 ≤ L) (hΛ : Λ.card ≤ L ^ 2) (h : LocalHamiltonian Λ q R J)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    (A C : Finset (Site Λ)) (hAC : Disjoint A C) (b : ℝ) (hb : 0 ≤ b)
    (hI : FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A C ≤ b) :
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let F := reindex p p (sheetSwapOp q A)
    let ψ : Configuration Λ (q * q) → ℂ := fun c ↦ Ω (p.symm c).1 * Ω (p.symm c).2
    let B := graphNeighborhood Λ ⌈rangeResetRadius R J Δ r * (1 + b + Real.log L)⌉₊
      ((A ∪ C)ᶜ ∪ crossingSites Λ R A)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
    ∃ U : Matrix (Configuration Λ (q * q)) (Configuration Λ (q * q)) ℂ,
      U ∈ unitaryGroup (Configuration Λ (q * q)) ℂ ∧
      U ∈ supportedOperators (q * q) (B : Set (Site Λ)) ∧
      ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
        rangeResetUnitaryPrefactor R J Δ r * (L : ℝ) ^ (-r) := by
  intro p F ψ B
  obtain ⟨hψn, hφn, z, M, hz, hMsupp, -, hfwd, hrev⟩ :=
    h.reset_localized_filter hq hJ hΔ hr hL hΛ E₀ Ω hgs A C hAC b hb hI
  obtain ⟨U, hU, hUsupp, hUerr⟩ := exists_supported_unitary_of_two_sided B hMsupp hb hz hfwd hrev
    (rangeResetFilterPrefactor_pos R hJ hΔ hr).le (by positivity)
  exact ⟨hψn, hφn, U, hU, hUsupp, hUerr.trans_eq (by rw [rangeResetUnitaryPrefactor])⟩

end TNLean.Lattice.LocalHamiltonian
