/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.AreaLaw
import TNLean.MPS.AreaLaw.Hastings.MPSFromEntropy
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant
import TNLean.MPS.AreaLaw.MPSApproximation

/-!
# Matrix product state approximation of the gapped ground state from Lemma 1

Let `Ω` be a gapped ground vector of a finite-range Hamiltonian on the chain of `L` sites with
local dimension `q > 1`, and suppose Lemma 1 holds around `Ω` with constants `ξ' > 0` and
`C₁ ≥ 1`. The area law bounds the entropy of every initial segment by `S_max`. With
`k₀ = ⌈exp(2 S_max)/2⌉`, truncating every cut onto the `k'` leading eigenvectors of its left
marginal, for `k' ≥ k₀`, gives an open-boundary matrix product state `Φ` of bond dimension at
most `k'` with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 505–557, with `S_max` from eq. `entbd` (lines 130–137).
This discharges the per-cut entropy hypothesis of
`isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy`, recorded in
`docs/paper-gaps/hastings07_mps_entropy_stage.tex`.

`isOpenMPS_norm_sub_sq_le_of_gappedGroundState` takes Lemma 1 as a hypothesis, as
`regionEntropy_prefix_le_of_factorization` does.
`exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState` supplies it from Lemma 1 with a
polynomial constant (`exists_projectorFactorization_pow`), so it takes only the hypotheses of
Hastings' theorem: finite range, bounded interaction strength and a spectral gap. In units of
the gap, with `ξ̂ = lemmaOneLength R (J/ΔE) 1` and a fixed `κ > 6`, Lemma 1 holds at the rate
`ξ' = κ ξ̂` with constant `K ξ̂³`, where `K` depends only on `R` and `κ`; the constant is
replaced by `C₁ = max (K ξ̂³) 1`, which only weakens Lemma 1.

**Scope restriction (quantitative bounds of Lemma 1):** the theorems inherit the restriction of
Lemma 1 with a polynomial constant. At the length `ξ̂`, the bound holds at the rate `ξ' = κ ξ̂`
for every fixed `κ > 6`, with `K` depending on `κ`, and the printed endpoint `ξ' = 6ξ` is not
reached there. It is reached for the inflated length `ζ = lemmaOneEndpointLength R J ΔE =
(5/4) ξ̂`, at `ξ' = 6ζ` (`exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState_endpoint`).
The length `ζ` may stand in for the source's `ξ`: the source fixes `ξ = max(2v/ΔE, ξ_C)` only
through some Lieb–Robinson pair, and a bound valid for `|t| ≤ l/v` stays valid for a larger
velocity (lines 96–112), so raising the chain velocity by `5/4` is a legitimate choice.
Both lengths come from the chain Lieb–Robinson estimate, whose prefactor grows with `J` and
whose second operator acts on one site, so neither is shown to be the source's
`max(2v/ΔE, ξ_C)` for a pair satisfying eq. `lrb` (lines 96–112, 139–142). The bond dimension
`k₀ = ⌈exp(2 S_max)/2⌉` inherits this through the area-law bound `S_max`. Documented in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

The error is the squared norm, documented in
`docs/paper-gaps/hastings07_mps_error_measure.tex`. The value of `S_max` carries the local fix
of `TNLean.MPS.AreaLaw.Hastings.areaLawBound`.

**Local fix (constant):** the constant `e^{2/ξ'}` replaces the printed `e^{1/ξ'}`, because the
constraint is available only at even exponents. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Matrix Real
open TNLean.Lattice

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q R : ℕ} {J : ℝ}

/-- **Matrix product state approximation of the gapped ground state, from Lemma 1 (stage
theorem).** Let `Ω` be a gapped ground vector of a finite-range Hamiltonian `h` on the chain
of `L` sites with local dimension `q > 1`, around which Lemma 1 holds with constants `ξ' > 0`
and `C₁ ≥ 1`. With `k₀ = ⌈exp(2 S_max)/2⌉` for the area-law bound
`S_max = areaLawBound ξ' C₁ q`, for every `k' ≥ k₀` the truncation `Φ` onto the `k'` leading
eigenvectors at every cut is an open-boundary matrix product state of bond dimension at most
`k'` with
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constants of the module docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_gappedGroundState (h : ChainHamiltonian L q R J)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (hq : 1 < q)
    {ξ' C₁ : ℝ} (hξ' : 0 < ξ') (hC₁ : 1 ≤ C₁)
    (hfact : ∀ c l : ℕ, c + l ≤ L → ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      IsFactorizationAt Ω c l (C₁ * Real.exp (-(l / ξ'))) OB OL OR)
    {k' : ℕ} (hk' : ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊ ≤ k') :
    let k₀ := ⌈Real.exp (2 * areaLawBound ξ' C₁ q) / 2⌉₊
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  intro k₀ P Φ
  refine isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy hq hgs.1 hξ'
    (fun j _ m hm ↦ hfact j m hm) (fun j _ ↦ ?_) hk'
  -- The area law bounds the entropy of every initial segment by `S_max`.
  have hS := regionEntropy_prefix_le_of_factorization h hgs hξ' hC₁ hfact j
  rw [← leftBlock_eq_interval] at hS
  calc Real.exp (2 * Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) / 2
      ≤ Real.exp (2 * areaLawBound ξ' C₁ q) / 2 := by gcongr
    _ ≤ k₀ := Nat.le_ceil _

/-- **Hastings' matrix product state approximation of the gapped ground state.** Let `R` be a
range and `κ > 6`. There is a constant `K ≥ 0`, depending only on `R` and `κ`, with the
following property. Let `J ≥ 0` bound the interaction terms, let `ΔE > 0` be a gap, and put
`ξ̂ = lemmaOneLength R (J/ΔE) 1`, `ξ' = κ ξ̂` and `C₁ = max (K ξ̂³) 1`. For every chain of `L`
sites with local dimension `q > 1` and every gapped ground vector `Ω` of a chain Hamiltonian
of range `R` and term norm `J` with gap `ΔE`, with `k₀ = ⌈exp(2 S_max)/2⌉` for
`S_max = areaLawBound ξ' C₁ q`, the truncation `Φ` onto the `k'` leading eigenvectors at every
cut, for every `k' ≥ k₀`, is an open-boundary matrix product state of bond dimension at most
`k'` with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`. The constants depend
only on `R`, `κ`, `J/ΔE` and `q`, not on `L`. Hastings, arXiv:0705.2024v4, lines 505–557, with
`C₁` polynomial in `ξ̂` as at lines 258–262 and the restrictions of the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState (R : ℕ) {κ : ℝ} (hκ : 6 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ}, 1 < q → ∀ (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ {k' : ℕ}, ⌈Real.exp (2 * areaLawBound (κ * lemmaOneLength R (J / ΔE) 1)
          (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) q) / 2⌉₊ ≤ k' →
        let k₀ := ⌈Real.exp (2 * areaLawBound (κ * lemmaOneLength R (J / ΔE) 1)
          (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) q) / 2⌉₊
        let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
          (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
            Ω).leadingEigenprojection k'
        let Φ := sequentialTruncation P (L - 1) Ω
        IsOpenMPS L q k' (fun x ↦ Φ x) ∧
          ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
            (4 * (max (K * lemmaOneLength R (J / ΔE) 1 ^ 3) 1) ^ 2 *
              exp (2 / (κ * lemmaOneLength R (J / ΔE) 1)) *
              ((k' : ℝ) / k₀) ^ (-1 / ((κ * lemmaOneLength R (J / ΔE) 1) * log q))) := by
  obtain ⟨K, hK0, hF⟩ := exists_projectorFactorization_pow R hκ
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} hq h {E₀} {Ω} hgs {k'} hk' ↦ ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hξ'0 : 0 < κ * lemmaOneLength R (J / ΔE) 1 :=
    mul_pos (by linarith) (lemmaOneLength_pos R _ 1)
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hgs hq hξ'0 (le_max_right _ _)
    (fun c l _ ↦ ?_) hk'
  obtain ⟨OB, OL, OR, hf⟩ := hF hJ hΔ h hgs c l
  exact ⟨OB, OL, OR, hf.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

/-- **Hastings' matrix product state approximation at the printed rate `ξ' = 6ξ`.** There is a
constant `K ≥ 0`, depending only on `R`, with the following property. Let `J ≥ 0` bound the
interaction terms, let `ΔE > 0` be a gap, and put `ζ = lemmaOneEndpointLength R J ΔE =
(5/4) ξ̂`, `ξ' = 6ζ` and `C₁ = max (K ζ³) 1`. Then the conclusion of
`exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState` holds with these `ξ'` and `C₁`.
Hastings, arXiv:0705.2024v4, lines 505–557, with `ξ' = 6ξ` (lines 141–142) for `ξ = ζ`, `C₁`
polynomial in `ζ` (lines 258–262), and the restriction on `ζ` of the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState_endpoint (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ}, 1 < q → ∀ (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ {k' : ℕ}, ⌈Real.exp (2 * areaLawBound (6 * lemmaOneEndpointLength R J ΔE)
          (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) q) / 2⌉₊ ≤ k' →
        let k₀ := ⌈Real.exp (2 * areaLawBound (6 * lemmaOneEndpointLength R J ΔE)
          (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) q) / 2⌉₊
        let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
          (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
            Ω).leadingEigenprojection k'
        let Φ := sequentialTruncation P (L - 1) Ω
        IsOpenMPS L q k' (fun x ↦ Φ x) ∧
          ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
            (4 * (max (K * lemmaOneEndpointLength R J ΔE ^ 3) 1) ^ 2 *
              exp (2 / (6 * lemmaOneEndpointLength R J ΔE)) *
              ((k' : ℝ) / k₀) ^ (-1 / ((6 * lemmaOneEndpointLength R J ΔE) * log q))) := by
  obtain ⟨K, hK0, hF⟩ := exists_projectorFactorization_endpoint R
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} hq h {E₀} {Ω} hgs {k'} hk' ↦ ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hζ0 : 0 < 6 * lemmaOneEndpointLength R J ΔE := by
    rw [lemmaOneEndpointLength_eq]; linarith [lemmaOneLength_pos R (J / ΔE) 1]
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hgs hq hζ0 (le_max_right _ _)
    (fun c l _ ↦ ?_) hk'
  obtain ⟨OB, OL, OR, hf⟩ := hF hJ hΔ h hgs c l
  exact ⟨OB, OL, OR, hf.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw.Hastings
