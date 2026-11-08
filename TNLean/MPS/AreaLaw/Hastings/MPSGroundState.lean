/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.AreaLaw
import TNLean.MPS.AreaLaw.Hastings.MPSFromEntropy
import TNLean.MPS.AreaLaw.Hastings.LiebRobinson
import TNLean.MPS.AreaLaw.MPSApproximation

/-!
# Matrix product state approximation of a gapped ground state

Let `Ω` be a gapped ground vector on a chain of `L` sites. Approximate
factorization with constants `ξ' > 0` and `C₁ ≥ 1`, together with an
entropy bound `Smax` at every cut, gives a matrix product state `Φ` of
bond dimension at most `k'` for every `k' ≥ k₀ = ceil(exp(2 Smax)/2)`.
The squared error is at most
`(L-1) * 4 C₁² exp(2/ξ') * (k'/k₀)^(-1/(ξ' log q))`.
Hastings, arXiv:0705.2024v4, lines 505–557, uses the entropy bound from
lines 130–144 to choose the common threshold.

This module supplies both hypotheses from the Hamiltonian assumptions,
using `Smax = areaLawBound ξ' C₁ q`. For `q = 1`, truncation is exact.

**Scope restriction (auxiliary parameters):** the endpoints below use
`lemmaOneLength R (J/ΔE) 1` or `ζ = lemmaOneEndpointLength R J ΔE`.
The corresponding physical Lieb–Robinson velocities include a term
proportional to the gap, rather than being expressed as a fixed multiple of `J`. Moreover,
the auxiliary entropy bound at these lengths has the corrected doubled
exponent. The common order-`J` source-parameter conclusion, with the
printed entropy maximum in `k₀`, is proved in
`Hastings/SourceConsequences.lean`. The auxiliary bounds remain valid.
See `docs/paper-gaps/hastings07_lemma1_decay_length.tex`,
`docs/paper-gaps/hastings07_doubling_constants.tex`, and
`docs/paper-gaps/hastings07_mps_entropy_stage.tex`.

**Local fix (error and constant):** the error is the squared norm of an
unnormalized truncation, and `exp(2/ξ')` replaces the printed `exp(1/ξ')`
because the constraint is available only at even exponents. See
`docs/paper-gaps/hastings07_mps_error_measure.tex` and
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Matrix Real
open TNLean.Lattice

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q R : ℕ} {J : ℝ}

/-- **Matrix product state approximation of the gapped ground state, from Lemma 1 (stage
theorem).** Let `Ω` be a gapped ground vector of a finite-range Hamiltonian `h` on the chain
of `L` sites with local dimension `q ≥ 1`, around which Lemma 1 holds with constants `ξ' > 0`
and `C₁ ≥ 1`. With `k₀ = ⌈exp(2 S_max)/2⌉` for the area-law bound
`S_max = areaLawBound ξ' C₁ q`, for every `k' ≥ k₀` the truncation `Φ` onto the `k'` leading
eigenvectors at every cut is an open-boundary matrix product state of bond dimension at most
`k'` with
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constants of the module docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_gappedGroundState [NeZero q] (h : ChainHamiltonian L q R J)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ)
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
  refine isOpenMPS_norm_sub_sq_le_of_isFactorizationAt_of_entropy hgs.1 hξ'
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
sites with local dimension `q ≥ 1` and every gapped ground vector `Ω` of a chain Hamiltonian
of range `R` and term norm `J` with gap `ΔE`, with `k₀ = ⌈exp(2 S_max)/2⌉` for
`S_max = areaLawBound ξ' C₁ q`, the truncation `Φ` onto the `k'` leading eigenvectors at every
cut, for every `k' ≥ k₀`, is an open-boundary matrix product state of bond dimension at most
`k'` with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`. The constants depend
only on `R`, `κ`, `J/ΔE` and `q`, not on `L`. Hastings, arXiv:0705.2024v4, lines 505–557, with
`C₁` polynomial in `ξ̂` as at lines 258–262 and the restrictions of the module docstring. -/
theorem exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState (R : ℕ) {κ : ℝ} (hκ : 6 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
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
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} _ h {E₀} {Ω} hgs {k'} hk' ↦ ?_⟩
  have hξ'0 : 0 < κ * lemmaOneLength R (J / ΔE) 1 :=
    mul_pos (by linarith) (lemmaOneLength_pos R _ 1)
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hgs hξ'0 (le_max_right _ _)
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
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
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
  refine ⟨K, hK0, fun {J ΔE} hJ hΔ {L q} _ h {E₀} {Ω} hgs {k'} hk' ↦ ?_⟩
  have hζ0 : 0 < 6 * lemmaOneEndpointLength R J ΔE := by
    rw [lemmaOneEndpointLength_eq]; linarith [lemmaOneLength_pos R (J / ΔE) 1]
  refine isOpenMPS_norm_sub_sq_le_of_gappedGroundState h hgs hζ0 (le_max_right _ _)
    (fun c l _ ↦ ?_) hk'
  obtain ⟨OB, OL, OR, hf⟩ := hF hJ hΔ h hgs c l
  exact ⟨OB, OL, OR, hf.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw.Hastings
