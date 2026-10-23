/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ChainBootstrap
import TNLean.MPS.AreaLaw.Hastings.ProjectorFactorization

/-!
# Hastings' bootstrap lemma from the approximate factorization

Lemma 2 of Hastings, *An area law for one-dimensional quantum systems* (arXiv:0705.2024v4,
`References/0705.2024/law16.tex`, lines 280–311), bounds the entropy `S_j` of the first `j`
sites of the ground state `Ψ₀` by `ln k + ξ' ln(2 C₁²/P) ln D + F(ξ', D)`, for every mixture
`ρ` of pure states of Schmidt rank at most `k` across the cut with overlap
`⟨Ψ₀, ρ Ψ₀⟩ = P > 0`. Its proof uses the Hamiltonian only through Lemma 1, the approximate
factorization `‖O_B O_L O_R − P₀‖ ≤ C₁ e^{-m/ξ'}` (eq. `prodapprox`, lines 246–267).

This file first states the bound with Lemma 1 in the form `IsFactorizationAt` in which it is
produced, at the cut `j` and every length `m`, and then discharges Lemma 1 by
`exists_projectorFactorization`. The result is Lemma 2 on Hastings' own hypotheses: a chain
Hamiltonian of finite range and finite interaction strength with a unique gapped ground state.
As in the source, the constant `C₁` is that of Lemma 1: it depends on the range, the
interaction strength, the gap and `ξ'`, and not on the length of the chain, the cut or the
mixture.

The source's sites carry nearest-neighbour terms (lines 85–93), which it obtains from any
finite range by grouping sites; here the range `R` is arbitrary.

**Local fix (decay length):** Lemma 1, and with it this bound, holds at every
`ξ' > 6ξ` with `ξ = 8 max(2v/ΔE, 1)` for the chain Lieb–Robinson velocity `v`, not at the
printed `ξ' = 6ξ` with `ξ = max(2v/ΔE, ξ_C)` (lines 139–142). Documented in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `entropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt`: the bootstrap bound from
  the factorization at the cut `j` and every length.
* `exists_entropy_le_of_overlap_schmidtRank_mixture`: Lemma 2.
-/

namespace TNLean.MPS.AreaLaw.Hastings

open TNLean.MPS.AreaLaw
open scoped InnerProductSpace

variable {L q : ℕ}

/-- **The bootstrap bound from Lemma 1 at one cut.** Let `Ω` be a unit vector on the chain of
`L` sites with local dimension `q ≥ 2`, and suppose that at the cut `j` and every length `m`
there is a factorization `IsFactorizationAt Ω j m (C₁ e^{-m/ξ'})`, with `ξ' > 0` and
`C₁ ≥ 1`: the conclusion of Hastings' Lemma 1. Then for every mixture `∑ wᵢ |ψᵢ⟩⟨ψᵢ|` of unit
trace of vectors of cut rank at most `k` with overlap `P > 0` with `Ω`, the entropy of the
first `j` sites is at most `ln k + ξ' ln(2 C₁²/P) ln q + F(ξ', q)`.
Hastings, arXiv:0705.2024v4, Lemma 2 (`ble`), lines 280–311; this is
`entropy_le_of_overlap_schmidtRank_mixture_of_factorization` with its factorization hypothesis
read off `IsFactorizationAt`, since `[j − m, j + m)` lies in the first `j + m` sites. -/
theorem entropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt (hq : 2 ≤ q)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (j : ℕ) {ξ' C₁ : ℝ} (hξ : 0 < ξ')
    (hC₁ : 1 ≤ C₁)
    (hfact : ∀ m : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      IsFactorizationAt Ω j m (C₁ * Real.exp (-(m / ξ'))) OB OL OR)
    {k r : ℕ} (hk : 1 ≤ k) (w : Fin r → ℝ) (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q))
    (hw : ∀ i, 0 ≤ w i) (hrank : ∀ i, (cutMatrix (ψ i) j).rank ≤ k)
    (hnorm : ∑ i, w i * ‖ψ i‖ ^ 2 = 1) {P : ℝ} (hP : 0 < P)
    (hPdef : ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 j) Ω ≤
      Real.log k + ξ' * Real.log (2 * C₁ ^ 2 / P) * Real.log q + bootstrapRemainder ξ' q :=
  entropy_le_of_overlap_schmidtRank_mixture_of_factorization hq hΩ j hξ hC₁
    (fun m _ ↦ by
      obtain ⟨OB, OL, OR, hF⟩ := hfact m
      obtain ⟨SB, SL, SR, h⟩ := exists_factorization_of_isFactorizationAt hF
      exact ⟨OB, OL, OR, SB, SL, SR, h⟩)
    hk w ψ hw hrank hnorm hP hPdef

end TNLean.MPS.AreaLaw.Hastings

namespace TNLean.MPS.AreaLaw

open Hastings
open scoped InnerProductSpace

/-- **Hastings' bootstrap lemma (Lemma 2).** Let `H` be a chain Hamiltonian of range `R` and
term norm at most `J ≥ 0` with a unique ground state `Ω` and gap `ΔE > 0`, and let
`ξ' > 6ξ` with `ξ = lemmaOneLength R J ΔE`. There is a constant `C₁ ≥ 1`, depending only on
`R`, `J`, `ΔE` and `ξ'`, such that for every such chain of `L` sites with local dimension
`q`, every cut `j` and every mixture `ρ = ∑ wᵢ |ψᵢ⟩⟨ψᵢ|` of unit trace of vectors of Schmidt
rank at most `k ≥ 1` across the cut with `⟨Ω, ρ Ω⟩ = P > 0`,
`S(ρ⁰_{1,j}) ≤ ln k + ξ' ln(2 C₁²/P) ln q + F(ξ', q)`.
Hastings, arXiv:0705.2024v4, Lemma 2 (`ble`), lines 280–311, with the decay length of the
module docstring. -/
theorem exists_entropy_le_of_overlap_schmidtRank_mixture (R : ℕ) {J ΔE : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < ΔE) {ξ' : ℝ} (hξ' : 6 * lemmaOneLength R J ΔE < ξ') :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 j) Ω ≤
          Real.log k + ξ' * Real.log (2 * C₁ ^ 2 / P) * Real.log q +
            bootstrapRemainder ξ' q := by
  obtain ⟨C, -, hF⟩ := exists_projectorFactorization R hJ hΔ hξ'
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro L q _ h E₀ Ω hgs j k r hk w ψ hw hrank hnorm P hP hPdef
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have hξ : 0 < ξ' := lt_trans (by positivity [lemmaOneLength_pos R J ΔE]) hξ'
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q ≤ 1` the entropy vanishes and the right side is nonnegative.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    refine (regionEntropy_le_card_mul_log hΩ _).trans ?_
    have hk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hξ0 : 0 ≤ Real.log (ξ' / 2 + 1) := Real.log_nonneg (by linarith)
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero, bootstrapRemainder, one_pow,
      sub_self, Real.log_zero, zero_add]
    linarith
  · refine entropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt hq hΩ j hξ
      (le_max_right _ _) (fun m ↦ ?_) hk w ψ hw hrank hnorm hP hPdef
    obtain ⟨OB, OL, OR, hFm⟩ := hF h hgs j m
    exact ⟨OB, OL, OR, hFm.mono
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw
