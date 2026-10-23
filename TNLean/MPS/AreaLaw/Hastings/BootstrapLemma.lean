/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ChainBootstrap
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant

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
`exists_projectorFactorization_pow`. The result is a quantitatively restricted Lemma 2 on Hastings'
own hypotheses: a chain Hamiltonian of finite range and finite interaction strength with a unique
gapped ground state. With `ξ̂ = lemmaOneLength R (J/ΔE) 1` the length of Lemma 1 in units of the
gap and `ξ' = κ ξ̂` for a fixed `κ > 6`, the constant is `C₁ = K ξ̂³`, with `K` depending only
on the range and `κ`. So `C₁` is bounded by a polynomial in the length, as the source requires
(lines 258–262), and is uniform in the chain length, local dimension, Hamiltonian, ground state,
cut and mixture.

The source's sites carry nearest-neighbour terms (lines 85–93), which it obtains from any
finite range by grouping sites; here the range `R` is arbitrary.

**Scope restriction (quantitative bounds):** `exists_entropy_le_of_overlap_schmidtRank_mixture`
inherits the quantitative restrictions of the formalized Lemma 1. Its length `ξ̂` comes from the
chain Lieb–Robinson estimate. That estimate is linear in the size of the support, as in the
source (lines 96–112), but its prefactor grows with `J` and its second operator acts on one site,
so `ξ̂` is not shown to be the source's `max(2v/ΔE, ξ_C)`. The bound is proved at the rate
`ξ' = κ ξ̂` for every `κ > 6`, with `K` depending on `κ`; the printed endpoint `ξ' = 6ξ`
(lines 139–142) is not established, and no counterexample to that endpoint is asserted.
Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
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

open Hastings Matrix TNLean.Lattice
open scoped InnerProductSpace

/-- **Hastings' bootstrap lemma (Lemma 2).** Let `κ > 6`. There is a constant `K ≥ 1`,
depending only on the range `R` and `κ`, with the following property. Let `H` be a chain
Hamiltonian of range `R` and term norm at most `J ≥ 0` with a unique ground state `Ω` and gap
`ΔE > 0`, on `L` sites with local dimension `q`, and let `ξ̂ = lemmaOneLength R (J/ΔE) 1`,
`ξ' = κ ξ̂` and `C₁ = K ξ̂³`. For every cut `j` and every mixture `ρ = ∑ wᵢ |ψᵢ⟩⟨ψᵢ|` of unit
trace of vectors of Schmidt rank at most `k ≥ 1` across the cut with `⟨Ω, ρ Ω⟩ = P > 0`,
`S(ρ⁰_{1,j}) ≤ ln k + ξ' ln(2 C₁²/P) ln q + F(ξ', q)`.
Hastings, arXiv:0705.2024v4, Lemma 2 (`ble`), lines 280–311, with `C₁` polynomial in the length
(lines 258–262) and the restrictions of the module docstring. -/
theorem exists_entropy_le_of_overlap_schmidtRank_mixture (R : ℕ) {κ : ℝ} (hκ : 6 < κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ (j : ℕ) {k r : ℕ}, 1 ≤ k → ∀ (w : Fin r → ℝ)
        (ψ : Fin r → EuclideanSpace ℂ (Fin L → Fin q)), (∀ i, 0 ≤ w i) →
        (∀ i, (cutMatrix (ψ i) j).rank ≤ k) → ∑ i, w i * ‖ψ i‖ ^ 2 = 1 →
        ∀ {P : ℝ}, 0 < P → ∑ i, w i * ‖⟪ψ i, Ω⟫_ℂ‖ ^ 2 = P →
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 j) Ω ≤
          Real.log k + κ * lemmaOneLength R (J / ΔE) 1 *
            Real.log (2 * (K * lemmaOneLength R (J / ΔE) 1 ^ 3) ^ 2 / P) * Real.log q +
            bootstrapRemainder (κ * lemmaOneLength R (J / ΔE) 1) q := by
  obtain ⟨K, -, hF⟩ := exists_projectorFactorization_pow R hκ
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs j k r hk w ψ hw hrank hnorm P hP hPdef
  have hΩ : ‖Ω‖ = 1 := hgs.1
  have h16 := (sixteen_le_lemmaOneLength_and_le R (div_nonneg hJ hΔ.le)).1
  have hξ : 0 < κ * lemmaOneLength R (J / ΔE) 1 := mul_pos (by linarith) (by linarith)
  have hC₁ : 1 ≤ max K 1 * lemmaOneLength R (J / ΔE) 1 ^ 3 :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ (by linarith))
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q ≤ 1` the entropy vanishes and the right side is nonnegative.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    refine (regionEntropy_le_card_mul_log hΩ _).trans ?_
    have hk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hξ0 : 0 ≤ Real.log (κ * lemmaOneLength R (J / ΔE) 1 / 2 + 1) :=
      Real.log_nonneg (by linarith)
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero, bootstrapRemainder, one_pow,
      sub_self, Real.log_zero, zero_add]
    linarith
  · refine entropy_le_of_overlap_schmidtRank_mixture_of_isFactorizationAt hq hΩ j hξ hC₁
      (fun m ↦ ?_) hk w ψ hw hrank hnorm hP hPdef
    obtain ⟨OB, OL, OR, hFm⟩ := hF hJ hΔ h hgs j m
    exact ⟨OB, OL, OR, hFm.mono (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos (by linarith) 3).le)
      (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw
