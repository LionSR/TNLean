/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.RelentFromBootstrap
import TNLean.MPS.AreaLaw.Hastings.LiebRobinson

/-!
# The entropy gain across a cut of a gapped chain

Hastings' eq. `relent` (arXiv:0705.2024v4, lines 234–242 and 413–503)
bounds the mutual information of the two intervals beside a cut of large
entropy. This file derives it from the Hamiltonian assumptions and the
source's entropy-window condition. The relative-entropy step uses the
effect `O_Bᴴ O_B`, so the contraction form of approximate factorization
suffices.

**Scope restriction (auxiliary velocity):** the endpoint below uses
`ζ = lemmaOneEndpointLength R J ΔE`, `ξ' = 6ζ` and `C₁ = K ζ³`. Its
admissible physical Lieb–Robinson velocity is
`10ΔE * chainLRVelocity R (J/ΔE)`, which includes a gap-dependent term
rather than being expressed as a fixed multiple of `J`. The common order-`J` source-parameter
version is proved in `Hastings/SourceConsequences.lean`. See
`docs/paper-gaps/hastings07_lemma1_decay_length.tex` for this distinction
and the reciprocal-length convention.

**Local fix (explicit constants):** the bound uses `2 C₁` and
`C₂ = relentConst`. These changes affect only numerical constants and
are recorded in `docs/paper-gaps/hastings07_relent_constants.tex`.
-/

open Matrix

namespace TNLean.MPS.AreaLaw.Hastings

/-- **Eq. `relent` of Hastings' area law.** Let `R` be a range. There is a constant `K ≥ 0`,
depending only on `R`, with the following property. Let `h` be a chain Hamiltonian of range `R`
and term norm at most `J ≥ 0` with a gapped ground state `Ω` and gap `ΔE > 0`, let
`ζ = lemmaOneEndpointLength R J ΔE`, `ξ' = 6ζ` and `C₁ = K ζ³`, and let `c` be a cut and `l` a
length with `c + l ≤ L`. If the entropy of the first `c` sites is at least
`(l + ξ' ln C₁) ln q + F(ξ', q)`, the window condition of line 483, then the mutual information
of `A = [c - l, c)` and `B = [c, c + l)` is at least `(1 − 2ε') l/ξ' − ln (2 C₁) − C₂` with
`ε' = 2 C₁ e^{-l/ξ'}` and `C₂ = relentConst`.

For local dimension `q = 1` the window condition never holds, since the entropy of the first
`c` sites is `0` while `F(ξ', 1) = 1 + ln(ξ'/2 + 1) > 0`; the proof treats that case directly.

Hastings, arXiv:0705.2024v4, `law16.tex`, eq. `relent` (lines 234–242), proved at
lines 413–503, with the constants of the module docstring. -/
theorem exists_relent_of_isGappedGroundState (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ c l : ℕ, c + l ≤ L →
      (l + 6 * lemmaOneEndpointLength R J ΔE *
          Real.log (K * lemmaOneEndpointLength R J ΔE ^ 3)) * Real.log q +
          bootstrapRemainder (6 * lemmaOneEndpointLength R J ΔE) q ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 c) Ω →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) (c + l)) Ω ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) c) Ω +
          Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L c (c + l)) Ω -
          (1 - 2 * ((2 * (K * lemmaOneEndpointLength R J ΔE ^ 3)) *
            Real.exp (-(l / (6 * lemmaOneEndpointLength R J ΔE))))) *
            (l / (6 * lemmaOneEndpointLength R J ΔE)) +
          Real.log (2 * (K * lemmaOneEndpointLength R J ΔE ^ 3)) + relentConst := by
  obtain ⟨K₀, hK₀, hF⟩ := exists_projectorFactorization_endpoint R
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs c l hcl hS
  have hζ8 : 8 ≤ lemmaOneEndpointLength R J ΔE := by
    unfold lemmaOneEndpointLength
    have := le_max_right (2 * (5 / 4 * chainLRVelocity R (J / ΔE))) (1 : ℝ)
    linarith
  have hξ : 0 < 6 * lemmaOneEndpointLength R J ΔE := by linarith
  have hpow : 1 ≤ lemmaOneEndpointLength R J ΔE ^ 3 := one_le_pow₀ (by linarith)
  have hC₁ : 1 ≤ (K₀ + 1) * lemmaOneEndpointLength R J ΔE ^ 3 := by nlinarith
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q = 1` the window condition fails: the entropy vanishes and `F(ξ', 1) > 0`.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    have hS0 := TNLean.Lattice.regionEntropy_le_card_mul_log hgs.1 (interval L 0 c)
    have hξ0 : 0 ≤ Real.log (6 * lemmaOneEndpointLength R J ΔE / 2 + 1) :=
      Real.log_nonneg (by linarith)
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_add, bootstrapRemainder, one_pow,
      sub_self, Real.log_zero, add_zero] at hS hS0
    exfalso
    linarith
  refine relent_of_projectorFactorization_of_le_entropy hq hgs.1 hcl hξ hC₁ (fun m _ ↦ ?_) hS
  obtain ⟨OB, OL, OR, hF'⟩ := hF hJ hΔ h hgs c m
  refine ⟨OB, OL, OR, hF'.mono (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)⟩
  nlinarith

end TNLean.MPS.AreaLaw.Hastings
