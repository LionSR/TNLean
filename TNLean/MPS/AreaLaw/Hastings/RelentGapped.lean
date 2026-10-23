/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.RelentFromBootstrap
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant

/-!
# The entropy gain across a cut of a gapped chain

Hastings' eq. `relent` (arXiv:0705.2024v4, `law16.tex`, lines 234–242) bounds the mutual
information of the two intervals of `l` sites beside a cut of large entropy from below, for the
ground state of a gapped chain. Its proof (lines 413–503) combines Lemma 1, the approximate
factorization of the ground-state projector, with the bootstrap lemma and the monotonicity of
the relative entropy. This file supplies Lemma 1 at the printed rate
(`exists_projectorFactorization_endpoint`) to `relent_of_projectorFactorization_of_le_entropy`,
so that the hypotheses are those of the source: a gapped ground state of a chain Hamiltonian,
and the window condition of line 483 on the entropy of the cut. The length is
`ζ = lemmaOneEndpointLength R J ΔE`, the rate is `ξ' = 6ζ` as at lines 141–142, and the
constant is `C₁ = K ζ³`, polynomial in `ζ` as at lines 258–262, with `K` depending only on `R`.
The relative-entropy step uses the effect `O_Bᴴ O_B` (route 1 of the note added), so Lemma 1 is
used in its form without positivity, at the full rate.

**Local fix (explicit constants):** the bound holds with `C₁` replaced by `2 C₁` and with
`C₂ = relentConst`; only the values of the constants move. Documented in
`docs/paper-gaps/hastings07_relent_constants.tex`.

**Scope restriction (the length of Lemma 1):** the length `ζ = (5/4) ξ̂` comes from the chain
Lieb–Robinson estimate with its velocity raised by `5/4`. That estimate's prefactor grows with
`J` and its second operator acts on one site, so `ζ` has the form of the source's
`max(2v/ΔE, ξ_C)` but is not shown to arise from a pair satisfying eq. `lrb` (lines 96–112).
Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `exists_relent_of_isGappedGroundState`: eq. `relent` for the ground state of a gapped chain,
  at `ξ' = 6ζ` with `C₁ = K ζ³` and `K` independent of the chain, the interaction strength and
  the gap.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 234–267 and 413–503.
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
