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
the relative entropy. This file supplies Lemma 1 with a polynomial constant
(`exists_projectorFactorization_pow`) to `relent_of_projectorFactorization_of_le_entropy`, so
that the hypotheses are those of the source: a gapped ground state of a chain Hamiltonian, and
the window condition of line 483 on the entropy of the cut. In units of the gap the length is
`ξ̂ = lemmaOneLength R (J/ΔE) 1`, the rate is `ξ' = κ ξ̂` for a fixed `κ > 6`, and the constant
is `C₁ = K ξ̂³`, polynomial in `ξ̂` as at lines 258–262, with `K` depending only on `R` and `κ`.

**Local fix (explicit constants):** the bound holds with `C₁` replaced by `2 C₁` and with
`C₂ = relentConst`; only the values of the constants move. Documented in
`docs/paper-gaps/hastings07_relent_constants.tex`.

**Scope restriction (the rate and the length of Lemma 1):** Lemma 1 is used at the rate
`ξ' = κ ξ̂` for a fixed `κ > 6`, with `K` depending on `κ`, rather than at the printed
`ξ' = 6ξ`. The length `ξ̂` comes from a chain Lieb–Robinson estimate whose prefactor grows
with `J` and whose second operator acts on one site; it has the form of the source's
`max(2v/ΔE, ξ_C)` but is not proved equal to it for a pair satisfying eq. `lrb`
(lines 96–112). Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `exists_relent_of_isGappedGroundState`: eq. `relent` for the ground state of a gapped chain,
  with `C₁ = K ξ̂³` and `K` independent of the chain, the interaction strength and the gap.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 234–267 and 413–503.
-/

open Matrix

namespace TNLean.MPS.AreaLaw.Hastings

/-- **Eq. `relent` of Hastings' area law.** Let `R` be a range and `κ > 6`. There is a constant
`K ≥ 0`, depending only on `R` and `κ`, with the following property. Let `h` be a chain
Hamiltonian of range `R` and term norm at most `J ≥ 0` with a gapped ground state `Ω` and gap
`ΔE > 0`, let `ξ̂ = lemmaOneLength R (J/ΔE) 1`, `ξ' = κ ξ̂` and `C₁ = K ξ̂³`, and let `c` be a
cut and `l` a length with `c + l ≤ L`. If the entropy of the first `c` sites is at least
`(l + ξ' ln C₁) ln q + F(ξ', q)`, the window condition of line 483, then the mutual information
of `A = [c - l, c)` and `B = [c, c + l)` is at least `(1 − 2ε') l/ξ' − ln (2 C₁) − C₂` with
`ε' = 2 C₁ e^{-l/ξ'}` and `C₂ = relentConst`.

For local dimension `q = 1` the window condition never holds, since the entropy of the first
`c` sites is `0` while `F(ξ', 1) = 1 + ln(ξ'/2 + 1) > 0`; the proof treats that case directly.

Hastings, arXiv:0705.2024v4, `law16.tex`, eq. `relent` (lines 234–242), proved at
lines 413–503, with the constants of the module docstring. -/
theorem exists_relent_of_isGappedGroundState (R : ℕ) {κ : ℝ} (hκ : 6 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ c l : ℕ, c + l ≤ L →
      (l + κ * lemmaOneLength R (J / ΔE) 1 *
          Real.log (K * lemmaOneLength R (J / ΔE) 1 ^ 3)) * Real.log q +
          bootstrapRemainder (κ * lemmaOneLength R (J / ΔE) 1) q ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 c) Ω →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) (c + l)) Ω ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) c) Ω +
          Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L c (c + l)) Ω -
          (1 - 2 * ((2 * (K * lemmaOneLength R (J / ΔE) 1 ^ 3)) *
            Real.exp (-(l / (κ * lemmaOneLength R (J / ΔE) 1))))) *
            (l / (κ * lemmaOneLength R (J / ΔE) 1)) +
          Real.log (2 * (K * lemmaOneLength R (J / ΔE) 1 ^ 3)) + relentConst := by
  obtain ⟨K₀, hK₀, hF⟩ := exists_projectorFactorization_pow R hκ
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs c l hcl hS
  have hξ16 := (sixteen_le_lemmaOneLength_and_le R (div_nonneg hJ hΔ.le)).1
  have hξ : 0 < κ * lemmaOneLength R (J / ΔE) 1 := mul_pos (by linarith) (by linarith)
  have hpow : 1 ≤ lemmaOneLength R (J / ΔE) 1 ^ 3 := one_le_pow₀ (by linarith)
  have hC₁ : 1 ≤ (K₀ + 1) * lemmaOneLength R (J / ΔE) 1 ^ 3 := by nlinarith
  rcases lt_or_ge q 2 with hq | hq
  · -- For `q = 1` the window condition fails: the entropy vanishes and `F(ξ', 1) > 0`.
    have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst hq1
    have hS0 := TNLean.Lattice.regionEntropy_le_card_mul_log hgs.1 (interval L 0 c)
    have hξ0 : 0 ≤ Real.log (κ * lemmaOneLength R (J / ΔE) 1 / 2 + 1) :=
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
