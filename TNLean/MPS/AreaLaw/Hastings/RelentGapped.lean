/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.RelentFromBootstrap
import TNLean.MPS.AreaLaw.Hastings.ProjectorFactorization

/-!
# The entropy gain across a cut of a gapped chain

Hastings' eq. `relent` (arXiv:0705.2024v4, `law16.tex`, lines 234–242) bounds the mutual
information of the two intervals of `l` sites beside a cut of large entropy from below, for the
ground state of a gapped chain. Its proof (lines 413–503) combines Lemma 1, the approximate
factorization of the ground-state projector, with the bootstrap lemma and the monotonicity of
the relative entropy. This file supplies Lemma 1 (`exists_projectorFactorization`) to
`relent_of_projectorFactorization_of_le_entropy`, so that the hypotheses are those of the
source: a gapped ground state of a chain Hamiltonian, and the window condition of line 483 on
the entropy of the cut.

**Local fix (explicit constants):** the bound holds with `C₁` replaced by `2 C₁` and with
`C₂ = relentConst`; only the values of the constants move. Documented in
`docs/paper-gaps/hastings07_relent_constants.tex`.

**Scope restriction (the constant of Lemma 1):** the constant `C₁` comes from Lemma 1 as
formalized. It depends only on `R`, `J`, `ΔE` and `ξ'`, not on the chain length, the local
dimension or the cut, but it is not shown to be bounded by a polynomial in `ξ` as the source
states (lines 258–262). The length `ξ = lemmaOneLength R J ΔE` comes from a chain
Lieb–Robinson estimate with a support factor `|X|²`; it has the form of the source's
`max(2v/ΔE, ξ_C)` but is not proved equal to it for a pair satisfying eq. `lrb`
(lines 96–112). Lemma 1 also holds here at every rate `ξ' > 6ξ` rather than at `ξ' = 6ξ`.
Documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex` and, for the rate,
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `exists_relent_of_isGappedGroundState`: eq. `relent` for the ground state of a gapped chain,
  with a constant `C₁ ≥ 1` independent of the length of the chain.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 234–267 and 413–503.
-/

open Matrix

namespace TNLean.MPS.AreaLaw.Hastings

/-- **Eq. `relent` of Hastings' area law.** Let `h` be a chain Hamiltonian of range `R` and term
norm `J ≥ 0` with a gapped ground state `Ω`, gap `ΔE > 0`, and let `ξ' > 6ξ` with
`ξ = lemmaOneLength R J ΔE`. There is a constant `C₁ ≥ 1`, independent of the length of the
chain, such that for local dimension `q ≥ 2`, every cut `c` and every length `l` with
`c + l ≤ L`: if the entropy of the first `c` sites is at least
`(l + ξ' ln C₁) ln q + F(ξ', q)`, the window condition of line 483, then the mutual information
of `A = [c - l, c)` and `B = [c, c + l)` is at least `(1 − 2ε') l/ξ' − ln (2 C₁) − C₂` with
`ε' = 2 C₁ e^{-l/ξ'}` and `C₂ = relentConst`.

The hypothesis `2 ≤ q` restricts nothing: for `q = 1` the entropy of the first `c` sites is
`0` while `F(ξ', 1) = 1 + ln(ξ'/2 + 1) > 0`, so the window condition never holds.

Hastings, arXiv:0705.2024v4, `law16.tex`, eq. `relent` (lines 234–242), proved at
lines 413–503, with the constants of the module docstring. -/
theorem exists_relent_of_isGappedGroundState (R : ℕ) {J ΔE : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < ΔE)
    {ξ' : ℝ} (hξ' : 6 * lemmaOneLength R J ΔE < ξ') :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      2 ≤ q → ∀ c l : ℕ, c + l ≤ L →
      (l + ξ' * Real.log C₁) * Real.log q + bootstrapRemainder ξ' q ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 c) Ω →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) (c + l)) Ω ≤
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L (c - l) c) Ω +
          Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L c (c + l)) Ω -
          (1 - 2 * ((2 * C₁) * Real.exp (-(l / ξ')))) * (l / ξ') + Real.log (2 * C₁) +
          relentConst := by
  obtain ⟨C, -, hF⟩ := exists_projectorFactorization R hJ hΔ hξ'
  have hξ : 0 < ξ' := (mul_pos (by norm_num) (lemmaOneLength_pos R J ΔE)).trans hξ'
  refine ⟨max C 1, le_max_right _ _, fun h E₀ Ω hgs hq c l hcl hS ↦ ?_⟩
  refine relent_of_projectorFactorization_of_le_entropy hq hgs.1 hcl hξ (le_max_right _ _)
    (fun m _ ↦ ?_) hS
  obtain ⟨OB, OL, OR, hF'⟩ := hF h hgs c m
  exact ⟨OB, OL, OR, hF'.mono
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

end TNLean.MPS.AreaLaw.Hastings
