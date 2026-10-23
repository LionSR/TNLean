/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalChain
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant

/-!
# Hastings' Lemma 3 on the chain

Lemma 3 of Hastings, *An area law for one-dimensional quantum systems* (arXiv:0705.2024v4,
`References/0705.2024/law16.tex`, lines 627–646, eq. `fwdback`), bounds the correlation between
an operator `A` supported away from the `l` sites on either side of a cut and an operator `B_L`
that is diagonal in the left Schmidt vectors of the ground state `Ψ₀`:
`⟨Ψ₀, A B_L Ψ₀⟩ − ⟨Ψ₀, A Ψ₀⟩⟨Ψ₀, B_L Ψ₀⟩ ≤ 3 √(2ε(l)) + ε(l)` with `ε(l) = C₁ e^{-l/ξ'}`.
Its proof uses the Hamiltonian only through the positive operators `O_B`, `O_L`, `O_R` of
Lemma 1.

This file discharges the factorization hypothesis of `norm_inner_mul_sub_le_of_factorization` with
the positive form of Lemma 1 at the printed rate,
`exists_projectorFactorization_posSemidef_endpoint`. The result is a quantitatively restricted
Lemma 3 on Hastings' own hypotheses: a chain Hamiltonian of finite range and finite interaction
strength with a unique gapped ground state. With `ζ = lemmaOneEndpointLength R J ΔE` the length
of Lemma 1 and `ξ' = 6ζ` the printed rate (lines 139–142), the constant is `C₁ = K ζ³` with `K`
depending only on the range, so it is bounded by a polynomial in the length (lines 258–262) and
does not depend on the length of the chain, the cut, the Schmidt data or `A`. The bound is on
the modulus of the difference, which is stronger than the printed one-sided bound.

**Local fix (positivity rate):** the proof of Lemma 3 needs `O_B` positive, and the positive
form of Lemma 1 decays at half its rate, so eq. `fwdback` holds with
`ε(l) = C₁ e^{-l/(2 · 6ζ)}` rather than at the rate `ξ' = 6ζ` of Lemma 1. Documented in
`docs/paper-gaps/hastings07_lemma1_positivity_rate.tex`.

**Scope restriction (quantitative bounds):** `exists_norm_inner_mul_sub_le` inherits the
quantitative restriction of the formalized Lemma 1. Its length
`ζ = (5/4) lemmaOneLength R (J/ΔE) 1` comes from the chain Lieb–Robinson estimate with the
velocity raised by `5/4`, whose prefactor grows with `J` and whose second operator acts on one
site, so `ζ` is not shown to be the source's `max(2v/ΔE, ξ_C)` for a Lieb–Robinson pair in the
source's sense (lines 96–112). Documented in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex` and
`docs/paper-gaps/hastings07_gaussian_average_exponent.tex`.

## Main results

* `exists_norm_inner_mul_sub_le`: Lemma 3.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

open Hastings

local notation "T" => toEuclideanCLM (𝕜 := ℂ)

/-- **Hastings' Lemma 3 (eq. `fwdback`).** There is a constant `K ≥ 0`, depending only on the
range `R`, with the following property. Let `H` be a chain Hamiltonian of range `R` and term norm
at most `J ≥ 0` with a unique ground state `Ω` and gap `ΔE > 0`, on `L` sites, and let
`ζ = lemmaOneEndpointLength R J ΔE`. For every cut `j` and length `l`, every Schmidt
decomposition `Ω = ∑ a_α ψ_L(α) ⊗ ψ_R(α)` across the cut with orthonormal `ψ_L`, `ψ_R`, every
`B_L = ∑ O(α) |ψ_L(α)⟩⟨ψ_L(α)| ⊗ 1` with `|O(α)| ≤ 1`, and every `A` with `‖A‖ ≤ 1` supported
away from the sites `j − l, …, j + l − 1`,
`|⟨Ω, A B_L Ω⟩ − ⟨Ω, A Ω⟩⟨Ω, B_L Ω⟩| ≤ 3 √(2ε) + ε` with `ε = K ζ³ e^{-l/(2 · 6ζ)}`.
Hastings, arXiv:0705.2024v4, Lemma 3, lines 627–646, with `ξ' = 6ζ` (lines 139–142),
`C₁ = K ζ³` polynomial in the length (lines 258–262) and the local fix and restriction of the
module docstring. -/
theorem exists_norm_inner_mul_sub_le (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      ∀ (j l : ℕ) {ι : Type*} [Fintype ι] (a : ι → ℂ)
        {ψL : ι → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L j))}
        {ψR : ι → EuclideanSpace ℂ ((v : {v // v ∉ leftBlock L j}) → Fin q)},
        Orthonormal ℂ ψL → Orthonormal ℂ ψR →
        WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) =
          (fun p ↦ ∑ α, a α * (WithLp.ofLp (ψL α) p.1 * WithLp.ofLp (ψR α) p.2)) →
        ∀ {O : ι → ℂ}, (∀ α, ‖O α‖ ≤ 1) →
        ∀ {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {SA : Finset (Fin L)},
        Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A SA →
        Disjoint SA (interval L (j - l) (j + l)) → ‖A‖ ≤ 1 →
        ‖⟪Ω, T (A * Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ -
            ⟪Ω, T A Ω⟫_ℂ *
              ⟪Ω, T (Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ‖ ≤
          3 * Real.sqrt (2 * (K * lemmaOneEndpointLength R J ΔE ^ 3 *
              Real.exp (-(l / (2 * (6 * lemmaOneEndpointLength R J ΔE)))))) +
            K * lemmaOneEndpointLength R J ΔE ^ 3 *
              Real.exp (-(l / (2 * (6 * lemmaOneEndpointLength R J ΔE)))) := by
  obtain ⟨K, hK, hF⟩ := exists_projectorFactorization_posSemidef_endpoint R
  refine ⟨K, hK, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs j l ι _ a ψL ψR hψL hψR hdec O hO A SA hA hSA hA1
  obtain ⟨OB, OL, OR, hOB, hOL, hOR, -, hOB1, hsB, hsL, hsR, herr⟩ := hF hJ hΔ h hgs j l
  exact norm_inner_mul_sub_le_of_factorization hgs.1 a hψL hψR hdec hO hA hSA hA1
    ⟨OB, OL, OR, _, _, _, hOB, nonneg_iff_posSemidef.mp hOL.nonneg,
      nonneg_iff_posSemidef.mp hOR.nonneg, hOB1, hOL.norm_le, hOR.norm_le,
      hsB, subset_rfl, hsL, subset_rfl, hsR, disjoint_compl_left, herr⟩

end TNLean.MPS.AreaLaw
