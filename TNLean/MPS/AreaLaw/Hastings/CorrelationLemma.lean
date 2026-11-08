/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalChain
import TNLean.MPS.AreaLaw.Hastings.PrintedAreaLawSource

/-!
# Hastings' correlation lemma at an admissible source length

For a gapped ground state, Hastings' Lemma 3 bounds the correlation of an operator
supported away from a cut and an operator diagonal in the Schmidt vectors at that cut.
The bound is `3 √(2ε(l)) + ε(l)`, with `ε(l) = C₁ exp(-l/ξ')`.

The positive factorization is supplied at the admissible source length
`s = max(2v/ΔE,80)`, where `v = 40 c_R J` and
`c_R = 2(R+1)2^(2R+1)exp(2R)`. At this length its rate is `ξ' = 6s` and its
constant is `C₁ = K s³`, with `K` depending only on the interaction range.
Both observable supports are arbitrary finite sets, as required by the
Lieb–Robinson bound. The resulting absolute-value estimate is stronger than the
source's one-sided correlation estimate.

**Local fix (positivity and length convention):** the factors are positive
semidefinite. At the original factorization length the positive repair halves the
rate; the enlarged admissible length absorbs that loss. The commutator bound uses
the reciprocal-length convention `exp(-d/ξ_C)` on `|t| ≤ d/v`. These corrections are
recorded in `docs/paper-gaps/hastings07_lemma1_positivity_rate.tex` and
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`.

Source: Hastings, arXiv:0705.2024v4, Lemma 3, eq. `fwdback`, lines 627–692;
Lemma 1, lines 246–267; note added, lines 912–1003.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

open Hastings

local notation "T" => toEuclideanCLM (𝕜 := ℂ)

/-- **Hastings' correlation lemma.** With
`s = max(2(40(chainLRVelocity R J - 1))/ΔE,80)` and `ξ' = 6s`, the correlation
of a contraction away from the cut and a Schmidt-diagonal contraction is at most
`3 √(2ε(l)) + ε(l)`, where `ε(l) = K s³ exp(-l/ξ')` and `K` depends only on `R`.
Hastings, arXiv:0705.2024v4, Lemma 3, eq. `fwdback`, lines 627–692, with the
positive-semidefinite and length conventions of the module docstring. -/
theorem exists_norm_inner_mul_sub_le (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J ΔE : ℝ}, 0 ≤ J → 0 < ΔE →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, IsGappedGroundState h.operator E₀ Ω ΔE →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / ΔE) 80
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
          3 * Real.sqrt (2 * (K * s ^ 3 *
              Real.exp (-(l / (6 * s))))) +
            K * s ^ 3 *
              Real.exp (-(l / (6 * s))) := by
  obtain ⟨K, hK, hF⟩ := exists_projectorFactorization_posSemidef_source R
  refine ⟨K, hK, ?_⟩
  intro J ΔE hJ hΔ L q _ h E₀ Ω hgs s j l ι _ a ψL ψR hψL hψR hdec O hO A SA hA hSA hA1
  obtain ⟨OB, OL, OR, hOB, hOL, hOR, -, hOB1, hsB, hsL, hsR, herr⟩ := hF hJ hΔ h hgs j l
  exact norm_inner_mul_sub_le_of_factorization hgs.1 a hψL hψR hdec hO hA hSA hA1
    ⟨OB, OL, OR, _, _, _, hOB, nonneg_iff_posSemidef.mp hOL.nonneg,
      nonneg_iff_posSemidef.mp hOR.nonneg, hOB1, hOL.norm_le, hOR.norm_le,
      hsB, subset_rfl, hsL, subset_rfl, hsR, disjoint_compl_left, herr⟩

end TNLean.MPS.AreaLaw
