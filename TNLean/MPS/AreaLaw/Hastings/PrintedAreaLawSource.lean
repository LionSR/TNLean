/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.PrintedAreaLaw
import TNLean.MPS.AreaLaw.Hastings.LiebRobinson

/-!
# Hastings' entropy bound with an interaction-proportional velocity

Choose the Lieb–Robinson pair `v = 40 c_R J`, `ξ_C = 80`, where
`c_R = 2(R+1)2^(2R+1)exp(2R)`. Its length `s = max(2v/Δ, ξ_C)` is at least twice
the factorization length. The corrected doubling argument therefore gives
the printed entropy bound at `ξ' = 6s`, with a constant depending only on the range.

**Local fix (length convention):** the pair uses decay `exp(-d/ξ_C)` and time bound
`|t| ≤ d/v`, as documented in `docs/paper-gaps/hastings07_lemma1_decay_length.tex`.
The correction to the fixed-length iteration remains recorded in
`docs/paper-gaps/hastings07_doubling_constants.tex`.

**Local fix (positivity):** the boundary factor is positive semidefinite, rather than
positive definite. At the enlarged length the positive factorization has the full
source decay rate. The correction at a fixed length is recorded in
`docs/paper-gaps/hastings07_lemma1_positivity_rate.tex`.

Source: Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112, and the main theorem,
eqs. `entbd` and `smd`, lines 124–144.
-/

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The source Lieb–Robinson pair has velocity `40c_RJ`, length `80`, and numerical
prefactor `4`. Both observable supports are arbitrary finite sets.
Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112. -/
theorem ChainHamiltonian.norm_heisenberg_commutator_le_hastings_source
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J) (hJ : 0 < J)
    (X Y : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A X)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val)
    (t : ℝ) (ht : |t| ≤ d / (40 * (chainLRVelocity R J - 1))) :
    ‖QuantumCircuit.heisenbergEvolution h.operator t A * B -
        B * QuantumCircuit.heisenbergEvolution h.operator t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ * Real.exp (-(d / 80)) := by
  have hw := chainLRVelocity_sub_one_pos R hJ
  exact h.norm_heisenberg_commutator_le_hastings
    (mul_pos (by norm_num) hw) (by linarith only [hw]) (by norm_num) X Y hA hB d hd t ht

/-- **The positive factorization at an admissible source length.** With velocity
`v = 40(chainLRVelocity R J - 1)` and `s = max(2v/Δ,80)`, the positive boundary factor
has error at most `K s³ exp(-l/(6s))`, with `K` depending only on the interaction range.
Hastings, arXiv:0705.2024v4, Lemma 1, lines 246–267, and the note added, lines 912–1003,
with the positivity correction of the module docstring. -/
theorem exists_projectorFactorization_posSemidef_source (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ c l : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        OB.PosSemidef ∧ Hastings.IsFactorizationAt Ω c l
          (K * s ^ 3 * Real.exp (-(l / (6 * s)))) OB OL OR := by
  obtain ⟨K, hK, hbound⟩ := exists_projectorFactorization_posSemidef_endpoint R
  refine ⟨K, hK, ?_⟩
  intro J Δ hJ hΔ L q _ h E₀ Ω hgs s c l
  obtain ⟨OB, OL, OR, hOB, hfac⟩ := hbound hJ hΔ h hgs c l
  refine ⟨OB, OL, OR, hOB, hfac.mono ?_⟩
  have hs : 2 * lemmaOneEndpointLength R J Δ ≤ s :=
    two_mul_lemmaOneEndpointLength_le_sourceLength R hJ hΔ
  have hζ : 0 < lemmaOneEndpointLength R J Δ := by
    rw [lemmaOneEndpointLength_eq_sourceLength R J hΔ]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_right _ _)
  have hpow := pow_le_pow_left₀ hζ.le
    (show lemmaOneEndpointLength R J Δ ≤ s by linarith only [hs, hζ]) 3
  have hdecay := Real.exp_le_exp.mpr (neg_le_neg
    (div_le_div_of_nonneg_left (Nat.cast_nonneg l)
      (show 0 < 2 * (6 * lemmaOneEndpointLength R J Δ) by positivity)
      (show 2 * (6 * lemmaOneEndpointLength R J Δ) ≤ 6 * s by linarith only [hs])))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hK) hdecay (Real.exp_pos _).le
    (mul_nonneg hK (pow_nonneg (by linarith only [hs, hζ]) _))

/-- The contraction form of Lemma 1 at the same admissible source length and rate as
its positive form. Hastings, arXiv:0705.2024v4, Lemma 1, lines 246–267. -/
theorem exists_projectorFactorization_source (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ c l : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        Hastings.IsFactorizationAt Ω c l (K * s ^ 3 * Real.exp (-(l / (6 * s)))) OB OL OR := by
  obtain ⟨K, hK, hbound⟩ := exists_projectorFactorization_posSemidef_source R
  refine ⟨K, hK, ?_⟩
  intro J Δ hJ hΔ L q _ h E₀ Ω hgs s c l
  obtain ⟨OB, OL, OR, -, hfac⟩ := hbound hJ hΔ h hgs c l
  exact ⟨OB, OL, OR, hfac⟩

namespace Hastings

/-- **Hastings' area-law bound.** The velocity is proportional to `J` and the length
scale is numerical. With `v = 40(chainLRVelocity R J - 1)`, `ξ = max(2v/Δ,80)` and
`ξ' = 6ξ`, the entropy is at most `c₀ ξ' log ξ' log q 2^(ξ' log q)`. The constant
depends only on the interaction range and is numerical for nearest-neighbour terms.
Hastings, arXiv:0705.2024v4, main theorem, eqs. `entbd` and `smd`, lines 124–144. -/
theorem exists_regionEntropy_prefix_le_source (R : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      let ξ' := 6 * max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ i : ℕ, Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 i) Ω ≤
        c₀ * ξ' * Real.log ξ' * Real.log q * (2 : ℝ) ^ (ξ' * Real.log q) := by
  obtain ⟨c₀, hc₀, hbound⟩ := exists_regionEntropy_prefix_le_printed R
  refine ⟨c₀, hc₀, ?_⟩
  intro J Δ hJ hΔ L q _ h E₀ Ω hgs
  exact hbound hJ hΔ h hgs _ (two_mul_lemmaOneEndpointLength_le_sourceLength R hJ hΔ)

end Hastings

end TNLean.MPS.AreaLaw
