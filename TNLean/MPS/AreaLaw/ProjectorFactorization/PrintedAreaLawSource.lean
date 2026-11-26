/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProjectorFactorization.LiebRobinson
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.MPS.AreaLaw.ProjectorFactorization.AreaLaw
import Mathlib.Analysis.Complex.ExponentialBounds

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.Hastings.exists_regionEntropy_prefix_le_printed`: the entropy bound for an
  enlarged Lieb–Robinson length.
-/

section PrintedAreaLaw

/-!
## The entropy bound for an enlarged Lieb–Robinson length

The corrected doubling argument has exponential factor `2^(2ξ' log D)` at a fixed
factorization length `ξ'`. The source chooses a Lieb–Robinson velocity and length
existentially. Enlarging that length by a factor of two therefore recovers the
printed form `c₀ ξ' log ξ' log D 2^(ξ' log D)`.

The correction to the fixed-length iteration remains the one recorded in
`docs/paper-gaps/hastings07_doubling_constants.tex`.

Source: Hastings, arXiv:0705.2024v4, main theorem, eqs. `entbd` and `smd`,
lines 124–144, and the doubling iteration, lines 197–231.
-/

open scoped Matrix.Norms.L2Operator

open ManyBody (interval ChainInteraction)

namespace TNLean.MPS.AreaLaw.Hastings

open Real

open ManyBody (IsGapped groundSpace)

/-- The remainder in the bootstrap entropy estimate is bounded uniformly in the
local dimension. Hastings, arXiv:0705.2024v4, Lemma 2, lines 280–390. -/
private theorem bootstrapRemainder_le_log_product {ξ : ℝ} {q : ℕ}
    (hξ : 4 ≤ ξ) (hq : 2 ≤ q) :
    Entropy.tailEntropyRemainder ξ q ≤ 8 * ξ * log ξ * log q := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : (1 / 2 : ℝ) ≤ log q :=
    (by linarith [log_two_gt_d9] : (1 / 2 : ℝ) ≤ log 2).trans
      (log_le_log (by norm_num) hq')
  have hlogξ : 1 ≤ log ξ := by
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using log_pow (2 : ℝ) 2
    have := log_le_log (by norm_num : (0 : ℝ) < 4) hξ
    linarith [log_two_gt_d9]
  have hsq : log ((q : ℝ) ^ 2 - 1) ≤ 2 * log q :=
    (log_le_log (by nlinarith only [hq'] : (0 : ℝ) < (q : ℝ) ^ 2 - 1)
      (by linarith)).trans_eq
      (log_pow _ _)
  have hshort : log (ξ / 2 + 1) ≤ ξ :=
    (log_le_self (by linarith)).trans (by linarith)
  have hprod : ξ ≤ 2 * ξ * log q := by
    have := mul_le_mul_of_nonneg_left hlogq (by linarith : 0 ≤ ξ)
    linarith only [this]
  have hlogprod : ξ * log q ≤ ξ * log ξ * log q := by
    have := mul_le_mul_of_nonneg_right hlogξ
      (mul_nonneg (by linarith : 0 ≤ ξ) (by linarith : 0 ≤ log q))
    linarith only [this]
  have h6 : 6 * log q ≤ 3 / 2 * ξ * log q := by
    have := mul_le_mul_of_nonneg_right hξ (by linarith only [hlogq] : 0 ≤ log q)
    linarith only [this]
  unfold Entropy.tailEntropyRemainder
  linarith only [hsq, hshort, hprod, hlogprod, h6, hξ]

/-- A polynomial factorization constant gives the printed entropy-bound shape
after doubling the length. Hastings, arXiv:0705.2024v4, eq. `smd`, lines 134–142. -/
private theorem areaLawBound_le_log_product {ξ C a : ℝ} {q : ℕ}
    (hξ : 4 ≤ ξ) (hC : 1 ≤ C) (ha : 0 ≤ a) (hlogC : log C ≤ a * log ξ)
    (hq : 2 ≤ q) :
    areaLawBound ξ C q ≤
      (6 * (2 * a + 5) * (2 : ℝ) ^ (9 / log 2 + 1) + 2 * a + 20) *
        ξ * log ξ * log q * (2 : ℝ) ^ (2 * (ξ * log q)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogξ : 1 ≤ log ξ := by
    calc
      1 = log (exp 1) := (log_exp _).symm
      _ ≤ log ξ := log_le_log (exp_pos _) (by linarith only [hξ, exp_one_lt_d9])
  have hlog4C : log (4 * C) ≤ (a + 1) * log ξ := by
    rw [log_mul (by norm_num) (by linarith only [hC])]
    have := log_le_log (by norm_num : (0 : ℝ) < 4) hξ
    linarith only [this, hlogC]
  have hξlog : 1 ≤ ξ * log ξ := by
    have := mul_le_mul_of_nonneg_left hlogξ (by linarith only [hξ] : 0 ≤ ξ)
    linarith only [this, hξ]
  have hstart : doublingStartLength ξ (2 * C) + 1 ≤ (2 * a + 5) * ξ * log ξ := by
    unfold doublingStartLength
    rw [show 2 * (2 * C) = 4 * C by ring]
    have hm := mul_le_mul_of_nonneg_left hlog4C (by linarith only [hξ] : 0 ≤ 2 * ξ)
    linarith only [hm, hξlog]
  have hlogq : 0 ≤ log q := log_nonneg (by linarith only [hq'])
  have hmax := maxEntropyBound_le_of_one_le (C₁ := 2 * C) (C₂ := relentConst)
    (D := (q : ℝ)) (by linarith only [hξ]) (by linarith only [hC])
    (by linarith only [hq']) (by norm_num [relentConst])
  have hmax' : maxEntropyBound ξ (2 * C) relentConst q ≤
      (6 * (2 * a + 5) * (2 : ℝ) ^ (9 / log 2 + 1)) *
        ξ * log ξ * log q * (2 : ℝ) ^ (2 * (ξ * log q)) := by
    simp only [relentConst, show (2 : ℝ) + 7 = 9 by norm_num] at hmax
    rw [rpow_add (by norm_num : (0 : ℝ) < 2)] at hmax
    refine hmax.trans ?_
    calc
      _ ≤ 6 * log q * ((2 * a + 5) * ξ * log ξ) *
          ((2 : ℝ) ^ (2 * (ξ * log q)) * (2 : ℝ) ^ (9 / log 2 + 1)) := by
        gcongr
      _ = _ := by ring
  have hcore : ξ * log C * log q ≤ a * ξ * log ξ * log q := by
    calc
      _ ≤ ξ * (a * log ξ) * log q := by gcongr
      _ = _ := by ring
  have hsmall : 2 * (ξ * log C * log q + Entropy.tailEntropyRemainder ξ q) + 3 * log q ≤
      (2 * a + 20) * ξ * log ξ * log q := by
    have h3 := mul_le_mul_of_nonneg_right hξlog hlogq
    have hF := bootstrapRemainder_le_log_product hξ hq
    linarith only [hcore, h3, hF, hlogq]
  have hpow : 1 ≤ (2 : ℝ) ^ (2 * (ξ * log q)) :=
    one_le_rpow (by norm_num) (mul_nonneg (by norm_num)
      (mul_nonneg (by linarith only [hξ]) hlogq))
  have hsmall' : 2 * (ξ * log C * log q + Entropy.tailEntropyRemainder ξ q) + 3 * log q ≤
      (2 * a + 20) * ξ * log ξ * log q * (2 : ℝ) ^ (2 * (ξ * log q)) :=
    hsmall.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ (2 * a + 20) * ξ * log ξ * log q by positivity))
  linarith only [areaLawBound_le (by linarith only [hξ]) hC hq, hmax', hsmall']

/-- The logarithm of a cubic factorization constant grows at most logarithmically
in the decay length. Hastings, arXiv:0705.2024v4, Lemma 1, lines 258–262. -/
private theorem log_max_cubic_le {K ζ ξ : ℝ} (hK : 0 ≤ K) (hζ : 0 ≤ ζ)
    (hξ : 4 ≤ ξ) (hζξ : ζ ≤ ξ) :
    log (max (K * ζ ^ 3) 1) ≤ (log (K + 1) + 3) * log ξ := by
  have hξ3 : 1 ≤ ξ ^ 3 := one_le_pow₀ (by linarith only [hξ])
  have hC : max (K * ζ ^ 3) 1 ≤ (K + 1) * ξ ^ 3 := by
    refine max_le ?_ (one_le_mul_of_one_le_of_one_le (by linarith only [hK]) hξ3)
    calc
      K * ζ ^ 3 ≤ K * ξ ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hζ hζξ 3) hK
      _ ≤ (K + 1) * ξ ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hlog := log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hC
  rw [log_mul (by linarith only [hK]) (ne_of_gt (lt_of_lt_of_le zero_lt_one hξ3)),
    log_pow] at hlog
  have hlogξ : 1 ≤ log ξ := by
    calc
      1 = log (exp 1) := (log_exp _).symm
      _ ≤ log ξ := log_le_log (exp_pos _) (by linarith only [hξ, exp_one_lt_d9])
  have hm := mul_le_mul_of_nonneg_left hlogξ
    (log_nonneg (by linarith only [hK] : 1 ≤ K + 1))
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog, hm]

/-- **Hastings' entropy bound for an enlarged length.** There is a constant `c₀ > 0`,
depending only on the interaction range, such that the entropy of every initial segment
is at most `c₀ ξ' log ξ' log q 2^(ξ' log q)` whenever `ξ' = 6s` and
`s ≥ 2 lemmaOneEndpointLength R J Δ`. For nearest-neighbour interactions the constant
is numerical. Hastings, arXiv:0705.2024v4, main theorem, eqs. `entbd` and `smd`,
lines 124–144. The larger length absorbs the corrected fixed-length doubling exponent. -/
theorem exists_regionEntropy_prefix_le_printed (R : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ s : ℝ, 2 * lemmaOneEndpointLength R J Δ ≤ s → ∀ i : ℕ,
        ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L 0 i) ≤
          c₀ * (6 * s) * log (6 * s) * log q * (2 : ℝ) ^ ((6 * s) * log q) := by
  obtain ⟨K, hK, hbound⟩ := exists_regionEntropy_prefix_le R
  let a := log (K + 1) + 3
  have ha : 0 ≤ a := by
    have := log_nonneg (by linarith only [hK] : 1 ≤ K + 1)
    dsimp only [a]
    linarith only [this]
  let c₀ := 6 * (2 * a + 5) * (2 : ℝ) ^ (9 / log 2 + 1) + 2 * a + 20
  have hc₀ : 0 < c₀ := by dsimp only [c₀]; positivity
  refine ⟨c₀, hc₀, ?_⟩
  intro J Δ hJ hΔ L q _ h hh hhJ E₀ Ω hΩ hgap hspan s hs i
  by_cases hq : 2 ≤ q
  · let ζ := lemmaOneEndpointLength R J Δ
    have hζ : 20 ≤ ζ := by
      dsimp only [ζ]
      rw [lemmaOneEndpointLength_eq]
      have h16 := (sixteen_le_lemmaOneLength_and_le R (div_nonneg hJ hΔ.le)).1
      linarith only [h16]
    have hξ : 4 ≤ 6 * ζ := by linarith only [hζ]
    have hscalar := areaLawBound_le_log_product hξ (le_max_right (K * ζ ^ 3) 1) ha
      (log_max_cubic_le hK (by linarith only [hζ]) hξ (by linarith only [hζ])) hq
    change 2 * ζ ≤ s at hs
    have hlogq : 0 ≤ log q := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
    refine (hbound hJ hΔ h hh hhJ hΩ hgap hspan i).trans (hscalar.trans ?_)
    change c₀ * (6 * ζ) * log (6 * ζ) * log q * (2 : ℝ) ^ (2 * (6 * ζ * log q)) ≤ _
    have hzs : 6 * ζ ≤ 6 * s := by linarith only [hs, hζ]
    have hs0 : 0 ≤ s := by linarith only [hs, hζ]
    have hlogζ : 0 ≤ log (6 * ζ) := log_nonneg (by linarith only [hξ])
    have hlogs : 0 ≤ log (6 * s) := log_nonneg (by linarith only [hξ, hzs])
    have hpref : c₀ * (6 * ζ) * log (6 * ζ) * log q ≤
        c₀ * (6 * s) * log (6 * s) * log q := by
      gcongr
    have hexponent : 2 * (6 * ζ * log q) ≤ 6 * s * log q := by
      have := mul_le_mul_of_nonneg_right
        (show 2 * (6 * ζ) ≤ 6 * s by linarith only [hs]) hlogq
      linarith only [this]
    have hpow := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent
    exact mul_le_mul hpref hpow (rpow_nonneg (by norm_num) _) (by positivity)
  · have hq1 : q = 1 := by have := NeZero.one_le (n := q); omega
    subst q
    simpa only [Nat.cast_one, log_one, mul_zero, zero_mul] using
      ManyBody.regionEntropy_le_card_mul_log hΩ (interval L 0 i)

end TNLean.MPS.AreaLaw.Hastings

end PrintedAreaLaw

section PrintedAreaLawSource

open ManyBody (interval ChainInteraction)

open scoped ComplexOrder Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- The source Lieb–Robinson pair has velocity `40c_RJ`, length `80`, and numerical
prefactor `4`. Both observable supports are arbitrary finite sets.
Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112. -/
theorem _root_.ManyBody.ChainInteraction.norm_heisenberg_commutator_le_hastings_source
    {L q R : ℕ} {J : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 < J)
    (X Y : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A X)
    (hB : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val)
    (t : ℝ) (ht : |t| ≤ d / (40 * (chainLRVelocity R J - 1))) :
    ‖ManyBody.heisenbergEvolution h.hamiltonian t A * B -
        B * ManyBody.heisenbergEvolution h.hamiltonian t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ * Real.exp (-(d / 80)) := by
  have hw := chainLRVelocity_sub_one_pos R hJ
  exact h.norm_heisenberg_commutator_le_hastings hh hhJ
    (mul_pos (by norm_num) hw) (by linarith only [hw]) (by norm_num) X Y hA hB d hd t ht

/-- **The positive factorization at an admissible source length.** With velocity
`v = 40(chainLRVelocity R J - 1)` and `s = max(2v/Δ,80)`, the positive boundary factor
has error at most `K s³ exp(-l/(6s))`, with `K` depending only on the interaction range.
Hastings, arXiv:0705.2024v4, Lemma 1, lines 246–267, and the note added, lines 912–1003,
with the positivity correction of the module docstring. -/
theorem exists_projectorFactorization_posSemidef_source (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ c l : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        OB.PosSemidef ∧ Hastings.IsFactorizationAt Ω c l
          (K * s ^ 3 * Real.exp (-(l / (6 * s)))) OB OL OR := by
  obtain ⟨K, hK, hbound⟩ := exists_projectorFactorization_posSemidef_endpoint R
  refine ⟨K, hK, ?_⟩
  intro J Δ hJ hΔ L q _ h hh hhJ E₀ Ω hΩ hgap hspan s c l
  obtain ⟨OB, OL, OR, hOB, hfac⟩ := hbound hJ hΔ h hh hhJ hΩ hgap hspan c l
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
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      let s := max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ c l : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        Hastings.IsFactorizationAt Ω c l (K * s ^ 3 * Real.exp (-(l / (6 * s)))) OB OL OR := by
  obtain ⟨K, hK, hbound⟩ := exists_projectorFactorization_posSemidef_source R
  refine ⟨K, hK, ?_⟩
  intro J Δ hJ hΔ L q _ h hh hhJ E₀ Ω hΩ hgap hspan s c l
  obtain ⟨OB, OL, OR, -, hfac⟩ := hbound hJ hΔ h hh hhJ hΩ hgap hspan c l
  exact ⟨OB, OL, OR, hfac⟩

namespace Hastings

/-- **Hastings' area-law bound.** The velocity is proportional to `J` and the length
scale is numerical. With `v = 40(chainLRVelocity R J - 1)`, `ξ = max(2v/Δ,80)` and
`ξ' = 6ξ`, the entropy is at most `c₀ ξ' log ξ' log q 2^(ξ' log q)`. The constant
depends only on the interaction range and is numerical for nearest-neighbour terms.
Hastings, arXiv:0705.2024v4, main theorem, eqs. `entbd` and `smd`, lines 124–144. -/
theorem exists_regionEntropy_prefix_le_source (R : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      let ξ' := 6 * max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80
      ∀ i : ℕ, ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L 0 i) ≤
        c₀ * ξ' * Real.log ξ' * Real.log q * (2 : ℝ) ^ (ξ' * Real.log q) := by
  obtain ⟨c₀, hc₀, hbound⟩ := exists_regionEntropy_prefix_le_printed R
  refine ⟨c₀, hc₀, ?_⟩
  intro J Δ hJ hΔ L q _ h hh hhJ E₀ Ω hΩ hgap hspan
  exact hbound hJ hΔ h hh hhJ hΩ hgap hspan _
      (two_mul_lemmaOneEndpointLength_le_sourceLength R hJ hΔ)

end Hastings

end TNLean.MPS.AreaLaw

end PrintedAreaLawSource
