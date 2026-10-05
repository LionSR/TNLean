/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLogBound
import TNLean.MPS.Preparation.BlockApproximationError
import TNLean.MPS.Preparation.RemainderBlocks
import TNLean.MPS.Preparation.ExplicitPreparationScale

/-!
# Every prescribed slope above half the correlation length at every ring length

For each prescribed `a > ξ/2`, choose `γ = ξ/(2a)`. The unequal-block estimate
`K M exp(-2γq/ξ)` then has rate `1/a`. Blocks of lengths
`q, ..., q, q + N % q` give error at most `ε` whenever
`q ≥ a log(N/ε) + b`, without requiring `q ∣ N`. The offset
`b = a max(log K,0) + L + 3D + 1` ensures injectivity of every used block.
If `q > N`, prepare the nonzero normalized target exactly.

Physical depth is at most `C(d,D) min(N,q)`. In particular one can take the explicit
ceiling of the displayed threshold. This extends the equal-block prescribed-slope result,
not just an existential choice of slope. The strict inequality `a > ξ/2` is retained;
no assertion at the endpoint `a = ξ/2` or at `t = 0` is made.

The remainder partition is the one in arXiv:2307.01696, Supplemental Material, proof of
Theorem 1. The sufficient coefficient `ξ/2` is a project improvement from the quadratic
overlap estimate, not a claim that the optimal physical circuit depth has been halved.

## References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696), Supplemental Material, proof of Theorem 1.
  The prescribed slope is a refinement using the quadratic overlap estimate.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

/-- **Every positive length and every prescribed slope `a > ξ/2`.** In the gauge of
arXiv:2307.01696, eq. (5), the quadratic unequal-block error estimate permits the displayed
slope at all ring lengths with nonzero periodic target. The last block absorbs the remainder;
when the chosen scale is longer than the ring, exact preparation is used instead.

The physical depth constant precedes the tensor, its spectral bound, and the prescribed
slope. The offset depends on these data, through the error prefactor and injectivity length.
The spectral bound is strictly between zero and one, as required for positive correlation
length. -/
theorem exists_isPreparedInDepth_allLength_of_slope (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (A B : MPSTensor d D) (ζ : ℂ) (σ : Matrix (Fin D) (Fin D) ℂ) (t : ℝ),
      ζ ≠ 0 → (∀ (N : ℕ) (s : Fin N → Fin d), mpv B s = ζ ^ N * mpv A s) →
      Kraus.IsNormal B → IsLeftCanonical B → σ.PosDef → σ.trace = 1 →
      Kraus.transferMap B σ = σ → 0 < t → t < 1 →
      (∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 → ‖μ‖ ≤ t) →
      ∀ a : ℝ, correlationLength t / 2 < a →
        ∃ b : ℝ, 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ (N q : ℕ) [NeZero N], mpvState A N ≠ 0 →
            a * Real.log (N / ε) + b ≤ q →
              ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ T ≤ C * min N q ∧
                IsPreparedInDepth T (fun s => ψ s) ∧
                1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_blockIsometryState d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D hd
  refine ⟨max (2 * Cb) Ce, fun A B ζ σ t hζ hmpv hNB hLC hσ htr hfix ht0 ht1
    hlam a ha => ?_⟩
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hξ : 0 < correlationLength (t : ℂ) :=
    correlationLength_pos (by rwa [hnorm]) (by rwa [hnorm])
  have ha0 : 0 < a := by linarith
  obtain ⟨K, hK, herr⟩ := exists_blockApproximationError_le_mul B hNB hLC hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => (hlam μ hμ hne).trans_eq hnorm.symm)
    (by rw [hnorm]; exact ht1.le)
    (γ := correlationLength (t : ℂ) / (2 * a)) (by positivity)
    ((div_lt_one (by positivity)).2 (by linarith))
  obtain ⟨L, hLpos, hL⟩ := hNB
  have hinj : ∀ n, L ≤ n → Kraus.IsInjective (blockTensor B n) := fun n hn =>
    (isNBlkInjective_iff_blockTensor_isInjective B n).mp (isNBlkInjective_of_le hLpos hL hn)
  let b : ℝ := a * max (Real.log K) 0 + L + 3 * D + 1
  have hb : 1 ≤ b := by
    have : 0 ≤ a * max (Real.log K) 0 + L + 3 * D := by positivity
    dsimp [b]
    linarith
  refine ⟨b, hb, fun ε hε hε1 N q _ hA0 hq => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlog : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hbq : b ≤ q := by linarith [mul_nonneg ha0.le hlog]
  have hmax : 0 ≤ a * max (Real.log K) 0 := by positivity
  have hLq : L ≤ q := by
    exact_mod_cast (show (L : ℝ) ≤ q by dsimp [b] at hbq; linarith)
  have hDq : 3 * D ≤ q := by
    exact_mod_cast (show (3 : ℝ) * D ≤ q by dsimp [b] at hbq; linarith)
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hphase := norm_inner_normalizedMPVState_of_mpv_eq hζ (hmpv N)
  by_cases hqN : q ≤ N
  · let ℓ := remainderBlockLengths q N
    have hsum := sum_remainderBlockLengths hq0 hqN
    have : NeZero (N / q) := ⟨(Nat.div_pos hqN hq0).ne'⟩
    have hℓq : ∀ j, q ≤ ℓ j := le_remainderBlockLengths q N
    have hℓ2q : ∀ j, ℓ j ≤ 2 * q := fun j =>
      (remainderBlockLengths_lt_two_mul hq0 j).le
    have hinjℓ : ∀ j, Kraus.IsInjective (blockTensor B (ℓ j)) :=
      fun j => hinj _ (hLq.trans (hℓq j))
    have hω : ∑ p, star (fixedPointPair σ p) * fixedPointPair σ p = 1 := by
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    refine ⟨blockIsometryState B (fixedPointPair σ) hsum, Cb * (2 * q),
      norm_blockIsometryState B hω hsum hinjℓ, ?_,
      hCb B _ hω ℓ hsum (2 * q) (fun j => hDq.trans (hℓq j)) hℓ2q hinjℓ, ?_⟩
    · rw [min_eq_right hqN, ← Nat.mul_assoc, Nat.mul_comm Cb 2]
      exact Nat.mul_le_mul_right q (le_max_left _ _)
    · rw [← hphase]
      refine (herr (N / q) ℓ hsum q hℓq hinjℓ).trans ?_
      have hexp : -(2 * (correlationLength (t : ℂ) / (2 * a))) * q /
          correlationLength (t : ℂ) = -((1 / a) * q) := by field_simp
      rw [hexp]
      calc K * ((N / q : ℕ) * Real.exp (-((1 / a) * q)))
          ≤ K * ((N : ℝ) ^ 1 * Real.exp (-((1 / a) * q))) := by
            simp only [pow_one]
            gcongr
            exact_mod_cast Nat.div_le_self N q
        _ ≤ ε := mul_pow_mul_exp_neg_le_of_le hK (by positivity) hN1 hε hε1
          (by simp) (by dsimp [b]; simp only [one_div, div_inv_eq_mul]; nlinarith) hq
  · have hstate : chainState (fun _ : Fin N => A) = mpvState A N := by
      ext s
      rw [chainState_apply, mpvState_apply, MPSChainTensor.coeff,
        MPSChainTensor.eval_const, mpv_eq, coeff_eq]
    obtain ⟨T, hT, hprep⟩ := hCe N (fun _ => A) (by rwa [hstate])
    refine ⟨normalizedMPVState A N, T, norm_normalizedMPVState hA0, ?_, ?_, ?_⟩
    · rw [min_eq_left (by omega : N ≤ q)]
      exact hT.trans (Nat.mul_le_mul_right N (le_max_right _ _))
    · simpa only [hstate, normalizedMPVState] using hprep
    · rw [inner_self_eq_norm_sq_to_K, norm_normalizedMPVState hA0]
      simpa using hε.le

end MPSPreparation
