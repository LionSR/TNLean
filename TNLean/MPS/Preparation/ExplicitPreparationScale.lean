/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousExactPreparation
import TNLean.MPS.Preparation.InjectivityCutoff

/-!
# Explicit blocking scale and physical preparation depth

For an error estimate `K N^k exp(-r q)`, choose
`q = ⌈a log(N/ε) + b⌉`, where `a ≥ max(k,1)/r` and
`b ≥ max(log K,0)/r + L + 3D + 1`. The rate is needed only at the selected usable
scale `q ≥ L`. Physical circuit depth is bounded by `C(d,D) min(N,q)`:
blocks between `q` and `2q` suffice when `q ≤ N`, and exact preparation handles `q > N`.
The normalized target must be nonzero, including in the exact branch.

This is a quantitative sufficient condition supplementing arXiv:2307.01696's
"Inhomogeneous short-range correlated MPS" paragraph. Its qualitative convergence assumption
does not imply the uniform rate used here; see `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- **Explicit scale, usable-scale cutoff, and physical depth.** The circuit constant depends
only on `d,D` and can be chosen as `max(2 Cb, Ce)`, where `Cb` is the block-preparation
constant and `Ce` the exact-preparation constant. The pair estimate is required only at the
selected scale when it does not exceed the ring length.

The uniform polynomial-exponential rate is an additional sufficient condition, not a
consequence asserted here of arXiv:2307.01696's qualitative inhomogeneous assumption. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_min_of_rate (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (N : ℕ) [NeZero N] (A : VaryingBondChain d D N), state A ≠ 0 →
      ∀ (K r : ℝ) (k L : ℕ) (a b ε : ℝ), 0 < K → 0 < r →
        max (k : ℝ) 1 / r ≤ a → max (Real.log K) 0 / r + L + 3 * D + 1 ≤ b →
        0 < ε → ε ≤ 1 →
        let q := ⌈a * Real.log (N / ε) + b⌉₊
        (0 < q → L ≤ q → q ≤ N →
          ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
            (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
            IsPairApproximable A hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) →
          3 * D + 1 ≤ q ∧ ∃ (ψ : MPVSpace d N) (T : ℕ),
            ‖ψ‖ = 1 ∧ T ≤ C * min N q ∧ IsPreparedInDepth T (fun s => ψ s) ∧
              1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, hCb⟩ := exists_isPreparedInDepth_of_isPairApproximable d D
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D hd
  refine ⟨max (2 * Cb) Ce, fun N _ A hA K r k L a b ε hK hr ha hb hε hε1 => ?_⟩
  dsimp only
  intro hrate
  let q := ⌈a * Real.log (N / ε) + b⌉₊
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ha0 : 0 ≤ a := (div_nonneg (le_trans zero_le_one (le_max_right _ _)) hr.le).trans ha
  have hlog : 0 ≤ Real.log (N / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  have hQq : a * Real.log (N / ε) + b ≤ (q : ℝ) := Nat.le_ceil _
  have hbase : max (Real.log K) 0 / r + L + 3 * D + 1 ≤ (q : ℝ) := by
    linarith [mul_nonneg ha0 hlog]
  have hmax : 0 ≤ max (Real.log K) 0 / r := by positivity
  have hLq : L ≤ q := by exact_mod_cast (show (L : ℝ) ≤ q by linarith)
  have hDq : 3 * D + 1 ≤ q := by
    exact_mod_cast (show (3 : ℝ) * D + 1 ≤ q by linarith)
  refine ⟨hDq, ?_⟩
  by_cases hqN : q ≤ N
  · obtain ⟨M, hM, ℓ, hsum, hℓq, hℓ2q, happ⟩ := hrate (by omega) hLq hqN
    let : NeZero M := ⟨hM.ne'⟩
    obtain ⟨ψ, hψ, hprep, herr⟩ := hCb ℓ hsum A (2 * q)
      (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))
      (fun j => (by omega : 3 * D ≤ q).trans (hℓq j)) hℓ2q happ
    refine ⟨ψ, Cb * (2 * q), hψ, ?_, hprep, herr.trans ?_⟩
    · rw [min_eq_right hqN, ← Nat.mul_assoc, Nat.mul_comm Cb 2]
      exact Nat.mul_le_mul_right q (le_max_left _ _)
    · exact mul_pow_mul_exp_neg_le_of_le hK hr hN1 hε hε1 ha (by linarith) hQq
  · obtain ⟨T, hT, hprep⟩ := hCe N (zeroPad A) (by rwa [← state_eq_chainState])
    have hu : ‖(‖state A‖ : ℂ)⁻¹ • state A‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
    refine ⟨_, T, hu, ?_, ?_, ?_⟩
    · rw [min_eq_left (by omega : N ≤ q)]
      exact hT.trans (Nat.mul_le_mul_right N (le_max_right _ _))
    · simpa only [← state_eq_chainState] using hprep
    · rw [inner_self_eq_norm_sq_to_K, hu]
      simpa using hε.le

end MPSPreparation
