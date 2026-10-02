/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SecondOrderBlockOverlap

/-!
# The approximation error for overlapping blocks at the second-order rate

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound the
error of the approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of eq. (S7) for a tensor that is not normal
by `ε = O((N/q) e^{-γ q/ξ_diag})`, `0 < γ < 1/2`. For normal blocks of multiplicity one and unit
weights whose `q`-site states may overlap, `TNLean.MPS.Preparation.OverlappingBlockError` proves
`ε ≤ C (N/q) e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. This file proves the second-order rate

  `ε ≤ C (N/q) e^{-2γ q/ξ}` for every `0 < γ < 1`

(`exists_approximationError_le_overlappingBlockSum_sq` and its `O`-form
`exists_approximationError_le_mul_overlappingBlockSum_sq`), for every block length `q` and every
number of blocks `M ≥ 1`. For the blocks `A_1 = (1, 0)` and `A_2 = (3/5, 4/5)` the error is at
least `(9/25)^q / 16` once `M ≥ 3`
(`MPSTensor.le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`), where `3/5` is the
eigenvalue of the mixed transfer map and `λ₂ = 3/5` is admissible, so the exponent `2γ q/ξ` cannot
be replaced by `c q/ξ` with `c > 2`.

The proof combines the overlap `num = b^{-1/2} ∑ⱼ zⱼ` after `V^{⊗M}`
(`sum_star_nonNormalApproxVector_mul_mpv`) with the elementary bound
`1 - s/t ≤ 2 (t² - s²)` for `t² ≥ 1/2`, where `t = ‖φ_N‖` and `s = |num|`. For `M ≥ 2`,
`t² - s² ≤ |t² - b| + 2 ∑ⱼ |zⱼ - 1|`, with the overlaps `zⱼ` to second order
(`exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le_sq`) and `|t² - b| = O(e^{-γ N/ξ})`
(`exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one`), which is `O(e^{-2γ q/ξ})` for
`N = qM ≥ 2q`. For `M = 1`, `s = |⟨W|u⟩|/√b` with `u = φ_1(P)`, `t = ‖u‖` and
`W = ∑ⱼ φ_1(P'_{j,∞})` of squared norm `b`; then `t² - s² ≤ ‖u - W‖²` and `W = φ_1(P_∞)`, so that
`‖u - W‖ = O(‖P - P_∞‖)`.

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-2γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`, for every `0 < γ < 1`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (multiplicity one, unit weights):** every block occurs once, with weight `1`.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one` — the norm of the target at
  the rate `e^{-γ N/ξ}`, `0 < γ < 1`.
* `MPSTensor.one_sub_norm_nonNormalApproxOverlap_blockSum_le` — the error is at most
  `1 - |∑ⱼ zⱼ| / (√b ‖φ_N‖)`.
* `MPSTensor.exists_approximationError_le_overlappingBlockSum_sq`,
  `MPSTensor.exists_approximationError_le_mul_overlappingBlockSum_sq` — Lemma 1'(ii) for overlapping
  blocks of multiplicity one and unit weights, at the second-order rate.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### Elementary estimates -/

/-- If `t² ≥ 1/2` and `t² - s² ≤ X` with `X ≥ 0` and `s ≥ 0`, then `1 - s/t ≤ 2 X`. -/
theorem one_sub_div_le_two_mul_of_sq_sub_sq_le {s t X : ℝ} (hs : 0 ≤ s) (ht0 : 0 ≤ t)
    (ht : 1 / 2 ≤ t ^ 2) (hX0 : 0 ≤ X) (hX : t ^ 2 - s ^ 2 ≤ X) : 1 - s / t ≤ 2 * X := by
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h] at ht; norm_num at ht
  rcases le_or_gt t s with hts | hts
  · have : 1 ≤ s / t := (one_le_div htpos).2 hts
    linarith
  · have hr0 : 0 ≤ s / t := div_nonneg hs ht0
    have hr1 : s / t < 1 := (div_lt_one htpos).2 hts
    have h1 : 1 - s / t ≤ 1 - (s / t) ^ 2 := by nlinarith
    have h2 : 1 - (s / t) ^ 2 = (t ^ 2 - s ^ 2) / t ^ 2 := by
      field_simp
    have h3 : (t ^ 2 - s ^ 2) / t ^ 2 ≤ 2 * X := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

/-! ### The norm of the target -/

variable {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- **The norm of the target at the rate of the mixed transfer maps.** In the setting of
`exists_norm_gram_blockTensor_blockSum_sub_le`, with `0 < γ < 1`, the periodic state of the direct
sum with unit weights on `N ≥ 1` sites satisfies `|‖φ_N‖² - b| ≤ K e^{-γ N/ξ}`. Its squared norm
is `∑ⱼ ∑ₖ ⟨φ_N(A_k)|φ_N(A_j)⟩`; the diagonal terms are `1` up to `O(e^{-γ N/ξ})` by the normal case
at `γ/2` (`exists_abs_norm_mpvState_sq_sub_one_le`), and the others decay at the rate of the mixed
transfer maps (`exists_norm_mpvOverlap_le_of_mixedMapLM`). This extends
`exists_abs_norm_mpvState_blockSum_sq_sub_le` from `γ < 1/2` to `γ < 1`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the bound on
`|c_N²/\tilde c_N² - 1|`. -/
theorem exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N ≠ 0 →
      |‖mpvState (blockSum Aj ι fun _ => 1) N‖ ^ 2 - b| ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx2 : Real.exp (-(γ / 2) / correlationLength lam₂) ^ 2 = x := by
    rw [← exp_neg_two_mul_div_correlationLength]; congr 2; ring
  choose K₅ hK₅ hc using fun j => exists_abs_norm_mpvState_sq_sub_one_le (Aj j) (hN j) (hA j)
    (hσ j) (htr j) (hfix j) (hlam j) (γ := γ / 2) (by positivity) (by linarith)
  simp only [hx2] at hc
  have hoff : ∀ j k, ∃ K : ℝ, 0 ≤ K ∧ (j ≠ k → ∀ N : ℕ,
      ‖mpvOverlap (Aj j) (Aj k) N‖ ≤ K * x ^ N) := fun j k => by
    by_cases hjk : j = k
    · exact ⟨0, le_rfl, fun h => absurd hjk h⟩
    · obtain ⟨K, hK, h⟩ := exists_norm_mpvOverlap_le_of_mixedMapLM (Aj j) (Aj k) hl
        (hmix j k hjk) hγ0 hγ
      exact ⟨K, hK, fun _ => h⟩
  choose Ko hKo hob using hoff
  refine ⟨∑ j, K₅ j + ∑ j, ∑ k, Ko j k,
    add_nonneg (Finset.sum_nonneg fun j _ => hK₅ j)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hKo j k),
    fun N hN0 => ?_⟩
  have hsum : ((‖mpvState (blockSum Aj ι fun _ => 1) N‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, mpvOverlap (Aj j) (Aj k) N := by
    rw [ofReal_norm_mpvState_sq, mpvOverlap]
    simp_rw [mpv_blockSum hι hdisj _ hN0, one_pow, one_mul, star_sum, Finset.sum_mul_sum,
      mpvOverlap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have hexp : ((‖mpvState (blockSum Aj ι fun _ => 1) N‖ ^ 2 - b : ℝ) : ℂ) =
      ∑ j, ((‖mpvState (Aj j) N‖ ^ 2 - 1 : ℝ) : ℂ) +
        ∑ j, ∑ k ∈ Finset.univ.erase j, mpvOverlap (Aj j) (Aj k) N := by
    rw [Complex.ofReal_sub, hsum]
    simp_rw [Complex.ofReal_sub, ofReal_norm_mpvState_sq, Complex.ofReal_one]
    have hsplit : ∑ j, ∑ k, mpvOverlap (Aj j) (Aj k) N =
        ∑ j, mpvOverlap (Aj j) (Aj j) N +
          ∑ j, ∑ k ∈ Finset.univ.erase j, mpvOverlap (Aj j) (Aj k) N := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [hsplit, Finset.sum_sub_distrib]
    simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hexp, add_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hc j N
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j Finset.univ)
        fun k _ _ => mul_nonneg (hKo j k) (pow_nonneg hx0 N)))
    exact hob j k (Ne.symm (Finset.ne_of_mem_erase hk)) N

/-! ### The overlap after the partial isometry -/

/-- **The error through the overlaps of the blocks.** For blocks placed with orthogonal ranges and
states `σ_j ≥ 0` of trace one, the error of the approximating state of arXiv:2307.01696,
Supplemental Material, eq. (S7), for the direct sum with unit weights, with `βⱼ = 1` and the pairs
of the `σ_j` embedded along `ι_j`, satisfies `ε ≤ 1 - |∑ⱼ zⱼ| / (√b ‖φ_N‖)`, where
`zⱼ = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` and `N = Mq`. The unnormalized overlap after `V^{⊗M}` is
`b^{-1/2} ∑ⱼ zⱼ` (`sum_star_nonNormalApproxVector_mul_mpv`), and `V^{⊗M}` does not increase norms,
so normalizing the approximating state can only increase the overlap. -/
theorem one_sub_norm_nonNormalApproxOverlap_blockSum_le [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (q M : ℕ) [NeZero M] :
    1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
        (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
      1 - ‖mpvState (blockSum Aj ι fun _ => 1) (M * q)‖⁻¹ *
        (‖∑ j, mpvOverlap (polarPosTensor (blockTensor (blockSum Aj ι fun _ => 1) q))
          (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M‖ / Real.sqrt b) := by
  set A := blockSum Aj ι fun _ => 1
  set ω : Fin b → Fin D × Fin D → ℂ := fun j => embedPair (ι j) (fixedPointPair (σ j))
  set α : Fin b → ℂ := ghzAmplitude fun _ => 1
  set σ' : Fin b → Matrix (Fin D) (Fin D) ℂ := fun j => embeddedBlockState (ι j) (σ j)
  have hω : ω = fun j => fixedPointPair (σ' j) :=
    funext fun j => embedPair_fixedPointPair (hι j) (hσ j)
  set v := nonNormalApproxVector A q M α ω
  set z : Fin b → ℂ := fun j =>
    mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor (σ' j)) M
  have hbb : ∑ _l : Fin b, ‖(1 : ℂ)‖ ^ 2 = b := by simp
  have hnum : ∑ τ, star (v τ) * mpv A (blockedConfigEquiv d M q τ) =
      ((Real.sqrt b : ℝ) : ℂ)⁻¹ * ∑ j, z j := by
    simp only [v, hω]
    rw [sum_star_nonNormalApproxVector_mul_mpv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [α, ghzAmplitude, hbb, Complex.star_def, one_div, map_inv₀, Complex.conj_ofReal]
    rfl
  -- The approximating vector has norm at most one.
  have hvle : ∑ τ, ‖v τ‖ ^ 2 ≤ 1 := by
    have hidem := Matrix.conjTranspose_polarIso_mul_polarIso
      (physicalMatrix (blockTensor A q))
    have h := sum_norm_sq_tensorPower_mulVec_le (M := M)
      (W := Matrix.polarIso (physicalMatrix (blockTensor A q)))
      (by rw [hidem, Matrix.polarSupport_mul_polarSupport])
      (nonNormalFixedPointState α ω)
    have horth : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0 := by
      intro j j'
      split_ifs with h'
      · subst h'
        simp only [ω]
        rw [inner_embedPair_self (hι j), fixedPointPair_norm_sq (hσ j), htr j]
      · exact inner_embedPair_eq_zero_of_disjoint (hdisj j j' h') _ _
    have hβ : (fun _ : Fin b => (1 : ℂ)) ≠ 0 := fun h' => one_ne_zero (congrFun h' 0)
    have hΩ := nonNormalFixedPointState_norm_sq (NeZero.ne M) hβ horth
    rw [← ofReal_sum_norm_sq, ← Complex.ofReal_one] at hΩ
    exact h.trans (Complex.ofReal_injective hΩ).le
  -- The overlap is at least `|num| / ‖φ_N‖`.
  set num := ∑ τ, star (v τ) * mpv A (blockedConfigEquiv d M q τ)
  set t := ‖mpvState A (M * q)‖
  have hov : t⁻¹ * ‖num‖ ≤ ‖nonNormalApproxOverlap A q M α ω‖ := by
    rw [nonNormalApproxOverlap_eq]
    change t⁻¹ * ‖num‖ ≤ ‖((Real.sqrt (∑ τ, ‖v τ‖ ^ 2) : ℂ)⁻¹ * (t : ℂ)⁻¹) * num‖
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (norm_nonneg _)]
    rcases (Real.sqrt_nonneg (∑ τ, ‖v τ‖ ^ 2)).lt_or_eq with hpos' | hzero
    · have hle : Real.sqrt (∑ τ, ‖v τ‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hvle
      have h1 : 1 ≤ (Real.sqrt (∑ τ, ‖v τ‖ ^ 2))⁻¹ := one_le_inv₀ hpos' |>.2 hle
      have h2 : 0 ≤ t⁻¹ * ‖num‖ := by positivity
      nlinarith
    · have hv0 : ∀ τ, v τ = 0 := by
        have hsum : ∑ τ, ‖v τ‖ ^ 2 = 0 := by
          have := Real.sqrt_eq_zero'.1 hzero.symm
          linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sq_nonneg ‖v τ‖]
        intro τ
        have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => sq_nonneg ‖v τ‖).1 hsum τ
          (Finset.mem_univ τ)
        simpa using this
      have : num = 0 := Finset.sum_eq_zero fun τ _ => by rw [hv0 τ, star_zero, zero_mul]
      rw [this, norm_zero, mul_zero]
      positivity
  have hnum' : ‖num‖ = ‖∑ j, z j‖ / Real.sqrt b := by
    rw [hnum, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_eq_inv_mul]
  rw [← hnum']
  linarith

/-! ### One block of sites -/

/-- The one-site fixed-point states `φ_N(P'_{j,∞})` of blocks placed with orthogonal ranges are
orthonormal: `⟨φ_N(P'_{k,∞})|φ_N(P'_{l,∞})⟩ = δ_{kl}` for `N ≥ 1`. -/
theorem mpvOverlap_fixedPointTensor_embeddedBlockState (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (k l : Fin b) (N : ℕ) [NeZero N] :
    mpvOverlap (fixedPointTensor (embeddedBlockState (ι l) (σ l)))
        (fixedPointTensor (embeddedBlockState (ι k) (σ k))) N = if k = l then 1 else 0 := by
  have horth : ∑ p, star (fixedPointPair (embeddedBlockState (ι k) (σ k)) p) *
      fixedPointPair (embeddedBlockState (ι l) (σ l)) p = if k = l then 1 else 0 := by
    rw [← embedPair_fixedPointPair (hι k) (hσ k), ← embedPair_fixedPointPair (hι l) (hσ l)]
    split_ifs with h
    · subst h
      rw [inner_embedPair_self (hι k), fixedPointPair_norm_sq (hσ k), htr k]
    · exact inner_embedPair_eq_zero_of_disjoint (hdisj k l h) _ _
  have h : mpvOverlap (fixedPointTensor (embeddedBlockState (ι l) (σ l)))
      (fixedPointTensor (embeddedBlockState (ι k) (σ k))) N =
        (∑ p, star (fixedPointPair (embeddedBlockState (ι k) (σ k)) p) *
          fixedPointPair (embeddedBlockState (ι l) (σ l)) p) ^ N := by
    simp only [mpvOverlap, mpv_fixedPointTensor]
    rw [← pairProductState_inner]
    refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun τ => ?_
    rw [mul_comm]
    rfl
  rw [h, horth]
  split_ifs <;> simp [NeZero.ne N]

open scoped Matrix.Norms.L2Operator in
/-- **One block of sites, to second order.** In the setting of
`exists_norm_polarPos_blockTensor_blockSum_sub_le`, with `λ₂ ≠ 0`, `0 < γ < 1` and
`x = e^{-γ/ξ}`, there is `K ≥ 0` with `‖φ_q‖² - |∑ⱼ zⱼ|²/b ≤ K x^{2q}` for `q ≥ 1`, where
`zⱼ = ⟨φ_1(P'_{j,∞})|φ_1(P)⟩` and `φ_q` is the periodic state of the direct sum with unit weights
on `q` sites. With `u = φ_1(P)` and `W = ∑ⱼ φ_1(P'_{j,∞})`, `‖u‖ = ‖φ_q‖`, `∑ⱼ zⱼ = ⟨W|u⟩` and
`‖W‖² = b` (`mpvOverlap_fixedPointTensor_embeddedBlockState`), so the left side is at most
`‖u - W‖²` (`norm_sq_sub_norm_inner_sq_div_le`). The limit `φ_1(P_∞)` equals `W`: its overlaps
with the `φ_1(P'_{j,∞})` are the traces of the idempotents `R_j`, and its squared norm is the
limit `b` of `‖φ_q‖²`. Hence `‖u - W‖ = O(‖P - P_∞‖) = O(x^q)`. -/
theorem exists_norm_mpvState_sq_sub_norm_sum_mpvOverlap_sq_le [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1) (h0 : lam₂ ≠ 0)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ, q ≠ 0 →
      ‖mpvState (blockSum Aj ι fun _ => 1) q‖ ^ 2 -
          ‖∑ j, mpvOverlap (polarPosTensor (blockTensor (blockSum Aj ι fun _ => 1) q))
            (fixedPointTensor (embeddedBlockState (ι j) (σ j))) 1‖ ^ 2 / b ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q := by
  have : NeZero D := ⟨fun h => by
    subst h; exact (ι 0 ⟨0, (Matrix.neZero_of_trace_eq_one (htr 0)).pos⟩).elim0⟩
  have hσs : ∀ k, (σ k).PosSemidef := fun k => (hσ k).posSemidef
  set A := blockSum Aj ι fun _ => 1
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    rw [hxdef, neg_div_correlationLength, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg hγ0 (Real.log_neg (norm_pos_iff.2 h0) hl)
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_blockSum_sub_le hι hdisj hN hA hσ
    htr hfix hl hlam hmix hγ0 hγ
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one hι hdisj hN hA
    hσ htr hfix hl hlam hmix hγ0 hγ
  set μL := (mpvStateOneLM (n := D * D) (D := D)) ∘ₗ ofPhysicalMatrixLM
  set Kμ := ‖LinearMap.toContinuousLinearMap μL‖
  have hμL : ∀ G, ‖μL G‖ ≤ Kμ * ‖G‖ := (LinearMap.toContinuousLinearMap μL).le_opNorm
  set Pinf := blockSumPosLimit ι σ
  set w : Fin b → MPVSpace (D * D) 1 := fun k =>
    mpvState (fixedPointTensor (embeddedBlockState (ι k) (σ k))) 1
  set W := ∑ k, w k
  have hinner : ∀ (X : MPSTensor (D * D) D) (k : Fin b),
      ⟪w k, mpvState X 1⟫_ℂ = mpvOverlap X (fixedPointTensor (embeddedBlockState (ι k) (σ k))) 1 :=
    fun X k => by rw [mpvOverlap_eq_star_mpvInner, mpvInner]; exact (inner_conj_symm _ _).symm
  have hW2 : ‖W‖ ^ 2 = b := by
    have h : ⟪W, W⟫_ℂ = b := by
      have hww : ∀ k l, ⟪w k, w l⟫_ℂ = if k = l then 1 else 0 := fun k l =>
        (hinner _ k).trans (mpvOverlap_fixedPointTensor_embeddedBlockState hι hdisj hσs htr k l 1)
      simp only [W, sum_inner, inner_sum, hww]
      simp
    rw [inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖W‖ ^ 2 : ℝ) : ℂ) = ((b : ℝ) : ℂ) := by push_cast; exact h
    exact Complex.ofReal_injective h'
  -- The limit `φ_1(P_∞)` is `W`.
  have hWv : ⟪W, μL Pinf⟫_ℂ = b := by
    simp only [W, sum_inner]
    have h1 : ∀ k, ⟪w k, μL Pinf⟫_ℂ = 1 := fun k => by
      change ⟪w k, mpvState (ofPhysicalMatrixLM Pinf) 1⟫_ℂ = 1
      rw [hinner, ← trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap, pow_one]
      exact (isIdempotentElem_mixedTransferMatrixLeft_blockSumPosLimit hι hdisj hσs htr k).2
    simp [h1]
  have hu : ∀ q : ℕ, ‖μL (Matrix.polarPos (physicalMatrix (blockTensor A q)))‖ =
      ‖mpvState A q‖ := fun q => by
    change ‖mpvState (polarPosTensor (blockTensor A q)) 1‖ = _
    rw [norm_mpvState_polarPosTensor_blockTensor, mul_one]
  have hvn : ‖μL Pinf‖ = Real.sqrt b := by
    refine norm_eq_of_forall_abs_norm_sub_le_pow (K := Kμ * K₁) (K' := Kn)
      (u := fun q => μL (Matrix.polarPos (physicalMatrix (blockTensor A q)))) hx0 hx1
      (fun q hq => ?_) (fun q hq => ?_)
    · rw [hu q]
      have hb1 : (1 : ℝ) ≤ Real.sqrt b := Real.one_le_sqrt.2 (by exact_mod_cast NeZero.one_le)
      have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by positivity)
      have h := hnorm q hq
      rw [← hsq] at h
      refine le_trans ?_ h
      rw [show ‖mpvState A q‖ ^ 2 - Real.sqrt b ^ 2 =
        (‖mpvState A q‖ - Real.sqrt b) * (‖mpvState A q‖ + Real.sqrt b) by ring, abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg _) (by
        rw [abs_of_nonneg (by positivity)]; linarith [norm_nonneg (mpvState A q)])
    · rw [← map_sub, mul_assoc]
      exact (hμL _).trans (mul_le_mul_of_nonneg_left (hpos q hq) (norm_nonneg _))
  have hvW : μL Pinf = W := by
    have h := @norm_sub_sq ℂ _ _ _ _ (μL Pinf) W
    have hre : RCLike.re ((starRingEnd ℂ) (b : ℂ)) = b := by simp
    rw [hvn, hW2, ← inner_conj_symm, hWv, hre, Real.sq_sqrt (by positivity)] at h
    exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (μL Pinf - W)]))
  -- Conclusion.
  refine ⟨(Kμ * K₁) ^ 2, by positivity, fun q hq => ?_⟩
  set H := Matrix.polarPos (physicalMatrix (blockTensor A q))
  have hsum : ∑ j, mpvOverlap (polarPosTensor (blockTensor A q))
      (fixedPointTensor (embeddedBlockState (ι j) (σ j))) 1 = ⟪W, μL H⟫_ℂ := by
    simp only [W, sum_inner]
    exact Finset.sum_congr rfl fun k _ => (hinner _ k).symm
  have hdist : ‖μL H - W‖ ≤ Kμ * K₁ * x ^ q := by
    rw [← hvW, ← map_sub, mul_assoc]
    exact (hμL _).trans (mul_le_mul_of_nonneg_left (hpos q hq) (norm_nonneg _))
  have h := norm_sq_sub_norm_inner_sq_div_le (u := μL H)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)) hW2
  rw [hu q, ← hsum] at h
  refine h.trans ?_
  calc ‖μL H - W‖ ^ 2 ≤ (Kμ * K₁ * x ^ q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    _ = (Kμ * K₁) ^ 2 * (x ^ 2) ^ q := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]

/-! ### The approximation error -/

/-- **Approximation error for blocks with overlapping states, at the second-order rate**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), with the rate of the module
docstring). Let `Aⁱ = ⊕ⱼ A_jⁱ` be the direct sum with unit weights of blocks placed on the bond
coordinates `ι_j`, let every block `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`,
`E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the moduli of the
eigenvalues other than `1` of every transfer map `E_{A_j}` and the moduli of all eigenvalues of the
mixed transfer maps `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of distinct blocks, so that `ξ = -1/log|λ₂|`
bounds `ξ_diag` and `ξ_off-diag`, and let `0 < γ < 1`. There is `C > 0` such that for every block
length `q` and every number of blocks `M ≥ 1`, with `N = qM`, `βⱼ = 1`, the pairs of the `σ_j`
embedded along `ι_j`, and `y = M e^{-2γ q/ξ}` (`= (N/q) e^{-2γ q/ξ}` for `q ≥ 1`), the error
`ε = 1 - |⟨φ~_N|φ_N⟩|` of the approximating state of eq. (S7) satisfies `ε ≤ C y e^{C y}`.

Project result. It improves `exists_approximationError_le_overlappingBlockSum`, at the rate
`e^{-γ q/ξ}` with `γ < 1/2`, to the rate `e^{-2γ q/ξ}` with `γ < 1`, the rate of the normal case
`exists_approximationError_le`. For the blocks `A_1 = (1, 0)` and `A_2 = (3/5, 4/5)` the error is
at least `(9/25)^q / 16` for `M ≥ 3`
(`le_one_sub_norm_nonNormalApproxOverlap_overlappingBlockTensor`), and `λ₂ = 3/5` is admissible, so
the exponent `2γ q/ξ` cannot be replaced by any `c q/ξ` with `c > 2`. -/
theorem exists_approximationError_le_overlappingBlockSum_sq [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂))) := by
  have hσs : ∀ k, (σ k).PosSemidef := fun k => (hσ k).posSemidef
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : ∀ q : ℕ, Real.exp (-(2 * γ) * q / correlationLength lam₂) = (x ^ 2) ^ q :=
    fun q => by rw [Real.exp_neg_mul_div_eq_pow, exp_neg_two_mul_div_correlationLength]
  simp_rw [hxq]
  set ov : ℕ → ∀ (M : ℕ), ℝ := fun q M =>
    ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
      (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ with hovdef
  -- The trivial bound `ε ≤ 1`, which suffices whenever `C y ≥ 1`.
  have htriv : ∀ C : ℝ, 0 ≤ C → ∀ q M : ℕ, 1 ≤ C * (M * (x ^ 2) ^ q) →
      1 - ov q M ≤ C * (M * (x ^ 2) ^ q) * Real.exp (C * (M * (x ^ 2) ^ q)) :=
    fun C hC q M hu => by
      have h2 : 1 ≤ Real.exp (C * (M * (x ^ 2) ^ q)) := Real.one_le_exp (by linarith)
      have h3 : 0 ≤ ov q M := norm_nonneg _
      nlinarith
  rcases le_or_gt 1 x with hx1 | hx1
  · refine ⟨1, one_pos, fun q M _ => htriv 1 zero_le_one q M ?_⟩
    have h1 : 1 ≤ (x ^ 2) ^ q := one_le_pow₀ (one_le_pow₀ hx1)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith
  have hlog : Real.log ‖lam₂‖ < 0 := by
    have h := hx1
    rw [hxdef, neg_div_correlationLength, Real.exp_lt_one_iff] at h
    exact neg_of_mul_neg_right h hγ0.le
  have h0 : lam₂ ≠ 0 := by rintro rfl; simp at hlog
  have hl : ‖lam₂‖ < 1 := by
    by_contra h
    exact absurd (Real.log_nonneg (not_lt.1 h)) (not_le.2 hlog)
  choose Cz hCz hz using fun j =>
    exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le_sq hι hdisj hN hA hσ htr hfix hl
      hlam hmix hγ0 hγ j
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_mpvState_blockSum_sq_sub_le_of_lt_one hι hdisj hN hA
    hσ htr hfix hl hlam hmix hγ0 hγ
  obtain ⟨K₁, hK₁, hone⟩ := exists_norm_mpvState_sq_sub_norm_sum_mpvOverlap_sq_le hι hdisj hN hA
    hσ htr hfix hl h0 hlam hmix hγ0 hγ
  set S := ∑ j, Cz j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => (hCz j).le
  have hCzS : ∀ j, Cz j ≤ S := fun j =>
    Finset.single_le_sum (f := Cz) (fun j _ => (hCz j).le) (Finset.mem_univ j)
  set C := 1 + 4 * Kn ^ 2 + 2 * Kn + 2 * K₁ + 4 * S with hCdef
  have hKn2' : 0 ≤ Kn ^ 2 := sq_nonneg Kn
  have hC1 : 1 ≤ C := by linarith
  refine ⟨C, by linarith, fun q M _ => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set y := (M : ℝ) * (x ^ 2) ^ q with hydef
  have hy0 : 0 ≤ y := by positivity
  rcases le_or_gt 1 (C * y) with hCy | hCy
  · exact htriv C (by linarith) q M hCy
  rcases Nat.eq_zero_or_pos q with hq | hq
  · exact htriv C (by linarith) q M (by subst hq; simp only [pow_zero, mul_one]; nlinarith)
  have hq0 : q ≠ 0 := hq.ne'
  have hexp : 1 ≤ Real.exp (C * y) := Real.one_le_exp (by positivity)
  set A := blockSum Aj ι fun _ => 1
  set zs := ∑ j, mpvOverlap (polarPosTensor (blockTensor A q))
    (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M
  set t := ‖mpvState A (M * q)‖
  set s := ‖zs‖ / Real.sqrt b
  have hmain := one_sub_norm_nonNormalApproxOverlap_blockSum_le (Aj := Aj) hι hdisj hσs htr q M
  change 1 - ov q M ≤ 1 - t⁻¹ * s at hmain
  have hts : 1 - t⁻¹ * s = 1 - s / t := by rw [inv_mul_eq_div]
  rw [hts] at hmain
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast NeZero.one_le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = ‖zs‖ ^ 2 / b := by simp only [s]; rw [div_pow, hsb]
  -- `C y < 1` gives the smallness conditions.
  have hKn2 : 4 * Kn ^ 2 * y < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by linarith) hy0) hCy
  have hKny : 2 * Kn * y < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by linarith) hy0) hCy
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · -- One block of sites.
    obtain rfl : M = 1 := by have := NeZero.ne M; omega
    have hy1 : y = (x ^ 2) ^ q := by rw [hydef, Nat.cast_one, one_mul]
    have htq : t = ‖mpvState A q‖ := by
      change ‖mpvState A (1 * q)‖ = _
      rw [one_mul]
    have hX := hone q hq0
    rw [← htq, ← hy1, ← hs2] at hX
    have hxq' : Kn * x ^ q ≤ 1 / 2 := by
      have h5 : (Kn * x ^ q) ^ 2 < (1 / 2) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm q 2, pow_mul, ← hy1]; linarith
      exact ((pow_lt_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 h5).le
    have ht2 : 1 / 2 ≤ t ^ 2 := by
      have h := hnorm q hq0
      rw [← htq] at h
      linarith [(abs_le.1 h).1]
    have h := one_sub_div_le_two_mul_of_sq_sub_sq_le (by positivity) (norm_nonneg _) ht2
      (by positivity) hX
    calc 1 - ov q 1 ≤ 2 * (K₁ * y) := hmain.trans h
      _ = (2 * K₁) * y := by ring
      _ ≤ C * y := mul_le_mul_of_nonneg_right (by linarith) hy0
      _ ≤ C * y * Real.exp (C * y) := le_mul_of_one_le_right (by positivity) hexp
  · -- At least two blocks of sites.
    have hxN : x ^ (M * q) ≤ y := by
      calc x ^ (M * q) ≤ x ^ (2 * q) := pow_le_pow_of_le_one hx0.le hx1.le (by nlinarith)
        _ = (x ^ 2) ^ q := by rw [pow_mul]
        _ ≤ y := le_mul_of_one_le_left (by positivity) hM
    have hN0 : M * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq0
    have hnt := abs_le.1 ((hnorm (M * q) hN0).trans (mul_le_mul_of_nonneg_left hxN hKn))
    have ht2 : 1 / 2 ≤ t ^ 2 := by linarith [hnt.1]
    -- The overlaps of the blocks.
    have hzj : ∀ j, ‖mpvOverlap (polarPosTensor (blockTensor A q))
        (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M - 1‖ ≤
          Cz j * y * Real.exp (C * y) := fun j => by
      have hsmall : Cz j * y < 1 := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right ((hCzS j).trans (by linarith)) hy0) hCy
      refine (hz j q M hq0 hM2 hsmall).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
        ((hCzS j).trans (by linarith)) hy0)) (by positivity [hCz j])
    set δz := S * y * Real.exp (C * y)
    have hδz0 : 0 ≤ δz := by positivity
    have hzs : ‖zs - b‖ ≤ δz := by
      have e : zs - b = ∑ j, (mpvOverlap (polarPosTensor (blockTensor A q))
          (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M - 1) := by
        simp [zs, Finset.sum_sub_distrib]
      rw [e]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => hzj j).trans_eq ?_)
      simp only [δz, S, Finset.sum_mul]
    have hs2' : b - 2 * δz ≤ s ^ 2 := by
      rw [hs2]
      have h1 : (b : ℝ) - δz ≤ ‖zs‖ := by
        have := norm_sub_norm_le (b : ℂ) zs
        rw [norm_sub_rev, Complex.norm_natCast] at this
        linarith
      rcases le_or_gt ((b : ℝ) - δz) 0 with h2 | h2
      · have : 0 ≤ ‖zs‖ ^ 2 / b := by positivity
        linarith
      · rw [le_div_iff₀ (by positivity)]
        have h3 := pow_le_pow_left₀ h2.le h1 2
        have h4 : ((b : ℝ) - δz) ^ 2 - ((b : ℝ) - 2 * δz) * b = δz ^ 2 := by ring
        nlinarith [sq_nonneg δz]
    have hX : t ^ 2 - s ^ 2 ≤ Kn * y + 2 * δz := by linarith [hnt.2]
    have h := one_sub_div_le_two_mul_of_sq_sub_sq_le (by positivity) (norm_nonneg _) ht2
      (by positivity) hX
    calc 1 - ov q M ≤ 2 * (Kn * y + 2 * δz) := hmain.trans h
      _ = 2 * Kn * y + 4 * S * y * Real.exp (C * y) := by simp only [δz]; ring
      _ ≤ 2 * Kn * y * Real.exp (C * y) + 4 * S * y * Real.exp (C * y) := by
          have := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * Kn * y by positivity)
          linarith
      _ = (2 * Kn + 4 * S) * y * Real.exp (C * y) := by ring
      _ ≤ C * y * Real.exp (C * y) := by
          gcongr; linarith

/-- **Approximation error for blocks with overlapping states at the second-order rate, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), with the rate of the module
docstring): in the setting of `exists_approximationError_le_overlappingBlockSum_sq`, there is `C`
with `ε ≤ C (N/q) e^{-2γ q/ξ}` for every block length `q` and every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_overlappingBlockSum_sq [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum_sq hι hdisj hN hA hσ htr
    hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M
    (ghzAmplitude fun _ => 1) (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

end MPSTensor
