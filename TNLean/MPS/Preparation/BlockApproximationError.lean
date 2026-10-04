/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrderedBlockOverlap
import TNLean.MPS.Preparation.BlockIsometryState

/-!
# The approximation error for blocks of unequal lengths

Let `A` be normal and left canonical, with a positive definite normalized fixed point as in
arXiv:2307.01696, eq. (5). Cut the ring into `M ≥ 1` blocks of lengths at least `q`, with
injective blocked tensors. The approximating state `(⊗ₖ V_k) ⊗ₖ |ω⟩` has normalized overlap
error at most `C M exp(-2γq/ξ)` for every `0 < γ < 1`.

This quadratic rate is a project improvement of the source's first-order bound in
Supplemental Material, Lemma 1'(i), `eq:fid_err_gen_normal`. For at least two blocks, the overlap
is the trace of an ordered product of mixed transfer matrices, and the compressed
perturbation of each factor cancels to first order. For a single block, the normalized
squared-distance estimate is used instead. The older absolute complex trace estimate remains
valid for all positive numbers of blocks at its first-order rate.

## Main declarations

* `MPSTensor.exists_norm_trace_prod_transferMatrix_sub_one_le` — the overlap estimate (S29) of
  arXiv:2103.13367 for blocks of unequal lengths.
* `MPSTensor.exists_blockApproximationError_le_mul` — the approximation error.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive parts with the fixed point, blocks of unequal lengths.** In the
setting of `exists_norm_mpvOverlap_polarPosTensor_sub_one_le`, and with `|λ₂| ≤ 1`, there is
`C > 0` such that for every family of block lengths `ℓ : Fin M → ℕ`, `M ≥ 1`, all at least `q`,
the trace of the ordered product of the mixed transfer matrices `τ_k` of the positive parts
`P_{ℓ k}` against `P_∞` satisfies `|Tr(τ_0 ⋯ τ_{M-1}) - 1| ≤ C y e^{C y}` with
`y = M e^{-γ q/ξ}`.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished`, applied to a product of different mixed transfer matrices, each within
`O(e^{-γ q/ξ})` of the idempotent `τ_BB`; the estimate itself is
`exists_norm_trace_prod_range_transferMatrix_sub_one_le`. The hypothesis `|λ₂| ≤ 1` makes
`e^{-γ ℓ/ξ} ≤ e^{-γ q/ξ}` for `ℓ ≥ q`. -/
theorem exists_norm_trace_prod_transferMatrix_sub_one_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hlam₁ : ‖lam₂‖ ≤ 1) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) (q : ℕ), (∀ k, q ≤ ℓ k) →
      ‖Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
          (polarPosTensor (blockTensor A (ℓ k))) (fixedPointTensor σ))).prod - 1‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨K, C, hK, hC, hδL, h⟩ :=
    exists_norm_trace_prod_range_transferMatrix_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C, hC, fun M _ ℓ q hq => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hlam₁
  set Tinf := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
  set T : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun L =>
    transferMatrix (Kraus.mixedMapLM (polarPosTensor (blockTensor A L)) (fixedPointTensor σ))
  -- Pad the `M` factors with `τ_∞`, which does not enter the product of the first `M`.
  set X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    if h : j < M then T (ℓ ⟨j, h⟩) else Tinf
  have hδ : ∀ j, ‖X j - Tinf‖ ≤ K * x ^ q := fun j => by
    simp only [X]
    split_ifs with h
    · exact (hδL _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (hq _)) hK)
    · rw [sub_self, norm_zero]; positivity
  have hprod : (List.ofFn fun k => T (ℓ k)) = (List.range M).map X := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < M := by simpa using h1
    simp [X, hi]
  rw [hprod]
  exact h q M X hδ

/-- The unequal-block preparation error satisfies `C M exp(-2γq/ξ)` for every `0 < γ < 1`.
The tensor is normal and left canonical, with a positive definite normalized fixed point;
each block has length at least `q` and its blocked tensor is injective.

This is a project improvement of arXiv:2307.01696, Supplemental Material, Lemma 1'(i),
`eq:fid_err_gen_normal`. For `M ≥ 2`, the ordered mixed-transfer product is estimated to
second order and the target normalization uses `N ≥ 2q`. For one block, the squared-distance
estimate supplies the same rate after normalization. The first-order absolute trace bound
remains a separate statement and is not asserted to have this rate for a single factor. -/
theorem exists_blockApproximationError_le_mul (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hlam₁ : ‖lam₂‖ ≤ 1) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} (hN : ∑ k, ℓ k = N)
      (q : ℕ), (∀ k, q ≤ ℓ k) → (∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) →
        1 - ‖⟪blockIsometryState A (fixedPointPair σ) hN, normalizedMPVState A N⟫_ℂ‖ ≤
          C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨C₁, hC₁, hover⟩ :=
    exists_norm_trace_prod_transferMatrix_sub_one_le_sq A hN hA hσ htr hfix hlam hlam₁ hγ0 hγ
  obtain ⟨K₁, hK₁, hone⟩ :=
    exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₅, hK₅, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix hlam
    (γ := γ) hγ0 hγ
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hlam₁
  set C := 1 + 4 * K₅ ^ 2 + 2 * K₅ + 2 * K₁ + 4 * C₁
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hCa : 4 * K₅ ^ 2 ≤ C := by dsimp only [C]; linarith
  have hCb : 2 * K₁ ≤ C := by dsimp only [C]; nlinarith [sq_nonneg K₅]
  have hCc : C₁ ≤ C := by dsimp only [C]; nlinarith [sq_nonneg K₅]
  have hCd : 2 * K₅ + 4 * C₁ ≤ C := by dsimp only [C]; nlinarith [sq_nonneg K₅]
  have hC1 : 1 ≤ C := by dsimp only [C]; nlinarith [sq_nonneg K₅]
  have hCexp : C ≤ C * Real.exp C + 1 := by
    have := le_mul_of_one_le_right hCpos.le (Real.one_le_exp hCpos.le)
    linarith only [this]
  refine ⟨C * Real.exp C + 1, by positivity, fun M _ ℓ N hN q hq hinj => ?_⟩
  have hxq : Real.exp (-(2 * γ) * q / correlationLength lam₂) = (x ^ 2) ^ q := by
    rw [Real.exp_neg_mul_div_eq_pow, exp_neg_two_mul_div_correlationLength]
  rw [hxq]
  set u := (M : ℝ) * (x ^ 2) ^ q
  have hu0 : 0 ≤ u := by positivity
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set ψ := blockIsometryState A (fixedPointPair σ) hN
  have hψ : ‖ψ‖ = 1 := norm_blockIsometryState A
    (by rw [fixedPointPair_norm_sq hσ.posSemidef, htr]) hN hinj
  have hz := inner_blockIsometryState_mpvState A σ hN hinj
  have hε1 : 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ 1 := by
    linarith only [norm_nonneg ⟪ψ, normalizedMPVState A N⟫_ℂ]
  by_cases hsmall : C * u < 1
  swap
  · have hbig : 1 ≤ C * u := le_of_not_gt hsmall
    exact hε1.trans (hbig.trans (mul_le_mul_of_nonneg_right hCexp hu0))
  have hMN : M * q ≤ N := by
    calc M * q = ∑ _ : Fin M, q := by simp
      _ ≤ ∑ k, ℓ k := Finset.sum_le_sum fun k _ => hq k
      _ = N := hN
  have hqN : q ≤ N := by
    exact (Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero (NeZero.ne M))).trans hMN
  set δ := x ^ q
  have hδ2 : (x ^ 2) ^ q = δ ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hδu : δ ^ 2 ≤ u := by
    rw [← hδ2]
    exact le_mul_of_one_le_left (by positivity) hM
  have hK5 : K₅ * δ ≤ 1 / 2 := by
    have h4 : 4 * K₅ ^ 2 * u < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCa hu0) hsmall
    have h5 : K₅ ^ 2 * δ ^ 2 ≤ K₅ ^ 2 * u :=
      mul_le_mul_of_nonneg_left hδu (sq_nonneg _)
    have h6 : (K₅ * δ) ^ 2 < (1 / 2) ^ 2 := by
      rw [mul_pow]
      linarith only [h4, h5]
    exact ((pow_lt_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 h6).le
  have hcn : |‖mpvState A N‖ ^ 2 - 1| ≤ K₅ * δ :=
    (hc N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hqN) hK₅)
  have hv : 1 / 2 ≤ ‖mpvState A N‖ ^ 2 := by
    linarith only [(abs_le.1 hcn).1, hK5]
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  have herr : 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ C * u * Real.exp (C * u) := by
    rcases Nat.lt_or_ge M 2 with hM2 | hM2
    · obtain rfl : M = 1 := by have := NeZero.ne M; omega
      have hℓ : ℓ 0 = N := by simpa only [Fin.sum_univ_one] using hN
      have hz1 : ⟪ψ, mpvState A N⟫_ℂ =
          mpvOverlap (polarPosTensor (blockTensor A N)) (fixedPointTensor σ) 1 := by
        rw [hz, ← trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap]
        simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
          mul_one, pow_one]
        rw [hℓ]
      have hvu : ‖mpvState A N‖ = ‖mpvState (polarPosTensor (blockTensor A N)) 1‖ := by
        rw [norm_mpvState_polarPosTensor_blockTensor, mul_one]
      have hW : ‖mpvState A N‖ ^ 2 - ‖⟪ψ, mpvState A N⟫_ℂ‖ ^ 2 ≤ K₁ * u := by
        rw [hz1, hvu]
        refine (hone N).trans (mul_le_mul_of_nonneg_left ?_ hK₁)
        simp only [u, Nat.cast_one, one_mul]
        exact pow_le_pow_of_le_one (sq_nonneg _) (pow_le_one₀ hx0 hx1) hqN
      calc 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ 2 * (K₁ * u) :=
            one_sub_norm_inner_smul_inv_norm_le_two_mul hψ.le hv hW
        _ ≤ C * u := by nlinarith only [hCb, hu0]
        _ ≤ C * u * Real.exp (C * u) := le_mul_of_one_le_right (by positivity) hexp
    have hlow := hover M ℓ q hM2 hq
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCc hu0) hsmall)
    have hcy : |‖mpvState A N‖ ^ 2 - 1| ≤ K₅ * u := by
      refine (hc N).trans (mul_le_mul_of_nonneg_left ?_ hK₅)
      calc x ^ N ≤ x ^ (2 * q) :=
            pow_le_pow_of_le_one hx0 hx1 ((Nat.mul_le_mul_right q hM2).trans hMN)
        _ = (x ^ 2) ^ q := pow_mul x 2 q
        _ ≤ u := le_mul_of_one_le_left (by positivity) hM
    set s := ‖⟪ψ, mpvState A N⟫_ℂ‖
    have hs0 : 0 ≤ s := norm_nonneg _
    set v := C₁ * u * Real.exp (C₁ * u)
    have hv0 : 0 ≤ v := by positivity
    have hgap : 1 - s ≤ v := by
      have h := norm_sub_norm_le (1 : ℂ) ⟪ψ, mpvState A N⟫_ℂ
      rw [norm_one, norm_sub_rev, hz] at h
      change 1 - ‖⟪ψ, mpvState A N⟫_ℂ‖ ≤ v
      rw [hz]
      exact h.trans hlow
    have hsq : 1 - s ^ 2 ≤ 2 * v := by
      by_cases hs1 : s ≤ 1
      · nlinarith only [hgap, hs1, hs0]
      · nlinarith only [hs1, hv0]
    have hW : ‖mpvState A N‖ ^ 2 - s ^ 2 ≤ K₅ * u + 2 * v := by
      linarith only [(abs_le.1 hcy).2, hsq]
    have hexpC : Real.exp (C₁ * u) ≤ Real.exp (C * u) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCc hu0)
    have h1 : v ≤ C₁ * u * Real.exp (C * u) :=
      mul_le_mul_of_nonneg_left hexpC (by positivity)
    have h2 : K₅ * u ≤ K₅ * u * Real.exp (C * u) :=
      le_mul_of_one_le_right (by positivity) hexp
    have h3 : (2 * K₅ + 4 * C₁) * u * Real.exp (C * u) ≤ C * u * Real.exp (C * u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd hu0) (by positivity)
    have h4 : (2 * K₅ + 4 * C₁) * u * Real.exp (C * u) =
        2 * (K₅ * u * Real.exp (C * u)) + 4 * (C₁ * u * Real.exp (C * u)) := by ring
    have herror := one_sub_norm_inner_smul_inv_norm_le_two_mul hψ.le hv hW
    change 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ 2 * (K₅ * u + 2 * v) at herror
    linarith only [herror, h1, h2, h3, h4]
  refine herr.trans ?_
  calc C * u * Real.exp (C * u) ≤ C * u * Real.exp C := by
        gcongr
        exact hsmall.le.trans hC1
    _ ≤ (C * Real.exp C + 1) * u := by nlinarith only [hu0]

end MPSTensor
