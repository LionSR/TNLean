/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.BlockIsometryState

/-!
# The approximation error for blocks of unequal lengths

Let `A` be a normal tensor in the gauge of arXiv:2307.01696, eq. (5), and cut the ring of `N`
sites into `M ≥ 1` blocks of lengths `ℓ 0, …, ℓ (M - 1)`, each at least `q`, with injective
blocked tensors. The approximating state `|ψ⟩ = (⊗ₖ V_k) ⊗ₖ |ω⟩` of these blocks
(`MPSTensor.blockIsometryState`) has error `1 - |⟨ψ|φ_N⟩| ≤ C M e^{-γ q/ξ}`, with `C` depending
only on `A`, `σ`, `λ₂`, and `γ` (`MPSTensor.exists_blockApproximationError_le_mul`).

For blocks of equal length this is Lemma 1'(i) of the source
(`MPSTensor.exists_approximationError_le_mul`). The Supplemental Material, proof of Theorem 1,
uses the same bound for blocks "all of the same size, `q_N`, except for the last one, which may
be larger". The proof is the source's: the overlap `⟨ψ|φ_N(A)⟩` is the trace of the ordered
product of the mixed transfer matrices `τ_k` of the positive parts `P_{ℓ k}` against the fixed
point, each within `O(e^{-γ q/ξ})` of the same idempotent, and the telescoping bound of
arXiv:2103.13367, eqs. `final_eq` to `finished`, holds for a product of such matrices
(`exists_norm_trace_prod_range_transferMatrix_sub_one_le`).

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
    (hlam₁ : ‖lam₂‖ ≤ 1) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
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

/-- **Approximation error for blocks of unequal lengths.** Let `A` be normal in the gauge
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (arXiv:2307.01696, eq. (5)), let
`|λ₂| ≤ 1` bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length
`ξ = -1/log|λ₂|`, and let `0 < γ < 1/2`. There is `C > 0` such that for every cutting of a ring
of `N` sites into `M ≥ 1` blocks of lengths `ℓ k ≥ q` with injective blocked tensors, the
approximating state `|ψ⟩ = (⊗ₖ V_k) ⊗ₖ |ω⟩` has error
`1 - |⟨ψ|φ_N⟩| ≤ C M e^{-γ q/ξ}`.

arXiv:2307.01696, Lemma 1 and Lemma 1'(i), for blocks of different lengths; the Supplemental
Material, proof of Theorem 1, applies Lemma 1 to blocks "all of the same size, `q_N`, except for
the last one, which may be larger". The proof is that of `exists_approximationError_le`: the
triangle inequality `one_sub_norm_inner_smul_inv_norm_le`, with the overlap bounded by
`exists_norm_trace_prod_transferMatrix_sub_one_le` and the normalization by
`exists_abs_norm_mpvState_sq_sub_one_le`, using `N ≥ q`. -/
theorem exists_blockApproximationError_le_mul (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    (hlam₁ : ‖lam₂‖ ≤ 1) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} (hN : ∑ k, ℓ k = N)
      (q : ℕ), (∀ k, q ≤ ℓ k) → (∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) →
        1 - ‖⟪blockIsometryState A (fixedPointPair σ) hN, normalizedMPVState A N⟫_ℂ‖ ≤
          C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨C₁, hC₁, hover⟩ :=
    exists_norm_trace_prod_transferMatrix_sub_one_le A hN hA hσ htr hfix hlam hlam₁ hγ0 hγ
  obtain ⟨K₅, hK₅, hc⟩ :=
    exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  set C := C₁ + K₅
  refine ⟨C * Real.exp C + 1, by positivity, fun M _ ℓ N hN q hq hinj => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hlam₁
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hover' := hover M ℓ q hq
  rw [hxq] at hover' ⊢
  set u := (M : ℝ) * x ^ q
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hu : 0 ≤ u := by positivity
  set ψ := blockIsometryState A (fixedPointPair σ) hN
  have hψ : ‖ψ‖ = 1 := norm_blockIsometryState A
    (by rw [fixedPointPair_norm_sq hσ.posSemidef, htr]) hN hinj
  have hz := inner_blockIsometryState_mpvState A σ hN hinj
  -- `N ≥ q`, so the normalization term is dominated by `u`.
  have hqN : q ≤ N := by
    have := hq ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
    rw [← hN]
    exact this.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have hcu : |‖mpvState A N‖ ^ 2 - 1| ≤ K₅ * u := by
    refine (hc N).trans (mul_le_mul_of_nonneg_left ?_ hK₅)
    calc (x ^ 2) ^ N = x ^ (2 * N) := (pow_mul _ _ _).symm
      _ ≤ x ^ q := pow_le_pow_of_le_one hx0 hx1 (by omega)
      _ ≤ u := le_mul_of_one_le_left (by positivity) hM
  have herr : 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤
      C₁ * u * Real.exp (C₁ * u) + K₅ * u :=
    one_sub_norm_inner_smul_inv_norm_le hψ.le (by
      rw [hz]
      refine le_trans ?_ hover'
      rw [norm_sub_rev]
      simpa only [norm_one] using abs_norm_sub_norm_le (1 : ℂ) _) hcu
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  have hbound : 1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ C * u * Real.exp (C * u) := by
    have h1 : C₁ * u * Real.exp (C₁ * u) ≤ C₁ * u * Real.exp (C * u) := by
      gcongr
      simp only [C]; linarith
    have h2 : K₅ * u ≤ K₅ * u * Real.exp (C * u) := le_mul_of_one_le_right (by positivity) hexp
    have h3 : C * u * Real.exp (C * u) = C₁ * u * Real.exp (C * u) + K₅ * u * Real.exp (C * u) := by
      simp only [C]; ring
    linarith
  exact le_mul_of_le_mul_exp_of_le (by positivity) zero_le_one hu hbound
    (by linarith [norm_nonneg ⟪ψ, normalizedMPVState A N⟫_ℂ])

end MPSTensor
