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
(`norm_prod_range_sub_pow_le_of_isIdempotentElem`).

## Main declarations

* `MPSTensor.one_sub_norm_inner_smul_inv_norm_le` — the triangle inequality of the source's
  proof of Lemma 1'(i), as a statement about vectors.
* `MPSTensor.exists_norm_trace_prod_transferMatrix_sub_one_le` — the overlap estimate (S29) of
  arXiv:2103.13367 for blocks of unequal lengths.
* `MPSTensor.exists_blockApproximationError_le_mul` — the approximation error.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- **The triangle inequality of Lemma 1'(i).** If `‖ψ‖ ≤ 1`, `|⟨ψ|v⟩ - 1| ≤ a`, and
`|‖v‖² - 1| ≤ b`, then the error `1 - |⟨ψ|v/‖v‖⟩|` against the normalization of `v` is at most
`a + b`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i):
`ε ≤ |1 - c_N |⟨φ'_N|φ_N⟩|| + |c_N - 1| |⟨φ'_N|φ_N⟩|`. -/
theorem one_sub_norm_inner_smul_inv_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ v : E} (hψ : ‖ψ‖ ≤ 1) {a b : ℝ}
    (ha : ‖⟪ψ, v⟫_ℂ - 1‖ ≤ a) (hb : |‖v‖ ^ 2 - 1| ≤ b) :
    1 - ‖⟪ψ, ((‖v‖ : ℂ)⁻¹) • v⟫_ℂ‖ ≤ a + b := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  set c := ‖v‖ with hcdef
  set z := ⟪ψ, v⟫_ℂ
  rcases eq_or_ne c 0 with hc0 | hc0
  · have : 1 ≤ b := by simpa [hc0] using hb
    linarith [norm_nonneg ⟪ψ, ((c : ℂ)⁻¹) • v⟫_ℂ]
  have hcpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc0)
  have hinner : ⟪ψ, ((c : ℂ)⁻¹) • v⟫_ℂ = (c : ℂ)⁻¹ * z := inner_smul_right _ _ _
  set w := ‖⟪ψ, ((c : ℂ)⁻¹) • v⟫_ℂ‖
  have hw1 : w ≤ 1 := by
    refine (norm_inner_le_norm (𝕜 := ℂ) ψ _).trans ?_
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
      inv_mul_cancel₀ hc0, mul_one]
    exact hψ
  have hcw : c * w = ‖z‖ := by
    simp only [w, hinner, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcpos, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hz : |1 - ‖z‖| ≤ ‖z - 1‖ := by
    calc |1 - ‖z‖| = |‖(1 : ℂ)‖ - ‖z‖| := by rw [norm_one]
      _ ≤ ‖z - 1‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
  have hc1 : |c - 1| ≤ |c ^ 2 - 1| := by
    rw [show c ^ 2 - 1 = (c - 1) * (c + 1) by ring, abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
  have e : 1 - w = (1 - ‖z‖) + (c - 1) * w := by rw [← hcw]; ring
  have : (c - 1) * w ≤ |c - 1| := by
    calc (c - 1) * w ≤ |c - 1| * w := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |c - 1| * 1 := mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
      _ = |c - 1| := mul_one _
  rw [e]
  linarith [le_abs_self (1 - ‖z‖)]

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive parts with the fixed point, blocks of unequal lengths.** In the
setting of `exists_norm_mpvOverlap_polarPosTensor_sub_one_le`, and with `|λ₂| ≤ 1`, there is
`C > 0` such that for every family of block lengths `ℓ : Fin M → ℕ`, `M ≥ 1`, all at least `q`,
the trace of the ordered product of the mixed transfer matrices `τ_k` of the positive parts
`P_{ℓ k}` against `P_∞` satisfies `|Tr(τ_0 ⋯ τ_{M-1}) - 1| ≤ C y e^{C y}` with
`y = M e^{-γ q/ξ}`.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished`, applied to a product of different mixed transfer matrices, each within
`O(e^{-γ q/ξ})` of the idempotent `τ_BB`. -/
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
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  set Ψ := mixedTransferMatrixLeft (fixedPointTensor σ)
  set K₃ := ‖LinearMap.toContinuousLinearMap Ψ‖
  have hK₃ : 0 ≤ K₃ := norm_nonneg _
  have hΨ : ∀ G, ‖Ψ G‖ ≤ K₃ * ‖G‖ := (LinearMap.toContinuousLinearMap Ψ).le_opNorm
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  set K₄ := ‖trL‖
  have hK₄ : 0 ≤ K₄ := norm_nonneg _
  have htrace : ∀ G, ‖Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ G‖ ≤ K₄ * ‖G‖ := trL.le_opNorm
  set Tinf := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
  set c := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ + ‖Tinf‖
  have hc : 0 ≤ c := by positivity
  set K := c * (K₃ * K₁)
  have hK : 0 ≤ K := by positivity
  refine ⟨K₄ * c * K + K + 1, by positivity, fun M _ ℓ q hq => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div_correlationLength]
    rcases (norm_nonneg lam₂).eq_or_lt with h | h
    · rw [← h, Real.log_zero, mul_zero]
    · exact mul_nonpos_of_nonneg_of_nonpos hγ0.le (Real.log_nonpos h.le hlam₁)
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  set T : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun L =>
    transferMatrix (Kraus.mixedMapLM (polarPosTensor (blockTensor A L)) (fixedPointTensor σ))
  -- `T L - Tinf = Ψ(P_L - P_∞)`.
  have hTΨ : ∀ L, T L - Tinf = Ψ (Matrix.polarPos (physicalMatrix (blockTensor A L)) -
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := fun L => by
    rw [map_sub]
    congr 1
    change Tinf = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
      (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix (virtualPairEquiv D) id))
      (fixedPointTensor σ))
    rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
  have hδL : ∀ L, q ≤ L → ‖T L - Tinf‖ ≤ K₃ * K₁ * x ^ q := fun L hL => by
    rw [hTΨ]
    refine (hΨ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hpos L).trans ?_) hK₃
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hL) hK₁
  set X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j =>
    if h : j < M then T (ℓ ⟨j, h⟩) else Tinf
  have hδ : ∀ j, ‖X j - Tinf‖ ≤ K₃ * K₁ * x ^ q := fun j => by
    simp only [X]
    split_ifs with h
    · exact hδL _ (hq _)
    · rw [sub_self, norm_zero]; positivity
  have hprod : (List.ofFn fun k => T (ℓ k)) = (List.range M).map X := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < M := by simpa using h1
    simp [X, hi]
  have htel := norm_prod_range_sub_pow_le_of_isIdempotentElem
    (isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr)
    (c := c) (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))
    hδ M
  -- `1 = Tr Tinf^M`.
  have hover : Matrix.trace (List.ofFn fun k => T (ℓ k)).prod - 1 =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (((List.range M).map X).prod - Tinf ^ M) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply, hprod,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      mpvOverlap_fixedPointTensor_self hσ.posSemidef htr]
  have hy : 0 ≤ c * (K₃ * K₁ * x ^ q) := by positivity
  have hgeom := one_add_pow_sub_one_le_mul_exp hy M
  calc ‖Matrix.trace (List.ofFn fun k => T (ℓ k)).prod - 1‖
      ≤ K₄ * ‖((List.range M).map X).prod - Tinf ^ M‖ := by rw [hover]; exact htrace _
    _ ≤ K₄ * (c * ((1 + c * (K₃ * K₁ * x ^ q)) ^ M - 1)) := by gcongr
    _ ≤ K₄ * (c * (M * (c * (K₃ * K₁ * x ^ q)) *
          Real.exp (M * (c * (K₃ * K₁ * x ^ q))))) := by gcongr
    _ = K₄ * c * K * u * Real.exp (K * u) := by
        simp only [u, K]; ring_nf
    _ ≤ (K₄ * c * K + K + 1) * u * Real.exp ((K₄ * c * K + K + 1) * u) := by
        have hKC : K ≤ K₄ * c * K + K + 1 := by nlinarith [mul_nonneg (mul_nonneg hK₄ hc) hK]
        have hKC' : K₄ * c * K ≤ K₄ * c * K + K + 1 := by linarith
        gcongr

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
  have hx1 : x ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div_correlationLength]
    rcases (norm_nonneg lam₂).eq_or_lt with h | h
    · rw [← h, Real.log_zero, mul_zero]
    · exact mul_nonpos_of_nonneg_of_nonpos hγ0.le (Real.log_nonpos h.le hlam₁)
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
    one_sub_norm_inner_smul_inv_norm_le hψ.le (by rw [hz]; exact hover') hcu
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
