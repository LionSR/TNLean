/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SecondOrderOverlap
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# The approximation error of the log-depth preparation, normal case

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), and let `λ₂` bound the moduli of the eigenvalues of `E_A` other
than `1`, with correlation length `ξ = -1/log|λ₂|`. Block `q` sites, write `B_q = V P_q` for the
polar decomposition of the blocked tensor, and let `P_∞` be the fixed-point tensor. For `N = qM`
this file proves explicit forms of

* the overlap estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367, Supplemental Material,
  "Proof of Theorem MPS_classification", eq. (S29)), quoted as eq. (S9) of arXiv:2307.01696:
  `|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| = O((N/q) e^{-γ q/ξ})` for every `0 < γ < 1`. The sources state
  it for `0 < γ < 1/2`; the range `γ < 1` is a project result;
* the approximation error `ε(φ'_N, φ_N) = 1 - |⟨φ'_N|φ_N⟩| = O((N/q) e^{-2γ q/ξ})` for every
  `0 < γ < 1`. arXiv:2307.01696, Lemma 1, eq. (17), and Lemma 1'(i), proves the rate
  `e^{-γ q/ξ}` for `0 < γ < 1/2`; the rate `e^{-2γ q/ξ}` is a project result.

Both are stated as `≤ C y e^{C y}`, with `y = (N/q) e^{-γ q/ξ}`, respectively
`y = (N/q) e^{-2γ q/ξ}`, and a constant `C` depending only on `A`, `σ`, `λ₂`, and `γ`, for all
`q` and all `M ≥ 1`. The source's iteration closes in this form, `ε_q + ε_q² (1 + ε_q/M)^{M-2}`
(arXiv:2103.13367, Supplemental Material, eq. (32)), and it gives the `O`-bound whenever `y`
stays bounded. The variants ending in `_mul` state the `O`-bound itself for all `q` and all
`M ≥ 1`. For `y > 1` it follows from `ε ≤ 1` and from the boundedness of the norms `‖φ_N(A)‖`.

## Proof outline (following arXiv:2103.13367)

1. **Transfer-map gap.** `exists_norm_transferMap_pow_sub_le` gives
   `‖E_A^n(X) - Tr(X) σ‖ ≤ C e^{-γ' n/ξ} ‖X‖` for every `0 < γ' < 1`, since `e^{-γ'/ξ}` exceeds
   the spectral radius of `E_A - |σ⟩⟨1|` (compare arXiv:2103.13367, eq. (21),
   `‖R‖_F ≤ Λ(q) e^{-qα}` with `|λ₁| = e^{-qα}` for the blocked transfer matrix). The overlap
   estimate uses it at `γ' = γ`, through the Gram matrices `P_q² = B_q† B_q`, a rearrangement of
   `E_A^q`, which are `e^{-γ q/ξ}`-close to `P_∞² = σᵀ ⊗ 1`.
2. **Positive parts.** The source bounds this step with `‖√X - √Y‖ ≤ √‖X - Y‖`
   (arXiv:2103.13367, eq. (26)), which halves the exponent. Here `P_∞²` is bounded below by a
   positive multiple of the identity, so the Lipschitz bound `‖√X - √Y‖ ≤ ‖X - Y‖ / √c` of
   `CFC.norm_sqrt_sub_sqrt_le_div` applies and keeps the exponent, as in arXiv:2606.24475,
   App. B3, eqs. (S27)–(S32). `exists_norm_polarPos_blockTensor_sub_le`, called at rate `γ`,
   gives `‖P_q - P_∞‖ ≤ K e^{-γ q/ξ}`.
3. **Telescoping.** For an idempotent `T_∞` and `‖T - T_∞‖ ≤ δ`,
   `‖T^M - T_∞^M‖ ≤ c((1 + cδ)^M - 1)` (eqs. `final_eq` to `finished`), applied with
   `δ = K e^{-γ q/ξ}` from step 2 to the mixed transfer matrices `τ_{AB}` and `τ_{BB}` of `P_q`
   against `P_∞`.
4. **Normalization.** `exists_norm_transferMatrix_pow_sub_le` calls the gap of step 1 at the
   same rate `γ`; hence `c_N² = Tr E_A^N` differs from `1` by `O(e^{-γ N/ξ})` for every
   `0 < γ < 1`. The triangle inequality of arXiv:2307.01696, proof of Lemma 1'(i), combines the
   two errors. Since `N ≥ q` the normalization term is dominated by the overlap term; no
   condition `q = o(N)` is needed.
5. **Second order.** This step is a project result. The error is at most
   `2 (‖φ_N‖² - |⟨φ'_N|φ_N⟩|²)`, which is of second order in `‖P_q - P_∞‖`. Since `τ_∞` is the
   rank-one idempotent `X ↦ Tr(X) σ`, `τ_∞ τ_q τ_∞ = α τ_∞` with `1 - |α| = O(‖P_q - P_∞‖²)`,
   and `τ_q = α (τ_∞ + Z)` with `τ_∞ Z τ_∞ = 0`. The trace of `(τ_∞ + Z)^M` is `1` up to
   `O(M ‖Z‖²)` for `M ≥ 2` (`IsIdempotentElem.norm_trace_add_pow_sub_le_of_le`). This gives the
   rate `e^{-2γ q/ξ}` for every `γ < 1`. The normalization is used at rate `γ` and
   `N = Mq ≥ 2q`, and `M = 1` is a direct estimate. For comparison, arXiv:2606.24475, App. B4,
   eq. (S52), bounds the trace linearly in the residual, which gives the rate `e^{-q/ξ}`. The
   error observed numerically decays as `e^{-γ q/ξ}` with `γ ≈ 2` (arXiv:2307.01696,
   Supplemental Material, discussion of Fig. S1; arXiv:2503.14645, eq. (4)).

## Main declarations

* `norm_pow_sub_pow_le_of_isIdempotentElem` (in `TNLean.Algebra.NormedRingTelescoping`) — the
  telescoping bound of step 3.
* Steps 1 and 2 are `MPSTensor.exists_norm_transferMap_pow_sub_le` and
  `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` in
  `TNLean.MPS.Preparation.PositivePartRate`.
* `MPSTensor.exists_norm_trace_prod_range_transferMatrix_sub_one_le` — the telescoping
  estimate for a product of mixed transfer matrices, each near the idempotent `τ_∞`.
* `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le` and its `O`-form
  `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le_mul` — the overlap estimate
  (S29) of arXiv:2103.13367.
* `MPSTensor.normalizedMPVState`, `MPSTensor.approximatingMPVState` — the normalized states
  `φ_N` and `φ'_N`.
* `MPSTensor.one_sub_norm_inner_smul_inv_norm_le` — the triangle inequality of the source's
  proof of Lemma 1'(i), as a statement about vectors.
* Step 5 is `MPSTensor.exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq` (the overlap to
  second order, for `M ≥ 2`) and `MPSTensor.exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le`
  (the case `M = 1`) in `TNLean.MPS.Preparation.SecondOrderOverlap`.
* `MPSTensor.exists_approximationError_le` and its `O`-form
  `MPSTensor.exists_approximationError_le_mul` — the approximation error, Lemma 1'(i), at rate
  `2γ/ξ`.

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  `difference`, `final_eq`, `intermediate`, `inequality`, `almost_done`, `finished`).
* arXiv:2307.01696, Lemma 1 (`lm:1`), eq. (17) (`eq:fid_err`), and Supplemental Material,
  "Proof of Lemma 1 and extension to non-normal tensors", eq. (S9) (`eq:app_error`) and
  Lemma 1'(i) (`eq:fid_err_gen_normal`); Supplemental Material, discussion of Fig. S1, for the
  numerically observed rate.
* arXiv:2606.24475, App. B3, eqs. (S27)–(S32), and App. B4, eq. (S52).
* arXiv:2503.14645, eq. (4).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Mixed transfer matrices -/

/-- The linear map `G ↦ τ_{G,B}` sending a `D² × D²` matrix `G`, read as a tensor through
`ofPhysicalMatrixLM`, to the transfer matrix of its mixed transfer map against `B`.

arXiv:2103.13367, the mixed transfer matrix `τ_{AB} = A† B` after eq. `eq:a_tensor`, read as a
function of `A`. -/
noncomputable def mixedTransferMatrixLeft (B : MPSTensor (D * D) D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  transferMatrixLM ∘ₗ mixedMapLMLeft B ∘ₗ ofPhysicalMatrixLM

open scoped Matrix.Norms.L2Operator in
/-- **Telescoping bound for products of mixed transfer matrices.** In the setting of
`exists_norm_polarPos_blockTensor_sub_le`, write `τ_L` for the mixed transfer matrix of the
positive part `P_L` of the `L`-site blocked tensor against the fixed-point tensor `P_∞`, and
`τ_∞` for that of `P_∞` against itself. There are `K ≥ 0` and `C > 0` such that
`‖τ_L - τ_∞‖ ≤ K e^{-γ L/ξ}` for every `L`, and every family of matrices `X j` with
`‖X j - τ_∞‖ ≤ K e^{-γ q/ξ}` satisfies `|Tr(X_0 ⋯ X_{M-1}) - 1| ≤ C y e^{C y}` for `M ≥ 1`,
with `y = M e^{-γ q/ξ}`.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished`: `τ_∞` is idempotent with `Tr τ_∞^M = 1`, and the telescoping estimate
bounds the distance of the product from `τ_∞^M`. -/
theorem exists_norm_trace_prod_range_transferMatrix_sub_one_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      (∀ L : ℕ, ‖transferMatrix (Kraus.mixedMapLM (polarPosTensor (blockTensor A L))
          (fixedPointTensor σ)) -
        transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))‖ ≤
          K * Real.exp (-γ / correlationLength lam₂) ^ L) ∧
      ∀ (q M : ℕ) [NeZero M] (X : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ),
        (∀ j, ‖X j -
          transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))‖ ≤
            K * Real.exp (-γ / correlationLength lam₂) ^ q) →
        ‖Matrix.trace ((List.range M).map X).prod - 1‖ ≤
          C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
            Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨K₁, hK₁, hpos⟩ :=
    exists_norm_polarPos_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
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
  refine ⟨K₃ * K₁, K₄ * c * K + K + 1, by positivity, by positivity, fun L => ?_,
    fun q M _ X hδ => ?_⟩
  · -- `τ_L - τ_∞ = Ψ(P_L - P_∞)`.
    have hTΨ : transferMatrix (Kraus.mixedMapLM (polarPosTensor (blockTensor A L))
        (fixedPointTensor σ)) - Tinf = Ψ (Matrix.polarPos (physicalMatrix (blockTensor A L)) -
          (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [map_sub]
      congr 1
      change Tinf = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
        (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix (virtualPairEquiv D) id))
        (fixedPointTensor σ))
      rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
    rw [hTΨ, mul_assoc]
    exact (hΨ _).trans (mul_le_mul_of_nonneg_left (hpos L) hK₃)
  set x := Real.exp (-γ / correlationLength lam₂)
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  have htel := norm_prod_range_sub_pow_le_of_isIdempotentElem
    (isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr)
    (c := c) (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))
    hδ M
  -- `1 = Tr τ_∞^M`.
  have hover : Matrix.trace ((List.range M).map X).prod - 1 =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (((List.range M).map X).prod - Tinf ^ M) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      mpvOverlap_fixedPointTensor_self hσ.posSemidef htr]
  have hy : 0 ≤ c * (K₃ * K₁ * x ^ q) := by positivity
  have hgeom := one_add_pow_sub_one_le_mul_exp hy M
  calc ‖Matrix.trace ((List.range M).map X).prod - 1‖
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

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive part with the fixed point, as a complex number.** In the setting of
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le`, the overlap itself, not only its modulus,
is close to `1`: `|⟨φ_M(P_∞)|φ_M(P_q)⟩ - 1| ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished`: the telescoping estimate bounds `Tr τ_{AB}^M - Tr τ_{BB}^M`, which is
this difference (`exists_norm_trace_prod_range_transferMatrix_sub_one_le` with all factors
equal). -/
theorem exists_norm_mpvOverlap_polarPosTensor_sub_one_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨K, C, -, hC, hδ, h⟩ :=
    exists_norm_trace_prod_range_transferMatrix_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C, hC, fun q M _ => ?_⟩
  have := h q M _ fun _ => hδ q
  rwa [List.map_const', List.length_range, List.prod_replicate,
    trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap]
    at this

/-- **Overlap of the positive part with the fixed point.** Let `A` be normal in the gauge
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (arXiv:2307.01696, eq. (5)), let `λ₂`
bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length `ξ`, and let
`0 < γ < 1`. Then there is `C > 0` such that for all `q` and all `M ≥ 1`, with `N = qM` and
`y = (N/q) e^{-γ q/ξ} = M e^{-γ q/ξ}`,
`|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| ≤ C y e^{C y}`, where `P_q` is the positive part of the `q`-site
blocked tensor and `P_∞` the fixed-point tensor.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished` (the estimate (S29)), quoted as arXiv:2307.01696, eq. (S9). The source
concludes `O(ε_q)` from `ε_q + ε_q² e^{ε_q}(1 + O(ε_q/M))`, which is the present bound in the
regime where `ε_q` stays bounded. The source states the estimate for `0 < γ < 1/2`; the range
`γ < 1` is a project result, since the positive parts are estimated with the Lipschitz bound of
the square root at the positive definite limit (`exists_norm_polarPos_blockTensor_sub_le`). -/
theorem exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖| ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_mpvOverlap_polarPosTensor_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C, hC, fun q M _ => ?_⟩
  calc |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖|
      = |‖(1 : ℂ)‖ - ‖mpvOverlap (polarPosTensor (blockTensor A q))
          (fixedPointTensor σ) M‖| := by rw [norm_one]
    _ ≤ ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1‖ := by
        rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
    _ ≤ _ := h q M

/-! ### The normalization `c_N` -/

open scoped Matrix.Norms.L2Operator in
/-- The transfer matrix of `E_A^n` is `e^{-γ n/ξ}`-close to that of `X ↦ Tr(X) σ`, in the
setting of `exists_norm_transferMap_pow_sub_le`. -/
theorem exists_norm_transferMatrix_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖transferMatrix (Kraus.transferMap A) ^ n -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ n := by
  obtain ⟨C, hC, hgap⟩ := exists_norm_transferMap_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K, hK, h⟩ := exists_norm_le_of_entry_eq_pow_sub (Kraus.transferMap A) σ hC.le hgap
    (fun (_ b : Fin D × Fin D) => Matrix.single b.2 b.1 (1 : ℂ))
    (fun a _ => a.2) (fun a _ => a.1)
  refine ⟨K, hK, fun n => ?_⟩
  rw [← transferMatrix_pow]
  refine h n _ fun a b => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, ← transferMap_fixedPointTensor_apply hσ.posSemidef]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Normalization.** In the setting of `exists_norm_transferMap_pow_sub_le`, the squared norm
`c_N² = Tr E_A^N` of the periodic state satisfies `|c_N² - 1| ≤ K e^{-γ N/ξ}` for every
`0 < γ < 1`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): `c_N = √(Tr E_A^N)` and
`|c_N - 1| = O(e^{-N/ξ})`. -/
theorem exists_abs_norm_mpvState_sq_sub_one_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      |‖mpvState A N‖ ^ 2 - 1| ≤ K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨K₀, hK₀, hT⟩ := exists_norm_transferMatrix_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  have htrace : ∀ G, ‖Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ G‖ ≤ ‖trL‖ * ‖G‖ := trL.le_opNorm
  have hK₄ : 0 ≤ ‖trL‖ := norm_nonneg _
  refine ⟨‖trL‖ * K₀, by positivity, fun N => ?_⟩
  have hone : Matrix.trace (transferMatrix (Kraus.transferMap (fixedPointTensor σ))) = 1 := by
    have h := trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor σ) 1
    rwa [pow_one, mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h
  have hc : (((‖mpvState A N‖ ^ 2 - 1 : ℝ)) : ℂ) =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (transferMatrix (Kraus.transferMap A) ^ N -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply, hone,
      trace_transferMatrix_transferMap_pow_eq_mpvOverlap, ← ofReal_norm_mpvState_sq]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hc, mul_assoc]
  exact (htrace _).trans (mul_le_mul_of_nonneg_left (hT N) hK₄)

/-- **A gap for a normal tensor.** For a normal left-canonical tensor `A` with `D ≥ 1` there is
`0 < t < 1` bounding the moduli of the eigenvalues other than `1` of its transfer map
(arXiv:2307.01696, eq. (5) and the remark after it: the transfer map of a normal tensor in this
gauge has `1` as its only eigenvalue of modulus `1`). -/
theorem exists_eigenvalue_norm_le_of_isNormal [NeZero D] (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 →
      ‖μ‖ ≤ t := by
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
    (Module.End.finite_hasEigenvalue (Kraus.transferMap A)) fun μ hμ hne =>
      lt_of_le_of_ne (hCh.eigenvalue_norm_le_one μ hμ)
        fun h => hne (hNT.primitive_transfer.unique_peripheral μ hμ h)
  exact ⟨max (1 - δ) (1 / 2), lt_max_of_lt_right (by norm_num),
    max_lt (by linarith) (by norm_num), fun μ hμ hne => (hgap μ hμ hne).trans (le_max_left _ _)⟩

/-- The periodic states of a normal tensor in the gauge of `exists_norm_transferMap_pow_sub_le`
have bounded norms: `c_N² = Tr E_A^N ≤ B` for all `N`. -/
theorem exists_norm_mpvState_sq_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) :
    ∃ B : ℝ, ∀ N : ℕ, ‖mpvState A N‖ ^ 2 ≤ B := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨t, ht0, ht1, hgap⟩ := exists_eigenvalue_norm_le_of_isNormal A hN hA
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => by rw [hnorm]; exact hgap μ hμ hne)
    (γ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨1 + K, fun N => ?_⟩
  have hx : Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ≤ 1 :=
    exp_neg_div_correlationLength_le_one (by norm_num) (hnorm.trans_le ht1.le)
  have hpow : Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ^ N ≤ 1 :=
    pow_le_one₀ (by positivity) hx
  have := (abs_le.1 ((hc N).trans (mul_le_of_le_one_right hK hpow))).2
  linarith

/-- The overlap of two periodic states is bounded by the product of their norms. -/
theorem norm_mpvOverlap_le {n D₁ D₂ : ℕ} (X : MPSTensor n D₁) (Y : MPSTensor n D₂) (M : ℕ) :
    ‖mpvOverlap X Y M‖ ≤ ‖mpvState X M‖ * ‖mpvState Y M‖ := by
  rw [mpvOverlap_eq_star_mpvInner, norm_star, mpvInner]
  exact norm_inner_le_norm _ _

/-- The positive part of the `q`-site blocked tensor generates, on `M` blocks, a state of the
same norm as the periodic state of `A` on `qM` sites: both squared norms are `Tr E_A^{qM}`.
The source states `E_B = E_A^q` (arXiv:2307.01696, text after eq. (6)); `E_P = E_B` follows from
`B = V P` (`transferMap_polarPosTensor_blockTensor`). -/
theorem norm_mpvState_polarPosTensor_blockTensor [NeZero D] (A : MPSTensor d D) (q M : ℕ) :
    ‖mpvState (polarPosTensor (blockTensor A q)) M‖ = ‖mpvState A (q * M)‖ := by
  have h : ((‖mpvState (polarPosTensor (blockTensor A q)) M‖ ^ 2 : ℝ) : ℂ) =
      ((‖mpvState A (q * M)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_norm_mpvState_sq, ofReal_norm_mpvState_sq,
      ← trace_transferMatrix_transferMap_pow_eq_mpvOverlap,
      ← trace_transferMatrix_transferMap_pow_eq_mpvOverlap,
      transferMap_polarPosTensor_blockTensor, transferMatrix_pow, ← pow_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (Complex.ofReal_injective h)

/-- **Overlap of the positive part with the fixed point**, `O`-form (arXiv:2103.13367,
Supplemental Material, eq. (S29), quoted as arXiv:2307.01696, eq. (S9)): in the setting of
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le`, there is `C` with
`|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| ≤ C (N/q) e^{-γ q/ξ}` for all `q` and all `M ≥ 1`, `N = qM`.

For `(N/q) e^{-γ q/ξ} ≤ 1` this is the explicit bound; otherwise both overlaps are bounded,
since `‖φ_M(P_q)‖ = ‖φ_N(A)‖` and the norms `‖φ_N(A)‖` are bounded. -/
theorem exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le_mul (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      |1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖| ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨C, hC, h⟩ :=
    exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨B, hB⟩ := exists_norm_mpvState_sq_le A hN hA hσ htr hfix
  have hB0 : 0 ≤ B := (sq_nonneg _).trans (hB 0)
  refine ⟨C * Real.exp C + (2 + B), by positivity, fun q M _ => ?_⟩
  have hfp : ‖mpvState (fixedPointTensor σ) M‖ = 1 := by
    have h1 := ofReal_norm_mpvState_sq (fixedPointTensor σ) M
    rw [mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (Complex.ofReal_injective (by rw [h1]; simp))
  have hz : ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖ ≤ 1 + B := by
    refine (norm_mpvOverlap_le _ _ M).trans ?_
    rw [hfp, mul_one, norm_mpvState_polarPosTensor_blockTensor]
    nlinarith [hB (q * M), norm_nonneg (mpvState A (q * M))]
  refine le_mul_of_le_mul_exp_of_le hC.le (by linarith) (by positivity) (h q M) ?_
  rw [abs_le]
  constructor <;> linarith [norm_nonneg
    (mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M)]

/-! ### The approximation error -/

/-- The periodic state of `B' = V P_∞` on `M` blocks of `q` sites, read on the `Mq` sites
through the regrouping of sites into blocks (arXiv:2307.01696, eqs. (9) and (10)). -/
noncomputable def approximatingMPVStateRaw (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ)
    (q M : ℕ) : MPVSpace d (M * q) :=
  (EuclideanSpace.equiv (ι := Cfg d (M * q)) (𝕜 := ℂ)).symm fun s =>
    mpv (approximatingTensor (blockTensor A q) σ) ((blockedConfigEquiv d M q).symm s)

/-- The **approximating state** `|φ'_N⟩ = |φ_M(V P_∞)⟩ / ‖φ_M(V P_∞)‖` on `N = Mq` sites
(arXiv:2307.01696, eqs. (9) and (10)). -/
noncomputable def approximatingMPVState (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ)
    (q M : ℕ) : MPVSpace d (M * q) :=
  ((‖approximatingMPVStateRaw A σ q M‖ : ℂ)⁻¹) • approximatingMPVStateRaw A σ q M

@[simp] lemma approximatingMPVStateRaw_apply (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) (q M : ℕ) (s : Cfg d (M * q)) :
    approximatingMPVStateRaw A σ q M s =
      mpv (approximatingTensor (blockTensor A q) σ) ((blockedConfigEquiv d M q).symm s) := by
  simp [approximatingMPVStateRaw, EuclideanSpace.equiv, PiLp.toLp_apply]

/-- For `B_q` injective, the unnormalized approximating state is a unit vector.

arXiv:2307.01696, eq. (10) and Supplemental Material, line 1013: the approximating state is the
product of the block unitaries
applied to "(normalized) nearest-neighbor entangled pairs", hence a unit vector. -/
theorem norm_approximatingMPVStateRaw (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    ‖approximatingMPVStateRaw A σ q M‖ = 1 := by
  have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (approximatingMPVStateRaw A σ q M)).symm
  rw [PiLp.inner_apply, ← (blockedConfigEquiv d M q).sum_comp] at h
  simp only [RCLike.inner_apply, approximatingMPVStateRaw_apply, Equiv.symm_apply_apply] at h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (Complex.ofReal_injective ?_)
  push_cast
  exact h.trans ((Finset.sum_congr rfl fun _ _ => mul_comm _ _).trans
    (mpv_approximatingTensor_norm_sq hB hσ htr))

/-- For `B_q` injective, the approximating state is a unit vector.

arXiv:2307.01696, eq. (10), as for `norm_approximatingMPVStateRaw`. -/
theorem norm_approximatingMPVState (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    ‖approximatingMPVState A σ q M‖ = 1 := by
  rw [approximatingMPVState, norm_approximatingMPVStateRaw A hB hσ htr M]
  simp [norm_approximatingMPVStateRaw A hB hσ htr M]

/-- For `B_q` injective, the approximating state is the periodic state of `V P_∞` itself
(its norm is `1`), and its overlap with the periodic state of `A` is the overlap of the
positive part with the fixed point: `⟨φ'_N|φ_N(A)⟩ = ⟨φ_M(P_∞)|φ_M(P_q)⟩`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): the source's step that the first
term of its triangle inequality "is exactly equal to the LHS of eq. (S9)", which rests on this
identity. -/
theorem inner_approximatingMPVState_mpvState (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    approximatingMPVState A σ q M = approximatingMPVStateRaw A σ q M ∧
      ⟪approximatingMPVState A σ q M, mpvState A (M * q)⟫_ℂ =
        mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M := by
  have hinner : ∀ w : MPVSpace d (M * q),
      ⟪approximatingMPVStateRaw A σ q M, w⟫_ℂ =
        ∑ τ : Fin M → Fin (blockPhysDim d q),
          star (mpv (approximatingTensor (blockTensor A q) σ) τ) *
            w (blockedConfigEquiv d M q τ) := fun w => by
    rw [PiLp.inner_apply, ← (blockedConfigEquiv d M q).sum_comp]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [RCLike.inner_apply, approximatingMPVStateRaw_apply, Equiv.symm_apply_apply, mul_comm]
    rfl
  have heq : approximatingMPVState A σ q M = approximatingMPVStateRaw A σ q M := by
    rw [approximatingMPVState, norm_approximatingMPVStateRaw A hB hσ htr M]; simp
  refine ⟨heq, ?_⟩
  rw [heq, hinner]
  simp only [mpvState_apply, mpv_blockedConfigEquiv_eq_sum_polar, mpv_approximatingTensor]
  rw [(isIsometry_polarIsoMatrix_of_isInjective hB).sum_star_mul_tensorPower]
  simp only [mpvOverlap, mpv_fixedPointTensor]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- **The triangle inequality of Lemma 1'(i).** If `‖ψ‖ ≤ 1`, `|1 - |⟨ψ|v⟩|| ≤ a`, and
`|‖v‖² - 1| ≤ b`, then the error `1 - |⟨ψ|v/‖v‖⟩|` against the normalization of `v` is at most
`a + b`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i):
`ε ≤ |1 - c_N |⟨φ'_N|φ_N⟩|| + |c_N - 1| |⟨φ'_N|φ_N⟩|`. -/
theorem one_sub_norm_inner_smul_inv_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ v : E} (hψ : ‖ψ‖ ≤ 1) {a b : ℝ}
    (ha : |1 - ‖⟪ψ, v⟫_ℂ‖| ≤ a) (hb : |‖v‖ ^ 2 - 1| ≤ b) :
    1 - ‖⟪ψ, ((‖v‖ : ℂ)⁻¹) • v⟫_ℂ‖ ≤ a + b := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans ha
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

/-- **The error as a squared distance.** If `‖ψ‖ ≤ 1`, `‖v‖² ≥ 1/2`, and
`‖v‖² - |⟨ψ|v⟩|² ≤ W`, then the error `1 - |⟨ψ|v/‖v‖⟩|` is at most `2W`. With
`t = |⟨ψ|v⟩|/‖v‖ ≤ 1`, the error `1 - t` is at most `1 - t² = (‖v‖² - |⟨ψ|v⟩|²)/‖v‖²`.

Unlike `one_sub_norm_inner_smul_inv_norm_le`, the bound is of second order in the distance of
`v` from the line through `ψ`. -/
theorem one_sub_norm_inner_smul_inv_norm_le_two_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ v : E} (hψ : ‖ψ‖ ≤ 1) (hv : 1 / 2 ≤ ‖v‖ ^ 2) {W : ℝ}
    (hW : ‖v‖ ^ 2 - ‖⟪ψ, v⟫_ℂ‖ ^ 2 ≤ W) :
    1 - ‖⟪ψ, ((‖v‖ : ℂ)⁻¹) • v⟫_ℂ‖ ≤ 2 * W := by
  have hc : 0 < ‖v‖ := by
    rcases (norm_nonneg v).eq_or_lt with h | h
    · rw [← h] at hv; norm_num at hv
    · exact h
  have h1 : ‖⟪ψ, ((‖v‖ : ℂ)⁻¹) • v⟫_ℂ‖ = ‖⟪ψ, v⟫_ℂ‖ / ‖v‖ := by
    rw [inner_smul_right, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, inv_mul_eq_div]
  have h2 : ‖⟪ψ, v⟫_ℂ‖ ≤ ‖v‖ :=
    (norm_inner_le_norm ψ v).trans (mul_le_of_le_one_left (norm_nonneg _) hψ)
  have hW0 : 0 ≤ W := by nlinarith [norm_nonneg ⟪ψ, v⟫_ℂ]
  rw [h1]
  set s := ‖⟪ψ, v⟫_ℂ‖
  have hs : 0 ≤ s := norm_nonneg _
  -- `1 - s/c ≤ (c² - s²)/c² ≤ 2 W`.
  have key : (1 - s / ‖v‖) * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 - s ^ 2 := by
    rw [sub_mul, one_mul, div_mul_eq_mul_div, sq, ← mul_assoc, mul_div_assoc,
      div_self hc.ne', mul_one]
    nlinarith
  nlinarith

open scoped Matrix.Norms.L2Operator in
/-- **Approximation error, normal case, at rate `2γ/ξ`** (arXiv:2307.01696, Lemma 1 and
Lemma 1'(i), with an improved rate). Let `A` be normal in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`,
`E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (eq. (5)), let `λ₂` bound the moduli of the eigenvalues of
`E_A` other than `1`, with correlation length `ξ = -1/log|λ₂|`, and let `0 < γ < 1`. There is
`C > 0` such that for every block length `q` and every number of blocks `M ≥ 1`, with `N = Mq`
and `y = (N/q) e^{-2γ q/ξ} = M e^{-2γ q/ξ}`, the error `ε = 1 - |⟨φ'_N|φ_N⟩|` of the
approximating state satisfies `ε ≤ C y e^{C y}`.

Project result. It improves the rate `e^{-γ q/ξ}` with `γ < 1/2` of arXiv:2307.01696,
eqs. (17) and (S11), to `e^{-2γ q/ξ}` with `γ < 1`; compare the rate `e^{-q/ξ}` of
arXiv:2606.24475, App. B4, eqs. (S52) and (S53). The error is of second order in the distance
of the positive parts. With `b = ‖φ_N(A)‖²` and `a = ⟨φ'_N|φ_N(A)⟩ = ⟨φ_M(P_∞)|φ_M(P_q)⟩`,
`ε ≤ 2 (b - |a|²)` once `b ≥ 1/2` (`one_sub_norm_inner_smul_inv_norm_le_two_mul`). For `M = 1`,
`b - |a|²` is bounded by `exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le`; for `M ≥ 2`,
`b - 1 = O(e^{-γ N/ξ}) = O(e^{-2γ q/ξ})` (`exists_abs_norm_mpvState_sq_sub_one_le`) and
`1 - |a|` is bounded by `exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq`. For the finitely
many `q` below the injectivity length of `A`, and for `C y ≥ 1`, the bound holds because
`ε ≤ 1`. -/
theorem exists_approximationError_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂))) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨C₁, hC₁, hover⟩ :=
    exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₁, hK₁, hone⟩ :=
    exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₅, hK₅, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨L, hLpos, hL⟩ := hN
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  have hx : 0 < x := Real.exp_pos _
  set C := 1 + ((x ^ 2) ^ L)⁻¹ + 4 * K₅ ^ 2 + 2 * K₅ + 2 * K₁ + 4 * C₁
  have hL0 : 0 < ((x ^ 2) ^ L)⁻¹ := by positivity
  have hK₅2 : 0 ≤ 4 * K₅ ^ 2 := by positivity
  have hCL : 1 + ((x ^ 2) ^ L)⁻¹ ≤ C := by simp only [C]; linarith
  have hCa : 4 * K₅ ^ 2 ≤ C := by simp only [C]; linarith
  have hCc : C₁ ≤ C := by simp only [C]; linarith
  have hCd : 2 * K₅ + 4 * C₁ ≤ C := by simp only [C]; linarith
  have hCe : 2 * K₁ ≤ C := by simp only [C]; linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun q M _ => ?_⟩
  have hxq : Real.exp (-(2 * γ) * q / correlationLength lam₂) = (x ^ 2) ^ q := by
    rw [Real.exp_neg_mul_div_eq_pow, exp_neg_two_mul_div_correlationLength]
  rw [hxq]
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hε1 : 1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤ 1 := by
    linarith [norm_nonneg ⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ]
  refine le_mul_mul_exp_of_forall_le (L := fun _ : Unit => L) (by positivity : 0 < x ^ 2)
    (by simpa only [Finset.univ_unique, Finset.sum_singleton] using hCL) hM hε1
    fun hx1 hLq hsmall => ?_
  replace hLq := hLq ()
  have hx1' : x ≤ 1 := by nlinarith
  set δ := x ^ q with hδdef
  set y := (M : ℝ) * (x ^ 2) ^ q with hydef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ2 : (x ^ 2) ^ q = δ ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hy0 : 0 ≤ y := by positivity
  have hδy : δ ^ 2 ≤ y := by rw [← hδ2]; exact le_mul_of_one_le_left (by positivity) hM
  have hexp : 1 ≤ Real.exp (C * y) := Real.one_le_exp (by positivity)
  have hB : Kraus.IsInjective (blockTensor A q) :=
    (isNBlkInjective_iff_blockTensor_isInjective A q).1 (isNBlkInjective_of_le hLpos hL hLq)
  obtain ⟨-, hz⟩ := inner_approximatingMPVState_mpvState A hB hσ.posSemidef htr M
  have hφt := (norm_approximatingMPVState A hB hσ.posSemidef htr M).le
  -- It suffices to bound `‖φ_N(A)‖² - |⟨φ_M(P_∞)|φ_M(P_q)⟩|²`.
  suffices h : 1 / 2 ≤ ‖mpvState A (M * q)‖ ^ 2 ∧
      ‖mpvState A (M * q)‖ ^ 2 -
          ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖ ^ 2 ≤
        C * y * Real.exp (C * y) / 2 by
    rw [← hz] at h
    exact (one_sub_norm_inner_smul_inv_norm_le_two_mul hφt h.1 h.2).trans_eq (by ring)
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · -- One block.
    obtain rfl : M = 1 := by have := NeZero.ne M; omega
    have hc1 := hc (1 * q)
    rw [one_mul] at hc1
    have hK5 : K₅ * δ ≤ 1 / 2 := by
      have h4 : 4 * K₅ ^ 2 * y < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCa hy0) hsmall
      have h5 : K₅ ^ 2 * δ ^ 2 ≤ K₅ ^ 2 * y := mul_le_mul_of_nonneg_left hδy (sq_nonneg _)
      have h6 : (K₅ * δ) ^ 2 < (1 / 2) ^ 2 := by rw [mul_pow]; linarith only [h4, h5]
      exact ((pow_lt_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 h6).le
    have hK5' : K₅ * x ^ q ≤ 1 / 2 := hK5
    have hAq : ‖mpvState A (1 * q)‖ = ‖mpvState A q‖ := by rw [one_mul]
    have hvu : ‖mpvState A q‖ = ‖mpvState (polarPosTensor (blockTensor A q)) 1‖ := by
      rw [norm_mpvState_polarPosTensor_blockTensor, mul_one]
    rw [hAq]
    refine ⟨by linarith only [(abs_le.1 hc1).1, hK5'], ?_⟩
    rw [hvu]
    have h1 := hone q
    have hy1 : y = (x ^ 2) ^ q := by rw [hydef, Nat.cast_one, one_mul]
    have h2 : 2 * K₁ * y ≤ C * y := mul_le_mul_of_nonneg_right hCe hy0
    have h3 : C * y ≤ C * y * Real.exp (C * y) := le_mul_of_one_le_right (by positivity) hexp
    rw [← hy1] at h1
    linarith only [h1, h2, h3]
  -- At least two blocks.
  have hlow := hover q M hM2 (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCc hy0) hsmall)
  have hcy : |‖mpvState A (M * q)‖ ^ 2 - 1| ≤ K₅ * y := by
    refine (hc (M * q)).trans (mul_le_mul_of_nonneg_left ?_ hK₅)
    calc x ^ (M * q) ≤ x ^ (2 * q) := pow_le_pow_of_le_one hx.le hx1' (by nlinarith)
      _ = δ ^ 2 := by rw [hδdef, ← pow_mul, mul_comm]
      _ ≤ y := hδy
  have hK5y : K₅ * y ≤ 1 / 2 := by
    have h := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (show 2 * K₅ ≤ C by linarith) hy0)
      hsmall
    linarith only [h]
  refine ⟨by linarith only [(abs_le.1 hcy).1, hK5y], ?_⟩
  set s := ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖
  have hs0 : 0 ≤ s := norm_nonneg _
  set u := C₁ * y * Real.exp (C₁ * y)
  have hu0 : 0 ≤ u := by positivity
  have hsq : 1 - s ^ 2 ≤ 2 * u := by
    by_cases hs1 : s ≤ 1
    · nlinarith only [hlow, hs1, hs0]
    · nlinarith only [hs1, hu0]
  have hexpC : Real.exp (C₁ * y) ≤ Real.exp (C * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCc hy0)
  have h1 : u ≤ C₁ * y * Real.exp (C * y) := mul_le_mul_of_nonneg_left hexpC (by positivity)
  have h2 : K₅ * y ≤ K₅ * y * Real.exp (C * y) := le_mul_of_one_le_right (by positivity) hexp
  have h3 : (2 * K₅ + 4 * C₁) * y * Real.exp (C * y) ≤ C * y * Real.exp (C * y) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd hy0) (by positivity)
  have h4 : (2 * K₅ + 4 * C₁) * y * Real.exp (C * y) =
      2 * (K₅ * y * Real.exp (C * y)) + 4 * (C₁ * y * Real.exp (C * y)) := by ring
  linarith only [(abs_le.1 hcy).2, hsq, h1, h2, h3, h4]

/-- **Approximation error, normal case, `O`-form** (arXiv:2307.01696, Lemma 1, eq. (17), and
Lemma 1'(i), eq. (S11)). In the setting of `exists_approximationError_le`, there is `C` with
`ε(φ'_N, φ_N) ≤ C (N/q) e^{-2γ q/ξ}` for every block length `q` and every number of blocks
`M ≥ 1`, `N = Mq`, and every `0 < γ < 1`.

Project result. It improves the rate `e^{-γ q/ξ}`, `γ < 1/2`, of the source to
`e^{-2γ q/ξ}`, `γ < 1` (see `exists_approximationError_le`). For `(N/q) e^{-2γ q/ξ} ≤ 1` this
is the explicit bound; otherwise it holds because `ε ≤ 1`. -/
theorem exists_approximationError_le_mul (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg ⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ]

end MPSTensor
