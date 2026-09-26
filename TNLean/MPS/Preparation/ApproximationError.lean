/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NormedRingTelescoping
import TNLean.MPS.Preparation.PositivePartRate
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Wielandt.SpanGrowth.CumulativeSpan

/-!
# The approximation error of the log-depth preparation, normal case

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), and let `λ₂` bound the moduli of the eigenvalues of `E_A` other
than `1`, with correlation length `ξ = -1/log|λ₂|`. Block `q` sites, write `B_q = V P_q` for the
polar decomposition of the blocked tensor, and let `P_∞` be the fixed-point tensor. For `N = qM`
this file proves, for every `0 < γ < 1/2`, explicit forms of

* the overlap estimate of Piroli, Styliaris, and Cirac (arXiv:2103.13367, Supplemental Material,
  "Proof of Theorem MPS_classification", eq. (S29)), quoted as eq. (S9) of arXiv:2307.01696:
  `|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| = O((N/q) e^{-γ q/ξ})`;
* the approximation error of arXiv:2307.01696, Lemma 1 and Lemma 1'(i):
  `ε(φ'_N, φ_N) = 1 - |⟨φ'_N|φ_N⟩| = O((N/q) e^{-γ q/ξ})`.

Both are stated as `≤ C y e^{C y}` with `y = (N/q) e^{-γ q/ξ}` and a constant `C` depending only
on `A`, `σ`, `λ₂`, and `γ`, for all `q` and all `M ≥ 1`. This is the form in which the source's
iteration closes (arXiv:2103.13367, eq. `finished`: `ε_q + ε_q² (1 + ε_q/M)^{M-2}`), and it gives
the `O`-bound whenever `y` stays bounded. The variants ending in `_mul` state the `O`-bound
itself, `≤ C (N/q) e^{-γ q/ξ}` for all `q` and all `M ≥ 1`: for `y > 1` it follows from `ε ≤ 1`
and from the boundedness of the norms `‖φ_N(A)‖`.

## Proof outline (following arXiv:2103.13367)

1. **Transfer-map gap.** `‖E_A^n(X) - Tr(X) σ‖ ≤ C r^n ‖X‖` with `r = e^{-2γ/ξ}`, which exceeds
   the spectral radius of `E_A - |σ⟩⟨1|` because `2γ < 1` (compare eq. `difference`,
   `‖R‖_F ≤ Λ(q) e^{-qα}` with `|λ₁| = e^{-qα}` for the blocked transfer matrix).
2. **Positive parts.** `P_q² - P_∞²` is a rearrangement of `E_A^q - |σ⟩⟨1|`, and
   `‖√X - √Y‖ ≤ √‖X - Y‖` (eq. `intermediate`) gives `‖P_q - P_∞‖ ≤ C e^{-γ q/ξ}`.
3. **Telescoping.** For an idempotent `T_∞` and `‖T - T_∞‖ ≤ δ`,
   `‖T^M - T_∞^M‖ ≤ c((1 + cδ)^M - 1)` (eqs. `final_eq` to `finished`), applied to the mixed
   transfer matrices `τ_{AB}` and `τ_{BB}` of `P_q` against `P_∞`.
4. **Normalization.** `c_N² = Tr E_A^N` differs from `1` by `O(e^{-2γN/ξ})`, and the triangle
   inequality of arXiv:2307.01696, proof of Lemma 1'(i), combines the two errors. Since `N ≥ q`
   the normalization term is dominated by the overlap term; no condition `q = o(N)` is needed.

## Main declarations

* `norm_pow_sub_pow_le_of_isIdempotentElem` (in `TNLean.Algebra.NormedRingTelescoping`) — the
  telescoping bound of step 3.
* Steps 1 and 2 are `MPSTensor.exists_norm_transferMap_pow_sub_le` and
  `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` in
  `TNLean.MPS.Preparation.PositivePartRate`.
* `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le` and its `O`-form
  `MPSTensor.exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le_mul` — the overlap estimate
  (S29) of arXiv:2103.13367.
* `MPSTensor.normalizedMPVState`, `MPSTensor.approximatingMPVState` — the normalized states
  `φ_N` and `φ'_N`.
* `MPSTensor.exists_approximationError_le` and its `O`-form
  `MPSTensor.exists_approximationError_le_mul` — the approximation error, Lemma 1'(i).

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (eqs.
  `difference`, `final_eq`, `intermediate`, `inequality`, `almost_done`, `finished`).
* arXiv:2307.01696, Lemma 1 (`lm:1`), eq. (17) (`eq:fid_err`), and Supplemental Material,
  "Proof of Lemma 1 and extension to non-normal tensors", eq. (S9) (`eq:app_error`) and
  Lemma 1'(i) (`eq:fid_err_gen_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace

/-- A square matrix of trace one has a nonempty index: `Tr σ = 1` forces `D ≠ 0`. -/
theorem Matrix.neZero_of_trace_eq_one {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (h : σ.trace = 1) : NeZero D :=
  ⟨by rintro rfl; simp at h⟩

namespace MPSTensor

variable {d D : ℕ}

/-! ### Mixed transfer matrices -/

/-- Reading a `D² × D²` matrix `G` as the tensor with physical dimension `D²` whose `k`-th matrix
is the `k`-th row of `G`, as a linear map. -/
noncomputable def ofPhysicalMatrixLM :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ] MPSTensor (D * D) D where
  toFun G := ofPhysicalMatrix (G.submatrix (virtualPairEquiv D) id)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The mixed map against a fixed right family, as a linear map in the left family. -/
noncomputable def mixedMapLMLeft {n : ℕ} (B : MPSTensor n D) :
    MPSTensor n D →ₗ[ℂ] Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) where
  toFun A := Kraus.mixedMapLM A B
  map_add' A A' := LinearMap.ext fun X => by simp [Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c A := Kraus.mixedMapLM_smul_left c A B

/-- The linear map `G ↦ τ_{G,B}` sending a `D² × D²` matrix `G`, read as a tensor through
`ofPhysicalMatrixLM`, to the transfer matrix of its mixed transfer map against `B`.

arXiv:2103.13367, the mixed transfer matrix `τ_{AB} = A† B` after eq. `eq:a_tensor`, read as a
function of `A`. -/
noncomputable def mixedTransferMatrixLeft (B : MPSTensor (D * D) D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  transferMatrixLM ∘ₗ mixedMapLMLeft B ∘ₗ ofPhysicalMatrixLM

/-- The mixed transfer matrix of `P_∞` against itself is idempotent: `E_{P_∞}` is the rank-one
projection `X ↦ Tr(X) σ` (arXiv:2103.13367: `τ_BB² = τ_BB`). -/
theorem isIdempotentElem_transferMatrix_fixedPointTensor {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    IsIdempotentElem (transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ)
      (fixedPointTensor σ))) := by
  rw [IsIdempotentElem, ← sq, ← transferMatrix_pow, Kraus.mixedMapLM_self, sq,
    Module.End.mul_eq_comp]
  exact congrArg transferMatrix (isTransferIdempotent_fixedPointTensor hσ htr)

/-- The fixed-point state is normalized: `⟨φ_M(P_∞)|φ_M(P_∞)⟩ = 1` for `M ≥ 1`
(arXiv:2103.13367: `⟨ψ_M|ψ_M⟩ = Tr τ_BB^M = 1`). -/
theorem mpvOverlap_fixedPointTensor_self {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (M : ℕ) [NeZero M] :
    mpvOverlap (fixedPointTensor σ) (fixedPointTensor σ) M = 1 := by
  simp only [mpvOverlap, mpv_fixedPointTensor]
  rw [← pairProductState_fixedPointPair_norm_sq (N := M) hσ htr]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun τ => ?_
  rw [mul_comm]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive part with the fixed point, as a complex number.** In the setting of
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le`, the overlap itself, not only its modulus,
is close to `1`: `|⟨φ_M(P_∞)|φ_M(P_q)⟩ - 1| ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished`: the telescoping estimate bounds `Tr τ_{AB}^M - Tr τ_{BB}^M`, which is
this difference. -/
theorem exists_norm_mpvOverlap_polarPosTensor_sub_one_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1‖ ≤
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
  refine ⟨K₄ * c * K + K + 1, by positivity, fun q M _ => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  set T := transferMatrix
    (Kraus.mixedMapLM (polarPosTensor (blockTensor A q)) (fixedPointTensor σ))
  -- `T - Tinf = Ψ(P_q - P_∞)`.
  have hTΨ : T - Tinf = Ψ (Matrix.polarPos (physicalMatrix (blockTensor A q)) -
      (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [map_sub]
    congr 1
    change Tinf = transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrix
      (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)).submatrix (virtualPairEquiv D) id))
      (fixedPointTensor σ))
    rw [ofPhysicalMatrix_sqrt_transpose_kronecker_one]
  have hδ : ‖T - Tinf‖ ≤ K₃ * K₁ * x ^ q := by
    rw [hTΨ]
    refine (hΨ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpos q) hK₃
  have htel := norm_pow_sub_pow_le_of_isIdempotentElem
    (isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr)
    (c := c) (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))
    hδ M
  -- The overlap is `Tr T^M`, and `1 = Tr Tinf^M`.
  have hover : mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1 =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (T ^ M - Tinf ^ M) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap,
      mpvOverlap_fixedPointTensor_self hσ.posSemidef htr]
  have hy : 0 ≤ c * (K₃ * K₁ * x ^ q) := by positivity
  have hgeom := one_add_pow_sub_one_le_mul_exp hy M
  calc ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M - 1‖
      ≤ K₄ * ‖T ^ M - Tinf ^ M‖ := by rw [hover]; exact htrace _
    _ ≤ K₄ * (c * ((1 + c * (K₃ * K₁ * x ^ q)) ^ M - 1)) := by gcongr
    _ ≤ K₄ * (c * (M * (c * (K₃ * K₁ * x ^ q)) *
          Real.exp (M * (c * (K₃ * K₁ * x ^ q))))) := by gcongr
    _ = K₄ * c * K * u * Real.exp (K * u) := by
        simp only [u, K]; ring_nf
    _ ≤ (K₄ * c * K + K + 1) * u * Real.exp ((K₄ * c * K + K + 1) * u) := by
        have hKC : K ≤ K₄ * c * K + K + 1 := by nlinarith [mul_nonneg (mul_nonneg hK₄ hc) hK]
        have hKC' : K₄ * c * K ≤ K₄ * c * K + K + 1 := by linarith
        gcongr

/-- **Overlap of the positive part with the fixed point.** Let `A` be normal in the gauge
`∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (arXiv:2307.01696, eq. (5)), let `λ₂`
bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length `ξ`, and let
`0 < γ < 1/2`. Then there is `C > 0` such that for all `q` and all `M ≥ 1`, with `N = qM` and
`y = (N/q) e^{-γ q/ξ} = M e^{-γ q/ξ}`,
`|1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩|| ≤ C y e^{C y}`, where `P_q` is the positive part of the `q`-site
blocked tensor and `P_∞` the fixed-point tensor.

arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification", eqs.
`final_eq` to `finished` (the estimate (S29)), quoted as arXiv:2307.01696, eq. (S9). The source
concludes `O(ε_q)` from `ε_q + ε_q² e^{ε_q}(1 + O(ε_q/M))`, which is the present bound in the
regime where `ε_q` stays bounded. -/
theorem exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
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
/-- The transfer matrix of `E_A^n` is `e^{-2γ n/ξ}`-close to that of `X ↦ Tr(X) σ`, in the
setting of `exists_norm_transferMap_pow_sub_le`. -/
theorem exists_norm_transferMatrix_pow_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖transferMatrix (Kraus.transferMap A) ^ n -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ n := by
  obtain ⟨C, hC, hgap⟩ := exists_norm_transferMap_pow_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K, hK, h⟩ := exists_norm_le_of_entry_eq_pow_sub (Kraus.transferMap A) σ hC.le hgap
    (fun (_ b : Fin D × Fin D) => Matrix.single b.2 b.1 (1 : ℂ))
    (fun a _ => a.2) (fun a _ => a.1)
  refine ⟨K, hK, fun n => ?_⟩
  rw [← transferMatrix_pow]
  refine h n _ fun a b => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, ← transferMap_fixedPointTensor_apply hσ.posSemidef]
  rfl

/-- The squared norm of the periodic state is the self-overlap: `‖φ_N(A)‖² = ⟨φ_N|φ_N⟩`. -/
theorem ofReal_norm_mpvState_sq (A : MPSTensor d D) (N : ℕ) :
    ((‖mpvState A N‖ ^ 2 : ℝ) : ℂ) = mpvOverlap A A N := by
  rw [EuclideanSpace.norm_sq_eq, mpvOverlap]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mpvState_apply, ← Complex.mul_conj']
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **Normalization.** In the setting of `exists_norm_transferMap_pow_sub_le`, the squared norm
`c_N² = Tr E_A^N` of the periodic state satisfies `|c_N² - 1| ≤ K e^{-2γ N/ξ}`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): `c_N = √(Tr E_A^N)` and
`|c_N - 1| = O(e^{-N/ξ})`. -/
theorem exists_abs_norm_mpvState_sq_sub_one_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      |‖mpvState A N‖ ^ 2 - 1| ≤ K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ N := by
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

/-- The periodic states of a normal tensor in the gauge of `exists_norm_transferMap_pow_sub_le`
have bounded norms: `c_N² = Tr E_A^N ≤ B` for all `N`. -/
theorem exists_norm_mpvState_sq_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) :
    ∃ B : ℝ, ∀ N : ℕ, ‖mpvState A N‖ ^ 2 ≤ B := by
  have := Matrix.neZero_of_trace_eq_one htr
  have hNT := isNormalTensor_of_isNormal_leftCanonical A hN hA
  have hCh := Kraus.isChannel_mapLM A hA
  obtain ⟨δ, hδ, hgap⟩ := uniform_eigenvalue_gap_of_finite_lt_one
    (Module.End.finite_hasEigenvalue (Kraus.transferMap A)) fun μ hμ hne =>
      lt_of_le_of_ne (hCh.eigenvalue_norm_le_one μ hμ)
        fun h => hne (hNT.primitive_transfer.unique_peripheral μ hμ h)
  set t := max (1 - δ) (1 / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by norm_num)
  have ht1 : t ≤ 1 := max_le (by linarith) (by norm_num)
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, hc⟩ := exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (fun μ hμ hne => by rw [hnorm]; exact (hgap μ hμ hne).trans (le_max_left _ _))
    (γ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨1 + K, fun N => ?_⟩
  have hx : Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ≤ 1 := by
    rw [neg_div_correlationLength, hnorm, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Real.log_nonpos ht0.le ht1)
  have hpow : (Real.exp (-(1 / 4) / correlationLength (t : ℂ)) ^ 2) ^ N ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) hx)
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
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

/-- The normalized periodic state `|φ_N⟩ = c_N⁻¹ |φ_N(A)⟩` with `c_N = ‖φ_N(A)‖`
(arXiv:2307.01696, Supplemental Material, eq. `eq:TI-MPS2`); it is `0` when `c_N = 0`. -/
noncomputable def normalizedMPVState (A : MPSTensor d D) (N : ℕ) : MPVSpace d N :=
  ((‖mpvState A N‖ : ℂ)⁻¹) • mpvState A N

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
  have hnorm : ‖approximatingMPVStateRaw A σ q M‖ = 1 := by
    have h := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (approximatingMPVStateRaw A σ q M)).symm
    simp only [hinner, approximatingMPVStateRaw_apply, Equiv.symm_apply_apply,
      mpv_approximatingTensor_norm_sq hB hσ htr] at h
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (Complex.ofReal_injective ?_)
    push_cast
    exact h
  have heq : approximatingMPVState A σ q M = approximatingMPVStateRaw A σ q M := by
    rw [approximatingMPVState, hnorm]; simp
  refine ⟨heq, ?_⟩
  rw [heq, hinner]
  simp only [mpvState_apply, mpv_blockedConfigEquiv_eq_sum_polar, mpv_approximatingTensor]
  rw [(isIsometry_polarIsoMatrix_of_isInjective hB).sum_star_mul_tensorPower]
  simp only [mpvOverlap, mpv_fixedPointTensor]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- **Approximation error, normal case** (arXiv:2307.01696, Lemma 1 and Lemma 1'(i)). Let `A`
be normal in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1` (eq. (5)), let
`λ₂` bound the moduli of the eigenvalues of `E_A` other than `1`, with correlation length
`ξ = -1/log|λ₂|`, and let `0 < γ < 1/2`. There is `C > 0` such that for every block length `q`
and every number of blocks `M ≥ 1`, with `N = Mq` and `y = (N/q) e^{-γ q/ξ} = M e^{-γ q/ξ}`,
the error `ε = 1 - |⟨φ'_N|φ_N⟩|` of the approximating state satisfies `ε ≤ C y e^{C y}`.

In particular `ε = O((N/q) e^{-γ q/ξ})` whenever `(N/q) e^{-γ q/ξ}` stays bounded (eq. (17)
and eq. (S11)); see `exists_approximationError_le_mul` for the unconditional `O`-form.

The proof is the triangle inequality of the source,
`ε ≤ |1 - c_N |⟨φ'_N|φ_N⟩|| + |c_N - 1| |⟨φ'_N|φ_N⟩|`, with the first term bounded by
`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le` (eq. (S9)) and the second by
`exists_abs_norm_mpvState_sq_sub_one_le`. The source drops the second term using `q = o(N)`;
here it is bounded by `e^{-2γN/ξ} ≤ e^{-γ q/ξ}` since `N ≥ q`, so no condition relating `q`
and `N` is needed. For the finitely many `q` below the injectivity length of `A` the bound
holds because `ε ≤ 1`. -/
theorem exists_approximationError_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C₁, hC₁, hover⟩ :=
    exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨K₅, hK₅, hc⟩ :=
    exists_abs_norm_mpvState_sq_sub_one_le A hN hA hσ htr hfix hlam hγ0 hγ
  obtain ⟨L, hLpos, hL⟩ := hN
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx : 0 < x := Real.exp_pos _
  set C := C₁ + K₅ + (x ^ L)⁻¹ + 1
  have hxL : 0 < (x ^ L)⁻¹ := by positivity
  have hC₁C : C₁ ≤ C := by linarith
  refine ⟨C, by positivity, fun q M _ => ?_⟩
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hu : 0 ≤ u := by positivity
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  set φt := approximatingMPVState A σ q M
  set φ := normalizedMPVState A (M * q)
  have hε1 : 1 - ‖⟪φt, φ⟫_ℂ‖ ≤ 1 := by linarith [norm_nonneg ⟪φt, φ⟫_ℂ]
  -- When `C u ≥ 1` the bound is trivial.
  have htriv : 1 ≤ C * u → 1 - ‖⟪φt, φ⟫_ℂ‖ ≤ C * u * Real.exp (C * u) := fun h =>
    hε1.trans (h.trans (le_mul_of_one_le_right (by positivity) hexp))
  by_cases hbig : 1 ≤ C * u
  · exact htriv hbig
  rw [not_le] at hbig
  have hx1 : x < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ u := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ h)
    have : 1 ≤ C := by linarith
    nlinarith
  have hLq : L ≤ q := by
    by_contra h
    rw [not_le] at h
    have hxLq : x ^ L ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le h.le
    have : x ^ L ≤ u := hxLq.trans (le_mul_of_one_le_left (by positivity) hM)
    have : 1 ≤ (x ^ L)⁻¹ * u := by
      rw [← inv_mul_cancel₀ (by positivity : x ^ L ≠ 0)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have : (x ^ L)⁻¹ * u ≤ C * u := by
      refine mul_le_mul_of_nonneg_right ?_ hu
      linarith
    linarith
  have hB : Kraus.IsInjective (blockTensor A q) :=
    (isNBlkInjective_iff_blockTensor_isInjective A q).1 (isNBlkInjective_of_le hLpos hL hLq)
  obtain ⟨-, hz⟩ := inner_approximatingMPVState_mpvState A hB hσ.posSemidef htr M
  set z := mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M
  set c := ‖mpvState A (M * q)‖
  -- The normalization term: `|c² - 1| ≤ K₅ e^{-2γN/ξ} ≤ K₅ u`.
  have hcu : |c ^ 2 - 1| ≤ K₅ * u := by
    refine (hc (M * q)).trans (mul_le_mul_of_nonneg_left ?_ hK₅)
    calc (x ^ 2) ^ (M * q) = x ^ (2 * (M * q)) := (pow_mul _ _ _).symm
      _ ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le (by
          have := Nat.one_le_iff_ne_zero.2 (NeZero.ne M); nlinarith)
      _ ≤ u := le_mul_of_one_le_left (by positivity) hM
  have hinner : ⟪φt, φ⟫_ℂ = (c : ℂ)⁻¹ * z := by
    rw [show φ = ((c : ℂ)⁻¹) • mpvState A (M * q) from rfl, inner_smul_right, hz]
  have hC' : C₁ * u * Real.exp (C₁ * u) + K₅ * u ≤ C * u * Real.exp (C * u) := by
    have h1 : C₁ * u * Real.exp (C₁ * u) ≤ C₁ * u * Real.exp (C * u) := by
      gcongr
    have h2 : K₅ * u ≤ K₅ * u * Real.exp (C * u) :=
      le_mul_of_one_le_right (by positivity) hexp
    have h3 : (C₁ + K₅) * u * Real.exp (C * u) ≤ C * u * Real.exp (C * u) := by
      gcongr
      linarith
    nlinarith
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- `c = 0`: then `|c² - 1| = 1 ≤ K₅ u`.
    have : 1 ≤ K₅ * u := by simpa [hc0] using hcu
    refine hε1.trans (this.trans ?_)
    nlinarith [Real.exp_pos (C₁ * u), mul_nonneg (mul_nonneg hC₁.le hu) (Real.exp_pos (C₁ * u)).le]
  · have hcpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc0)
    set w := ‖⟪φt, φ⟫_ℂ‖
    have hw1 : w ≤ 1 := by
      refine (norm_inner_le_norm (𝕜 := ℂ) φt φ).trans ?_
      have hunit : ∀ v : MPVSpace d (M * q), ‖((‖v‖ : ℂ)⁻¹) • v‖ ≤ 1 := fun v => by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
      calc ‖φt‖ * ‖φ‖ ≤ 1 * 1 := mul_le_mul (hunit _) (hunit _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hcw : c * w = ‖z‖ := by
      have hw : w = ‖(c : ℂ)⁻¹ * z‖ := by simp only [w, hinner]
      rw [hw, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hcpos, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hc1 : |c - 1| ≤ |c ^ 2 - 1| := by
      rw [show c ^ 2 - 1 = (c - 1) * (c + 1) by ring, abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
    have hover' := hover q M
    rw [hxq] at hover'
    have : 1 - w ≤ |1 - ‖z‖| + |c - 1| := by
      have e : 1 - w = (1 - ‖z‖) + (c - 1) * w := by rw [← hcw]; ring
      rw [e]
      have : (c - 1) * w ≤ |c - 1| := by
        calc (c - 1) * w ≤ |c - 1| * w := mul_le_mul_of_nonneg_right (le_abs_self _)
              (norm_nonneg _)
          _ ≤ |c - 1| * 1 := mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
          _ = |c - 1| := mul_one _
      linarith [le_abs_self (1 - ‖z‖)]
    linarith

/-- **Approximation error, normal case, `O`-form** (arXiv:2307.01696, Lemma 1, eq. (17), and
Lemma 1'(i), eq. (S11)): in the setting of `exists_approximationError_le`, there is `C` with
`ε(φ'_N, φ_N) ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` and every number of blocks
`M ≥ 1`, `N = Mq`.

For `(N/q) e^{-γ q/ξ} ≤ 1` this is the explicit bound; otherwise it holds because `ε ≤ 1`. -/
theorem exists_approximationError_le_mul (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le A hN hA hσ htr hfix hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg ⟪approximatingMPVState A σ q M, normalizedMPVState A (M * q)⟫_ℂ]

end MPSTensor
