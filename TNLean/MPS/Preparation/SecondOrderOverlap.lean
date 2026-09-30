/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IdempotentTracePerturbation
import TNLean.MPS.Preparation.InjectivityCutoff
import TNLean.MPS.Preparation.PositivePartRate
import TNLean.Spectral.MPVOverlapTrace

/-!
# The overlap of the positive part with the fixed point, to second order

Let `A` be a normal tensor in the gauge `∑ᵢ (Aⁱ)† Aⁱ = 1`, `E_A(σ) = σ`, `σ > 0`, `Tr σ = 1`
(arXiv:2307.01696, eq. (5)), and let `λ₂` bound the moduli of the eigenvalues of `E_A` other
than `1`, with correlation length `ξ = -1/log|λ₂|`. Let `P_q` be the positive part of the
`q`-site blocked tensor and `P_∞` the fixed-point tensor. This file proves that the overlap
`⟨φ_M(P_∞)|φ_M(P_q)⟩` is `1` up to second order in `‖P_q - P_∞‖`, which gives the rate
`e^{-2γ q/ξ}` of `TNLean.MPS.Preparation.ApproximationError`.

The overlap is `Tr τ_q^M` for the mixed transfer matrix `τ_q` of `P_q` against `P_∞`. Since `τ_∞`
is the rank-one idempotent `X ↦ Tr(X) σ`, `τ_∞ τ_q τ_∞ = α τ_∞` with `1 - |α| = O(‖P_q - P_∞‖²)`,
and `τ_q = α (τ_∞ + Z)` with `τ_∞ Z τ_∞ = 0`. The trace of `(τ_∞ + Z)^M` is `1` up to
`O(M ‖Z‖²)` for `M ≥ 2` (`IsIdempotentElem.norm_trace_add_pow_sub_le_of_le`). This is a project
result: arXiv:2103.13367, Supplemental Material, eq. (34), and arXiv:2307.01696, eq. (S9), bound
the overlap to first order, and arXiv:2606.24475, App. B4, eq. (S52), bounds the trace linearly in
the residual.

## Main declarations

* `MPSTensor.isIdempotentElem_transferMatrix_fixedPointTensor`,
  `MPSTensor.mpvOverlap_fixedPointTensor_self` — `τ_∞` is idempotent and `φ_M(P_∞)` is a unit
  vector.
* `MPSTensor.exists_norm_map_polarPosTensor_sub_le` — linear images of `P_q` converge to those of
  `P_∞` at rate `e^{-γ q/ξ}`.
* `MPSTensor.exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq` — the overlap to second order,
  for `M ≥ 2`.
* `MPSTensor.exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le` — the case `M = 1`.

## References

* arXiv:2103.13367, Supplemental Material, "Proof of Theorem MPS_classification" (the mixed
  transfer matrices after eq. `eq:a_tensor`, and eq. (34)).
* arXiv:2307.01696, eq. (5) and Supplemental Material, eq. (S9).
* arXiv:2606.24475, App. B4, eq. (S52).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace

/-- A square matrix of trace one has a nonempty index: `Tr σ = 1` forces `D ≠ 0`. -/
theorem Matrix.neZero_of_trace_eq_one {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (h : σ.trace = 1) : NeZero D :=
  ⟨by rintro rfl; simp at h⟩

namespace MPSTensor

variable {d D : ℕ}

/-! ### Mixed transfer matrices against the fixed point -/

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

/-- The squared norm of the periodic state is the self-overlap: `‖φ_N(A)‖² = ⟨φ_N|φ_N⟩`. -/
theorem ofReal_norm_mpvState_sq (A : MPSTensor d D) (N : ℕ) :
    ((‖mpvState A N‖ ^ 2 : ℝ) : ℂ) = mpvOverlap A A N := by
  rw [EuclideanSpace.norm_sq_eq, mpvOverlap]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mpvState_apply, ← Complex.mul_conj']
  rfl

/-! ### Second-order ingredients -/

open scoped Matrix.Norms.L2Operator in
/-- **Linear images of the positive parts.** In the setting of
`exists_norm_polarPos_blockTensor_sub_le`, with `0 < γ < 1`, every linear map `L` on tensors
with physical dimension `D²` satisfies `‖L(P_q) - L(P_∞)‖ ≤ K e^{-γ q/ξ}` for all `q`, where
`P_q` is the positive part of the `q`-site blocked tensor and `P_∞` the fixed-point tensor. -/
theorem exists_norm_map_polarPosTensor_sub_le (A : MPSTensor d D) (hN : Kraus.IsNormal A)
    (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : MPSTensor (D * D) D →ₗ[ℂ] F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖L (polarPosTensor (blockTensor A q)) - L (fixedPointTensor σ)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K₁, hK₁, hpos⟩ :=
    exists_norm_polarPos_blockTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
  set Φ := LinearMap.toContinuousLinearMap (L ∘ₗ ofPhysicalMatrixLM)
  refine ⟨‖Φ‖ * K₁, by positivity, fun q => ?_⟩
  have h : L (polarPosTensor (blockTensor A q)) - L (fixedPointTensor σ) =
      Φ (Matrix.polarPos (physicalMatrix (blockTensor A q)) -
        (CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [map_sub, ← ofPhysicalMatrix_sqrt_transpose_kronecker_one σ]
    rfl
  rw [h, mul_assoc]
  exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hpos q) (norm_nonneg _))

/-- The mixed transfer matrix `τ_∞` of `P_∞` against itself is the rank-one map `X ↦ Tr(X) σ`,
so it compresses every mixed transfer matrix to a multiple of itself:
`τ_∞ τ_{XY} τ_∞ = Tr(E_{XY}(σ)) τ_∞`, where `E_{XY}(ρ) = ∑ᵢ Xⁱ ρ (Yⁱ)†`. -/
theorem transferMatrix_fixedPointTensor_mul_mul {n : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (X Y : MPSTensor n D) :
    transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ)) *
        transferMatrix (Kraus.mixedMapLM X Y) *
        transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ)) =
      (Kraus.mixedMapLM X Y σ).trace •
        transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ)) := by
  have hE : ∀ ρ, Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ) ρ = ρ.trace • σ :=
    fun ρ => by rw [Kraus.mixedMapLM_self]; exact transferMap_fixedPointTensor_apply hσ ρ
  rw [← transferMatrix_comp, ← transferMatrix_comp]
  have hsmul : ∀ (c : ℂ) (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ),
      c • transferMatrix T = transferMatrix (c • T) := fun c T =>
    (map_smul (transferMatrixLM (D := D)) c T).symm
  rw [hsmul]
  congr 1
  refine LinearMap.ext fun ρ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hE, map_smul,
    smul_smul, mul_comm]

/-- The vectors `(Xⁱ √σ)ᵢ` of a tensor `X`, as a linear map into a Hilbert space. Their inner
products are the numbers `Tr(E_{XY}(σ))` of `transferMatrix_fixedPointTensor_mul_mul`
(`inner_sqrtWeightLM`). -/
noncomputable def sqrtWeightLM {n : ℕ} (σ : Matrix (Fin D) (Fin D) ℂ) :
    MPSTensor n D →ₗ[ℂ] EuclideanSpace ℂ (Fin n × Fin D × Fin D) where
  toFun X := WithLp.toLp 2 fun p => (X p.1 * CFC.sqrt σ) p.2.1 p.2.2
  map_add' X Y := by ext p; simp [Matrix.add_mul]
  map_smul' c X := by ext p; simp

/-- `⟨(Yⁱ √σ)ᵢ | (Xⁱ √σ)ᵢ⟩ = Tr(∑ᵢ Xⁱ σ (Yⁱ)†)` for `σ ≥ 0`. -/
theorem inner_sqrtWeightLM {n : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef)
    (X Y : MPSTensor n D) :
    ⟪sqrtWeightLM σ Y, sqrtWeightLM σ X⟫_ℂ = (Kraus.mixedMapLM X Y σ).trace := by
  set S := CFC.sqrt σ
  have hS : Sᴴ = S := Matrix.conjTranspose_cfc_sqrt σ
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have h : ∀ i, X i * σ * (Y i)ᴴ = X i * S * (Y i * S)ᴴ := fun i => by
    rw [Matrix.conjTranspose_mul, hS, ← hSS]; simp only [Matrix.mul_assoc]
  rw [Kraus.mixedMapLM_apply, Matrix.trace_sum]
  simp_rw [h]
  simp only [PiLp.inner_apply, sqrtWeightLM, LinearMap.coe_mk, AddHom.coe_mk,
    RCLike.inner_apply, Fintype.sum_prod_type, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, mul_comm]

/-- The one-site periodic state `X ↦ φ_1(X)`, with coefficients `Tr Xⁱ`, as a linear map. -/
noncomputable def mpvStateOneLM {n : ℕ} : MPSTensor n D →ₗ[ℂ] MPVSpace n 1 where
  toFun X := mpvState X 1
  map_add' X Y := by
    ext s; simp [mpvState_apply, coeff_eq, List.ofFn_succ, Matrix.trace_add]
  map_smul' c X := by
    ext s; simp [mpvState_apply, coeff_eq, List.ofFn_succ, Matrix.trace_smul]

/-- For a unit vector `w`, `‖u‖² - |⟨w|u⟩|² ≤ ‖u - w‖²`. The squared distance of `u` from the
line through `w` is at most its squared distance from `w`. -/
theorem norm_sq_sub_norm_inner_sq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {w u : F} (hw : ‖w‖ = 1) :
    ‖u‖ ^ 2 - ‖⟪w, u⟫_ℂ‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, hw]
  have h1 : RCLike.re ⟪u, w⟫_ℂ ≤ ‖⟪w, u⟫_ℂ‖ := by
    rw [← inner_conj_symm, RCLike.conj_re]; exact RCLike.re_le_norm _
  nlinarith [sq_nonneg (1 - ‖⟪w, u⟫_ℂ‖)]

/-! ### The overlap to second order -/

open scoped Matrix.Norms.L2Operator in
/-- **Overlap of the positive part with the fixed point, to second order.** In the setting of
`exists_norm_polarPos_blockTensor_sub_le`, with `0 < γ < 1` and `x = e^{-γ/ξ}`, there is
`C > 0` such that for all `q` and all `M ≥ 2` with `C y < 1`, `y = M x^{2q} = M e^{-2γ q/ξ}`,
`1 - |⟨φ_M(P_∞)|φ_M(P_q)⟩| ≤ C y e^{C y}`.

Project result. It improves the first-order estimate of arXiv:2103.13367, Supplemental Material,
eq. (34) (cited as eq. (S29) there by arXiv:2307.01696), quoted as arXiv:2307.01696, eq. (S9)
(`exists_abs_one_sub_norm_mpvOverlap_polarPosTensor_le`), and the estimate of arXiv:2606.24475,
App. B4, eq. (S52), which is linear in the residual. The overlap
is `Tr τ_q^M` for the mixed transfer matrix `τ_q` of `P_q` against `P_∞`. Since `τ_∞` is the
rank-one idempotent `X ↦ Tr(X) σ`, `τ_∞ τ_q τ_∞ = α τ_∞` with `α = ⟨ι(P_∞)|ι(P_q)⟩` for the
vectors `ι(X) = (Xⁱ √σ)ᵢ` of norm one; hence `1 - |α| ≤ ‖ι(P_q) - ι(P_∞)‖²/2`, of second order.
Writing `τ_q = α (τ_∞ + Z)` with `τ_∞ Z τ_∞ = 0`, the trace of `(τ_∞ + Z)^M` is `1` up to second
order (`IsIdempotentElem.norm_trace_add_pow_sub_le_of_le`), and `|α|^M ≥ 1 - M (1 - |α|)`. -/
theorem exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ q M : ℕ, 2 ≤ M →
      C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) < 1 →
      1 - ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M‖ ≤
        C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) *
          Real.exp (C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q)) := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨Kt, hKt, hT⟩ := exists_norm_map_polarPosTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
    (transferMatrixLM ∘ₗ mixedMapLMLeft (fixedPointTensor σ))
  obtain ⟨Kι, hKι, hι⟩ := exists_norm_map_polarPosTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
    (sqrtWeightLM (n := D * D) σ)
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  set K₄ := ‖trL‖
  have hK₄ : 0 ≤ K₄ := norm_nonneg _
  have htrace : ∀ G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      ‖Matrix.traceAddMonoidHom (Fin D × Fin D) ℂ G‖ ≤ K₄ * ‖G‖ := trL.le_opNorm
  -- `τ_∞` is an idempotent of trace one, and `Tr E_{P_∞}(σ) = 1`.
  set τ := transferMatrix (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ))
    with hτdef
  have hτ : IsIdempotentElem τ :=
    isIdempotentElem_transferMatrix_fixedPointTensor hσ.posSemidef htr
  have hτtr : τ.trace = 1 := by
    have h := trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap (fixedPointTensor σ)
      (fixedPointTensor σ) 1
    rwa [pow_one, mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h
  have hfinf : (Kraus.mixedMapLM (fixedPointTensor σ) (fixedPointTensor σ) σ).trace = 1 := by
    rw [Kraus.mixedMapLM_self, show Kraus.mapLM (fixedPointTensor σ) σ = σ.trace • σ from
      transferMap_fixedPointTensor_apply hσ.posSemidef σ, Matrix.trace_smul, htr, one_smul]
  have hnorm1 : ∀ X : MPSTensor (D * D) D, (Kraus.mixedMapLM X X σ).trace = 1 →
      ‖sqrtWeightLM σ X‖ = 1 := fun X hX => by
    have h := inner_sqrtWeightLM hσ.posSemidef X X
    rw [hX, inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖sqrtWeightLM σ X‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h')
  -- The constants.
  set t₁ := ‖τ‖
  set t₂ := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) - τ‖
  set c₄ := 2 * (Kt + Kι * t₁)
  set c₅ := t₁ + t₂
  set zc := c₅ ^ 4 * c₄ ^ 2
  set E₀ := K₄ * (t₁ + 3 * t₂)
  have hzc : 0 ≤ zc := by positivity
  have hE₀ : 0 ≤ E₀ := by positivity
  set C := 1 + Kι ^ 2 + 4 * zc + 2 * E₀ * zc
  have hC0 : 0 ≤ 2 * E₀ * zc := by positivity
  have hC1 : Kι ^ 2 ≤ C := by simp only [C]; linarith
  have hC2 : 4 * zc ≤ C := by simp only [C]; nlinarith [sq_nonneg Kι]
  have hC3 : Kι ^ 2 + 2 * E₀ * zc ≤ C := by simp only [C]; linarith
  have hC4 : 2 * zc ≤ C := by linarith
  refine ⟨C, by positivity, fun q M hM2 hsmall => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  set δ := x ^ q with hδdef
  set y := (M : ℝ) * (x ^ 2) ^ q with hydef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ2 : (x ^ 2) ^ q = δ ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hy0 : 0 ≤ y := by positivity
  have hδy : δ ^ 2 ≤ y := by rw [← hδ2]; exact le_mul_of_one_le_left (by positivity) hM
  have hKιy : Kι ^ 2 * y < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hC1 hy0) hsmall
  have hzcy : 4 * zc * y < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hC2 hy0) hsmall
  -- Write `τ_q = α (τ_∞ + Z)` with `τ_∞ Z τ_∞ = 0`.
  set Pq := polarPosTensor (blockTensor A q) with hPq
  set T := transferMatrix (Kraus.mixedMapLM Pq (fixedPointTensor σ)) with hTdef
  set α := (Kraus.mixedMapLM Pq (fixedPointTensor σ) σ).trace with hαdef
  have hTτ : ‖T - τ‖ ≤ Kt * δ := hT q
  have hιd : ‖sqrtWeightLM σ Pq - sqrtWeightLM σ (fixedPointTensor σ)‖ ≤ Kι * δ := hι q
  have hιi := hnorm1 _ hfinf
  have hιq : ‖sqrtWeightLM σ Pq‖ = 1 := by
    refine hnorm1 _ ?_
    rw [Kraus.mixedMapLM_self, hPq]
    change (Kraus.transferMap (polarPosTensor (blockTensor A q)) σ).trace = 1
    rw [transferMap_polarPosTensor_blockTensor, Module.End.pow_apply,
      Function.iterate_fixed hfix, htr]
  have hαι : α = ⟪sqrtWeightLM σ (fixedPointTensor σ), sqrtWeightLM σ Pq⟫_ℂ :=
    (inner_sqrtWeightLM hσ.posSemidef Pq (fixedPointTensor σ)).symm
  -- `1 - |α| ≤ ‖ι(P_q) - ι(P_∞)‖² / 2` and `|1 - α| ≤ ‖ι(P_q) - ι(P_∞)‖`.
  have hre : 1 - ‖α‖ ≤ Kι ^ 2 * δ ^ 2 / 2 := by
    have h := @norm_sub_sq ℂ _ _ _ _ (sqrtWeightLM σ Pq) (sqrtWeightLM σ (fixedPointTensor σ))
    rw [hιq, hιi, ← inner_conj_symm, RCLike.conj_re, ← hαι] at h
    have h1 : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hιd 2
    rw [mul_pow] at h2
    have h3 : RCLike.re α = α.re := rfl
    linarith only [h, h1, h2, h3]
  have hα1 : ‖1 - α‖ ≤ Kι * δ := by
    have h : 1 - α = ⟪sqrtWeightLM σ (fixedPointTensor σ),
        sqrtWeightLM σ (fixedPointTensor σ) - sqrtWeightLM σ Pq⟫_ℂ := by
      rw [inner_sub_right, ← hαι, inner_sqrtWeightLM hσ.posSemidef, hfinf]
    rw [h]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hιi, one_mul, norm_sub_rev]
    exact hιd
  have hKιδ : Kι ^ 2 * δ ^ 2 ≤ Kι ^ 2 * y := mul_le_mul_of_nonneg_left hδy (sq_nonneg _)
  have hαhalf : 1 / 2 ≤ ‖α‖ := by linarith only [hre, hKιδ, hKιy]
  have hα0 : α ≠ 0 := by
    rintro h; rw [h, norm_zero] at hαhalf; norm_num at hαhalf
  set Z := α⁻¹ • T - τ with hZdef
  have hZ : τ * Z * τ = 0 := by
    have h := transferMatrix_fixedPointTensor_mul_mul hσ.posSemidef Pq (fixedPointTensor σ)
    rw [← hτdef, ← hTdef, ← hαdef] at h
    rw [hZdef, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, h, smul_smul,
      inv_mul_cancel₀ hα0, one_smul, hτ.eq, hτ.eq, sub_self]
  have hTZ : T = α • (τ + Z) := by
    rw [hZdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ hα0, one_smul]
  have hZn : ‖Z‖ ≤ c₄ * δ := by
    have h : Z = α⁻¹ • ((T - τ) + (1 - α) • τ) := by
      rw [hZdef, smul_add, sub_smul, one_smul, smul_sub, smul_sub, smul_smul,
        inv_mul_cancel₀ hα0, one_smul]
      abel
    rw [h, norm_smul, norm_inv]
    have h1 : ‖(T - τ) + (1 - α) • τ‖ ≤ Kt * δ + Kι * δ * t₁ :=
      (norm_add_le _ _).trans (add_le_add hTτ (by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right hα1 (norm_nonneg _)))
    have h2 : ‖α‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith only [hαhalf]) (by norm_num)]; linarith only [hαhalf]
    calc ‖α‖⁻¹ * ‖(T - τ) + (1 - α) • τ‖ ≤ 2 * (Kt * δ + Kι * δ * t₁) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)
      _ = c₄ * δ := by simp only [c₄]; ring
  -- The blocks of `Z` are bounded by `z = c₅² c₄ δ`, and `z ≤ 1/2`.
  set z := c₅ * (c₄ * δ) * c₅ with hzdef
  have hblock : ∀ a b : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ, ‖a‖ ≤ c₅ → ‖b‖ ≤ c₅ →
      ‖a * Z * b‖ ≤ z := fun a b ha hb =>
    (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul ha hZn
      (norm_nonneg _) (by positivity))) hb (norm_nonneg _) (by positivity))
  have ht₁ : t₁ ≤ c₅ := le_add_of_nonneg_right (norm_nonneg _)
  have ht₂ : t₂ ≤ c₅ := le_add_of_nonneg_left (norm_nonneg _)
  have hz2 : z ^ 2 = zc * δ ^ 2 := by simp only [z, zc]; ring
  have hz0 : 0 ≤ z := by positivity
  have hz : z ≤ 1 / 2 := by
    have h1 : zc * δ ^ 2 ≤ zc * y := mul_le_mul_of_nonneg_left hδy hzc
    have h2 : z ^ 2 < (1 / 2) ^ 2 := by rw [hz2]; linarith only [h1, hzcy]
    exact (pow_lt_pow_iff_left₀ hz0 (by norm_num) two_ne_zero).1 h2 |>.le
  have hpert := IsIdempotentElem.norm_trace_add_pow_sub_le_of_le hτ hZ
    (tr := Matrix.traceAddMonoidHom (Fin D × Fin D) ℂ) (fun a b => Matrix.trace_mul_comm a b)
    hK₄ htrace (hblock _ _ ht₂ ht₁) (hblock _ _ ht₁ ht₂) (hblock _ _ ht₂ ht₂) hz hM2
  simp only [Matrix.traceAddMonoidHom_apply, hτtr] at hpert
  have hMz : (M : ℝ) * (2 * z ^ 2) = 2 * zc * y := by
    rw [hz2, hydef, hδ2]; ring
  rw [hMz] at hpert
  -- `|⟨φ_M(P_∞)|φ_M(P_q)⟩| = |α|^M |Tr(τ_∞ + Z)^M| ≥ 1 - Kι² y/2 - E`.
  set Eb := E₀ * (2 * zc * y) * Real.exp (2 * zc * y) with hEb
  have hEb0 : 0 ≤ Eb := by positivity
  have ha : mpvOverlap Pq (fixedPointTensor σ) M = α ^ M * ((τ + Z) ^ M).trace := by
    rw [← trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap, ← hTdef, hTZ, smul_pow,
      Matrix.trace_smul, smul_eq_mul]
  have hpowα : 1 - Kι ^ 2 * y / 2 ≤ ‖α‖ ^ M := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ ‖α‖ - 1 by linarith only [hαhalf]) M
    rw [add_sub_cancel] at h
    have h1 : (M : ℝ) * (1 - ‖α‖) ≤ Kι ^ 2 * y / 2 := by
      calc (M : ℝ) * (1 - ‖α‖) ≤ M * (Kι ^ 2 * δ ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hre (by positivity)
        _ = Kι ^ 2 * (M * δ ^ 2) / 2 := by ring
        _ = Kι ^ 2 * y / 2 := by rw [hydef, hδ2]
    linarith only [h, h1]
  have htrZ : 1 - Eb ≤ ‖((τ + Z) ^ M).trace‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (((τ + Z) ^ M).trace)
    rw [norm_one, norm_sub_rev] at h
    have h' : ‖Matrix.trace ((τ + Z) ^ M) - 1‖ ≤ Eb := hpert
    linarith only [h, h']
  have hlow : 1 - ‖mpvOverlap Pq (fixedPointTensor σ) M‖ ≤ Kι ^ 2 * y / 2 + Eb := by
    rw [ha, norm_mul, norm_pow]
    have hp0 : 0 ≤ ‖α‖ ^ M := by positivity
    have hr0 : 0 ≤ ‖((τ + Z) ^ M).trace‖ := norm_nonneg _
    have hu0 : 0 ≤ Kι ^ 2 * y / 2 := by positivity
    by_cases h1 : 1 - Eb ≤ 0
    · nlinarith only [h1, hp0, hr0, hu0, mul_nonneg hp0 hr0]
    by_cases h2 : 1 - Kι ^ 2 * y / 2 ≤ 0
    · nlinarith only [h2, hEb0, mul_nonneg hp0 hr0]
    push Not at h1 h2
    nlinarith only [mul_le_mul hpowα htrZ h1.le hp0, hu0, hEb0, mul_nonneg hu0 hEb0]
  -- Conclusion.
  have hexp : 1 ≤ Real.exp (C * y) := Real.one_le_exp (by positivity)
  have hexp' : Real.exp (2 * zc * y) ≤ Real.exp (C * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC4 hy0)
  have h1 : Eb ≤ 2 * E₀ * zc * y * Real.exp (C * y) := by
    rw [hEb, show E₀ * (2 * zc * y) = 2 * E₀ * zc * y by ring]
    exact mul_le_mul_of_nonneg_left hexp' (by positivity)
  have h2 : Kι ^ 2 * y / 2 ≤ Kι ^ 2 * y * Real.exp (C * y) := by
    have : 0 ≤ Kι ^ 2 * y := by positivity
    nlinarith only [this, hexp]
  have h3 : (Kι ^ 2 + 2 * E₀ * zc) * y * Real.exp (C * y) ≤ C * y * Real.exp (C * y) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hy0) (by positivity)
  have h4 : Kι ^ 2 * y * Real.exp (C * y) + 2 * E₀ * zc * y * Real.exp (C * y) =
      (Kι ^ 2 + 2 * E₀ * zc) * y * Real.exp (C * y) := by ring
  linarith only [hlow, h1, h2, h3, h4]

/-- **One block, to second order.** In the setting of `exists_norm_polarPos_blockTensor_sub_le`,
with `0 < γ < 1` and `x = e^{-γ/ξ}`, there is `K ≥ 0` with
`‖φ_1(P_q)‖² - |⟨φ_1(P_∞)|φ_1(P_q)⟩|² ≤ K x^{2q}` for all `q`. The left side is at most
`‖φ_1(P_q) - φ_1(P_∞)‖²` since `φ_1(P_∞)` is a unit vector, and `φ_1` is linear. -/
theorem exists_norm_mpvState_sq_sub_norm_mpvOverlap_sq_le (A : MPSTensor d D)
    (hN : Kraus.IsNormal A) (hA : IsLeftCanonical A) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosDef) (htr : σ.trace = 1) (hfix : Kraus.transferMap A σ = σ) {lam₂ : ℂ}
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.transferMap A) μ → μ ≠ 1 → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖mpvState (polarPosTensor (blockTensor A q)) 1‖ ^ 2 -
          ‖mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) 1‖ ^ 2 ≤
        K * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q := by
  have := Matrix.neZero_of_trace_eq_one htr
  obtain ⟨Kμ, hKμ, hμ⟩ := exists_norm_map_polarPosTensor_sub_le A hN hA hσ htr hfix hlam hγ0 hγ
    (mpvStateOneLM (n := D * D) (D := D))
  refine ⟨Kμ ^ 2, by positivity, fun q => ?_⟩
  have hw : ‖mpvState (fixedPointTensor σ) 1‖ = 1 := by
    have h1 := ofReal_norm_mpvState_sq (fixedPointTensor σ) 1
    rw [mpvOverlap_fixedPointTensor_self hσ.posSemidef htr] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (Complex.ofReal_injective (by rw [h1]; simp))
  have haw : mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) 1 =
      ⟪mpvState (fixedPointTensor σ) 1, mpvState (polarPosTensor (blockTensor A q)) 1⟫_ℂ := by
    rw [mpvOverlap_eq_star_mpvInner, mpvInner]; exact inner_conj_symm _ _
  have hdist : ‖mpvState (polarPosTensor (blockTensor A q)) 1 -
      mpvState (fixedPointTensor σ) 1‖ ≤ Kμ * Real.exp (-γ / correlationLength lam₂) ^ q :=
    hμ q
  rw [haw]
  refine (norm_sq_sub_norm_inner_sq_le hw).trans ?_
  calc ‖mpvState (polarPosTensor (blockTensor A q)) 1 - mpvState (fixedPointTensor σ) 1‖ ^ 2
      ≤ (Kμ * Real.exp (-γ / correlationLength lam₂) ^ q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdist 2
    _ = Kμ ^ 2 * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]

end MPSTensor
