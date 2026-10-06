/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IdempotentTracePerturbation
import TNLean.MPS.Preparation.OverlappingBlockError
import TNLean.MPS.Preparation.PolarCompression

/-!
# Overlaps of blocks with overlapping states, to second order

Let `Aⁱ = ⊕ⱼ A_jⁱ` be the direct sum, with unit weights, of normal blocks `A_j` in the gauge
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, placed on the bond coordinates
`ι_j`, and let `P` be the positive part of the `q`-site blocked tensor. This file proves that the
overlaps `zⱼ = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` of `P` with the fixed-point tensors `P'_{j,∞}` of the blocks,
placed in the full bond space, are `1` up to second order in `‖P - P_∞‖`:
`|zⱼ - 1| ≤ C y e^{C y}` with `y = M e^{-2γ q/ξ}`, for every `0 < γ < 1`, `q ≥ 1`, `M ≥ 2` and
`C y < 1`
(`exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le_sq`; vacuous for `λ₂ = 0`, where the
convention `ξ = 0` makes `e^{-γ/ξ} = 1`). Here `ξ = -1/log|λ₂|`, where `λ₂`
bounds the moduli of the eigenvalues other than `1` of the transfer maps `E_{jj}` of the blocks and
the moduli of all eigenvalues of the mixed transfer maps `E_{jj'}`, `j ≠ j'`.

The first-order estimate `exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le` gives
`y = M e^{-γ q/ξ}`. The positive part `P` converges to `P_∞` only to first order in the overlaps
`e^{-q/ξ_{jj'}}` of distinct blocks, through its blocks between distinct blocks; the overlaps `zⱼ`
see these blocks only to second order. The argument is that of
`exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq` for one normal tensor, with the idempotent
`R_j : ρ ↦ Tr(Π_j ρ) σ'_j` (`mixedMapLM_blockSumPosLimit_apply`) in place of `X ↦ Tr(X) σ`:

* `R_j τ R_j = α R_j` for the mixed transfer matrix `τ` of `P` against `P'_{j,∞}`, with
  `α = ⟨ι(P'_{j,∞})|ι(P)⟩` for the vectors `ι(X) = (Xⁱ √σ'_j)ᵢ`
  (`mixedTransferMatrixLeft_blockSumPosLimit_mul_mul`);
* both vectors have norm one: `‖ι(P)‖² = Tr E_A^q(σ'_j) = 1` because `σ'_j` is a fixed point of the
  transfer map of the direct sum (`transferMap_blockSum_embeddedBlockState`); hence
  `1 - Re α = ‖ι(P) - ι(P'_{j,∞})‖²/2`, and `ι(P'_{j,∞}) = ι(P_∞)`;
* `α` is real, `α = Tr(P ((√σ'_j)ᵀ ⊗ σ'_j))` with `P` Hermitian
  (`trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor`);
* `IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq` then bounds `zⱼ = Tr τ^M`.

**Scope restriction (multiplicity one, unit weights):** every block occurs once, with weight `1`.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor`,
  `MPSTensor.im_trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor` — the compression coefficient
  as a trace, and its reality for Hermitian `P`.
* `MPSTensor.transferMap_blockSum_embeddedBlockState` — the fixed points of the blocks are fixed
  points of the direct sum.
* `MPSTensor.isIdempotentElem_mixedTransferMatrixLeft_blockSumPosLimit`,
  `MPSTensor.mixedTransferMatrixLeft_blockSumPosLimit_mul_mul` — `R_j` is idempotent with trace
  one, and `R_j τ R_j = α R_j`.
* `MPSTensor.exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le_sq` — the overlaps of the
  blocks to second order, `M ≥ 2`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and the proof of Lemma 1'(ii).
* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*,
  arXiv:2103.13367, Supplemental Material, eq. (34) (the first-order overlap estimate).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal InnerProductSpace
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### The compression coefficient -/

/-! ### The fixed points of the blocks -/

variable {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- `E X Eᴴ Π = E X Eᴴ` for the projector `Π = E Eᴴ` of an injective `ι`. -/
theorem embeddedBlockState_mul_coordEmbedding_mul_conjTranspose {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) (X : Matrix (Fin D') (Fin D') ℂ) :
    embeddedBlockState ι X * (coordEmbedding ι * (coordEmbedding ι)ᴴ) = embeddedBlockState ι X := by
  rw [embeddedBlockState]
  calc coordEmbedding ι * X * (coordEmbedding ι)ᴴ * (coordEmbedding ι * (coordEmbedding ι)ᴴ)
      = coordEmbedding ι * X * ((coordEmbedding ι)ᴴ * coordEmbedding ι) *
          (coordEmbedding ι)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [conjTranspose_coordEmbedding_mul_self hι, Matrix.mul_one]

/-- The letters of the direct sum with unit weights act on the coordinates of block `j` as the
letters of `A_j`: `Aⁱ E_j = E_j A_jⁱ`. -/
theorem blockSum_mul_coordEmbedding (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (j : Fin b) (i : Fin d) :
    blockSum Aj ι (fun _ => 1) i * coordEmbedding (ι j) = coordEmbedding (ι j) * Aj j i := by
  rw [blockSum, Matrix.sum_mul, Finset.sum_eq_single j]
  · rw [one_smul, Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self (hι j), Matrix.mul_one]
  · intro k _ hk
    rw [one_smul, Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_eq_zero (hdisj k j hk),
      Matrix.mul_zero]
  · simp

/-- **The fixed points of the blocks are fixed by the direct sum.** For blocks placed with
orthogonal ranges, the transfer map of the direct sum with unit weights acts on `E_j X E_jᴴ` as the
transfer map of block `j`: `E_A(E_j X E_jᴴ) = E_j E_{A_j}(X) E_jᴴ`. In particular the fixed point
`σ'_j = E_j σ_j E_jᴴ` of block `j` in the full bond space is a fixed point of `E_A`. -/
theorem transferMap_blockSum_embeddedBlockState (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (j : Fin b)
    (X : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    Kraus.transferMap (blockSum Aj ι fun _ => 1) (embeddedBlockState (ι j) X) =
      embeddedBlockState (ι j) (Kraus.transferMap (Aj j) X) := by
  have h : ∀ i, blockSum Aj ι (fun _ => 1) i * embeddedBlockState (ι j) X *
      (blockSum Aj ι (fun _ => 1) i)ᴴ =
        coordEmbedding (ι j) * (Aj j i * X * (Aj j i)ᴴ) * (coordEmbedding (ι j))ᴴ := fun i => by
    have h1 := blockSum_mul_coordEmbedding (Aj := Aj) hι hdisj j i
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h2
    calc blockSum Aj ι (fun _ => 1) i * embeddedBlockState (ι j) X *
          (blockSum Aj ι (fun _ => 1) i)ᴴ
        = (blockSum Aj ι (fun _ => 1) i * coordEmbedding (ι j)) * X *
            ((coordEmbedding (ι j))ᴴ * (blockSum Aj ι (fun _ => 1) i)ᴴ) := by
          simp only [embeddedBlockState, Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc]
  rw [Kraus.transferMap_apply, Kraus.transferMap_apply]
  simp_rw [h]
  rw [embeddedBlockState, Matrix.mul_sum, Matrix.sum_mul]

/-! ### The idempotent of the limit -/

/-- A linear map `R : ρ ↦ Tr(Q ρ) σ` compresses every linear map `T` to a multiple of itself:
`R T R = Tr(Q T(σ)) R`, on transfer matrices. -/
theorem transferMatrix_mul_mul_of_eq_trace_smul
    {R : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {Q σ : Matrix (Fin D) (Fin D) ℂ} (hR : ∀ ρ, R ρ = (Q * ρ).trace • σ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    transferMatrix R * transferMatrix T * transferMatrix R =
      (Q * T σ).trace • transferMatrix R := by
  rw [← transferMatrix_comp, ← transferMatrix_comp]
  have hs : (Q * T σ).trace • transferMatrix R = transferMatrix ((Q * T σ).trace • R) :=
    (map_smul (transferMatrixLM (D := D)) (Q * T σ).trace R).symm
  rw [hs]
  congr 1
  ext ρ : 1
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hR, map_smul, smul_smul, mul_comm]

/-- If `√σ Q = √σ`, the mixed transfer maps against the fixed-point tensor of `σ` take values on
which `Tr(Q ·)` is the trace. -/
theorem trace_mul_mixedMapLM_fixedPointTensor {Q σ : Matrix (Fin D) (Fin D) ℂ}
    (hQ : CFC.sqrt σ * Q = CFC.sqrt σ) (X : MPSTensor (D * D) D) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (Q * Kraus.mixedMapLM X (fixedPointTensor σ) ρ).trace =
      (Kraus.mixedMapLM X (fixedPointTensor σ) ρ).trace := by
  rw [Matrix.trace_mul_comm, Kraus.mixedMapLM_apply, Matrix.sum_mul]
  refine congrArg Matrix.trace (Finset.sum_congr rfl fun i _ => ?_)
  rw [fixedPointTensor, Matrix.conjTranspose_mul, Matrix.conjTranspose_cfc_sqrt]
  simp only [Matrix.mul_assoc, hQ]

variable (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
  {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
include hι hdisj

/-- **The idempotent of the limit.** The mixed transfer matrix `R_j` of the limit `P_∞` against
the fixed-point tensor of block `j`, placed in the full bond space, is idempotent with trace one. -/
theorem isIdempotentElem_mixedTransferMatrixLeft_blockSumPosLimit (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (j : Fin b) :
    IsIdempotentElem (mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
      (blockSumPosLimit ι σ)) ∧
    (mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
      (blockSumPosLimit ι σ)).trace = 1 := by
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero D := ⟨fun h => by subst h; exact (ι j 0).elim0⟩
  have hR := mixedMapLM_blockSumPosLimit_apply hι hdisj hσ j
  have h1 := (trace_coordEmbedding_mul_conjTranspose_mul_embeddedBlockState hι j).trans (htr j)
  refine ⟨?_, ?_⟩
  · change transferMatrix _ * transferMatrix _ = transferMatrix _
    rw [← transferMatrix_comp]
    exact congrArg transferMatrix (isIdempotentElem_of_apply_eq_trace_smul hR h1).eq
  · change (transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrixLM (blockSumPosLimit ι σ))
      (fixedPointTensor (embeddedBlockState (ι j) (σ j))))).trace = 1
    rw [trace_transferMatrix_eq_linearMap_trace, trace_of_apply_eq_trace_smul hR, h1]

/-- **Compression by the idempotent of the limit.** For every `D² × D²` matrix `H`, the mixed
transfer matrix `τ` of the tensor read from `H` against the fixed-point tensor `P'_{j,∞}` of block
`j` satisfies `R_j τ R_j = α R_j` with `α = Tr(∑ᵢ Hⁱ σ'_j (P'^i_{j,∞})†)`. -/
theorem mixedTransferMatrixLeft_blockSumPosLimit_mul_mul (hσ : ∀ j, (σ j).PosSemidef) (j : Fin b)
    (H : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
        (blockSumPosLimit ι σ) *
      mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j))) H *
      mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
        (blockSumPosLimit ι σ) =
    (Kraus.mixedMapLM (ofPhysicalMatrixLM H) (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
        (embeddedBlockState (ι j) (σ j))).trace •
      mixedTransferMatrixLeft (fixedPointTensor (embeddedBlockState (ι j) (σ j)))
        (blockSumPosLimit ι σ) := by
  have hR := mixedMapLM_blockSumPosLimit_apply hι hdisj hσ j
  have h := transferMatrix_mul_mul_of_eq_trace_smul hR
    (Kraus.mixedMapLM (ofPhysicalMatrixLM H) (fixedPointTensor (embeddedBlockState (ι j) (σ j))))
  have hQ : CFC.sqrt (embeddedBlockState (ι j) (σ j)) *
      (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ) =
        CFC.sqrt (embeddedBlockState (ι j) (σ j)) := by
    rw [show CFC.sqrt (embeddedBlockState (ι j) (σ j)) = embeddedBlockState (ι j) (CFC.sqrt (σ j))
      from cfc_sqrt_coordEmbedding_mul_mul (hι j) (hσ j),
      embeddedBlockState_mul_coordEmbedding_mul_conjTranspose (hι j)]
  rw [trace_mul_mixedMapLM_fixedPointTensor hQ] at h
  exact h

omit hι hdisj in
/-- A vector that is the limit, at a geometric rate, of vectors whose norms converge to `c` at a
geometric rate has norm `c`. -/
theorem norm_eq_of_forall_abs_norm_sub_le_pow {F : Type*} [NormedAddCommGroup F] {v : F}
    {u : ℕ → F} {c K K' x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hu : ∀ q, q ≠ 0 → |‖u q‖ - c| ≤ K' * x ^ q)
    (hv : ∀ q, q ≠ 0 → ‖u q - v‖ ≤ K * x ^ q) : ‖v‖ = c := by
  have hlim : Filter.Tendsto (fun q : ℕ => (K + K') * x ^ (q + 1)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp
      (Filter.tendsto_add_atTop_nat 1) |>.const_mul (K + K')
  refine eq_of_abs_sub_nonpos (ge_of_tendsto' hlim fun q => ?_)
  calc |‖v‖ - c| ≤ |‖v‖ - ‖u (q + 1)‖| + |‖u (q + 1)‖ - c| := abs_sub_le _ _ _
    _ ≤ ‖v - u (q + 1)‖ + K' * x ^ (q + 1) :=
        add_le_add (abs_norm_sub_norm_le _ _) (hu _ q.succ_ne_zero)
    _ = ‖u (q + 1) - v‖ + K' * x ^ (q + 1) := by rw [norm_sub_rev]
    _ ≤ K * x ^ (q + 1) + K' * x ^ (q + 1) := by gcongr; exact hv _ q.succ_ne_zero
    _ = (K + K') * x ^ (q + 1) := by ring

/-! ### The overlaps of the blocks to second order -/

open scoped Matrix.Norms.L2Operator in
/-- **The overlap of one block, to second order.** In the setting of
`exists_norm_polarPos_blockTensor_blockSum_sub_le`, with `0 < γ < 1` and `x = e^{-γ/ξ}`, the
overlap `zⱼ = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` of the positive part `P` of the `q`-site blocked direct sum
with unit weights with the fixed-point tensor of block `j`, placed in the full bond space, satisfies
`|zⱼ - 1| ≤ C y e^{C y}` with `y = M x^{2q} = M e^{-2γ q/ξ}`, for `q ≥ 1`, `M ≥ 2` and `C y < 1`.
The bound has content only for `λ₂ ≠ 0`: for `λ₂ = 0` the convention `correlationLength 0 = 0`
gives `x = 1`, and `C y < 1` fails for `M ≥ 2`, so the statement is vacuous.

Project result; compare the first-order estimate
`exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le`, with `y = M e^{-γ q/ξ}`, and
arXiv:2103.13367, Supplemental Material, eq. (34). The mixed transfer matrix `τ` of `P` against
`P'_{j,∞}` is compressed by the idempotent `R_j` of the limit to `α R_j`
(`mixedTransferMatrixLeft_blockSumPosLimit_mul_mul`), with `α = ⟨ι(P'_{j,∞})|ι(P)⟩` real and
`1 - α = ‖ι(P) - ι(P'_{j,∞})‖²/2` of second order, and
`IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq` bounds `zⱼ = Tr τ^M`. -/
theorem exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le_sq
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j)) (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) (j : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q M : ℕ, q ≠ 0 → 2 ≤ M →
      C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) < 1 →
      ‖mpvOverlap (polarPosTensor (blockTensor (blockSum Aj ι fun _ => 1) q))
          (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M - 1‖ ≤
        C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q) *
          Real.exp (C * (M * (Real.exp (-γ / correlationLength lam₂) ^ 2) ^ q)) := by
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero D := ⟨fun h => by subst h; exact (ι j 0).elim0⟩
  have hσs : ∀ k, (σ k).PosSemidef := fun k => (hσ k).posSemidef
  set σ' := embeddedBlockState (ι j) (σ j) with hσ'def
  have hσ' : σ'.PosSemidef := (hσs j).mul_mul_conjTranspose_same _
  have htr' : σ'.trace = 1 := (trace_embeddedBlockState (hι j) (σ j)).trans (htr j)
  set F := fixedPointTensor σ' with hFdef
  set A := blockSum Aj ι fun _ => 1
  set x := Real.exp (-γ / correlationLength lam₂) with hxdef
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  rcases eq_or_ne lam₂ 0 with h0 | h0
  · -- For `λ₂ = 0` the rate is `x = 1`, and `C y < 1` fails for `C = 1` and `M ≥ 2`.
    have hx : x = 1 := by rw [hxdef, neg_div_correlationLength, h0]; simp
    refine ⟨1, one_pos, fun q M _ hM2 hsmall => absurd hsmall ?_⟩
    rw [hx, one_pow, one_pow, mul_one, one_mul, not_lt]
    exact_mod_cast (show 1 ≤ M by omega)
  have hx1 : x < 1 := by
    rw [hxdef, neg_div_correlationLength, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg hγ0 (Real.log_neg (norm_pos_iff.2 h0) hl)
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_blockSum_sub_le hι hdisj hN hA hσ
    htr hfix hl hlam hmix hγ0 hγ
  -- The linear maps `Ψ` (mixed transfer matrices) and `ι` (the vectors `(Xⁱ √σ'_j)ᵢ`).
  set Ψ := mixedTransferMatrixLeft F
  set Kt := ‖LinearMap.toContinuousLinearMap Ψ‖
  have hΨ : ∀ G, ‖Ψ G‖ ≤ Kt * ‖G‖ := (LinearMap.toContinuousLinearMap Ψ).le_opNorm
  set ιL := sqrtWeightLM (n := D * D) σ' ∘ₗ ofPhysicalMatrixLM
  set Kι := ‖LinearMap.toContinuousLinearMap ιL‖
  have hιL : ∀ G, ‖ιL G‖ ≤ Kι * ‖G‖ := (LinearMap.toContinuousLinearMap ιL).le_opNorm
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  have htrace : ∀ G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      ‖Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ G‖ ≤ ‖trL‖ * ‖G‖ := trL.le_opNorm
  -- The idempotent `R_j` of the limit.
  set Pinf := blockSumPosLimit ι σ
  set R := Ψ Pinf
  obtain ⟨hRi, hRtr⟩ := isIdempotentElem_mixedTransferMatrixLeft_blockSumPosLimit hι hdisj hσs htr j
  obtain ⟨C₀, hC₀, hG⟩ := IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq hRi
    (tr := Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ) (fun a b => Matrix.trace_mul_comm a b)
    (norm_nonneg _) htrace hRtr
  -- `ι(P_q)` and `ι(P'_{j,∞})` are unit vectors, and `ι(P_∞) = ι(P'_{j,∞})`.
  have hιF : ‖sqrtWeightLM σ' F‖ = 1 :=
    norm_sqrtWeightLM_fixedPointTensor hσ' htr'
  have hιq : ∀ q : ℕ,
      ‖ιL (Matrix.polarPos (physicalMatrix (blockTensor A q)))‖ = 1 := fun q => by
    refine norm_sqrtWeightLM_eq_one hσ' ?_
    change (Kraus.transferMap (polarPosTensor (blockTensor A q)) σ').trace = 1
    rw [transferMap_polarPosTensor_blockTensor, Module.End.pow_apply,
      Function.iterate_fixed (by
        rw [hσ'def, transferMap_blockSum_embeddedBlockState hι hdisj j, hfix j])]
    exact htr'
  have hιinf : ιL Pinf = sqrtWeightLM σ' F := by
    have hn : ‖ιL Pinf‖ = 1 := norm_eq_of_forall_abs_norm_sub_le_pow (K' := 0) hx0 hx1
      (fun q _ => by rw [hιq q, sub_self, abs_zero, zero_mul])
      (fun q hq => by
        rw [← map_sub]
        exact (hιL _).trans (by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hpos q hq) (norm_nonneg _)))
    have hinner : ⟪sqrtWeightLM σ' F, ιL Pinf⟫_ℂ = 1 := by
      change ⟪sqrtWeightLM σ' F, sqrtWeightLM σ' (ofPhysicalMatrixLM Pinf)⟫_ℂ = 1
      rw [inner_sqrtWeightLM hσ', mixedMapLM_blockSumPosLimit_apply hι hdisj hσs j,
        Matrix.trace_smul, trace_coordEmbedding_mul_conjTranspose_mul_embeddedBlockState hι j,
        htr j, one_smul]
      exact htr'
    have h := @norm_sub_sq ℂ _ _ _ _ (ιL Pinf) (sqrtWeightLM σ' F)
    rw [hn, hιF, ← inner_conj_symm, hinner, map_one, RCLike.one_re] at h
    exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (ιL Pinf - sqrtWeightLM σ' F)]))
  -- The constants.
  set K' := Kt * K₁ + Kι * K₁
  have hK' : 0 ≤ K' := by positivity
  refine ⟨C₀ * K' ^ 2 + 1, by positivity, fun q M hq hM2 hsmall => ?_⟩
  set H := Matrix.polarPos (physicalMatrix (blockTensor A q))
  set δ := K' * x ^ q with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hHd : ‖H - Pinf‖ ≤ K₁ * x ^ q := hpos q hq
  have hT : ‖Ψ H - R‖ ≤ δ := by
    rw [← map_sub]
    refine (hΨ _).trans ?_
    calc Kt * ‖H - Pinf‖ ≤ Kt * (K₁ * x ^ q) := mul_le_mul_of_nonneg_left hHd (norm_nonneg _)
      _ ≤ δ := by
        simp only [δ, K']
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap ιL)) hK₁)
          (pow_nonneg hx0 q)]
  have hιd : ‖ιL H - sqrtWeightLM σ' F‖ ≤ Kι * K₁ * x ^ q := by
    rw [← hιinf, ← map_sub, mul_assoc]
    exact (hιL _).trans (mul_le_mul_of_nonneg_left hHd (norm_nonneg _))
  -- The compression coefficient `α = ⟨ι(P'_{j,∞})|ι(P)⟩` is real, at most `1`, and `1 - α` is of
  -- second order.
  set αc := (Kraus.mixedMapLM (ofPhysicalMatrixLM H) F σ').trace with hαcdef
  have hαι : αc = ⟪sqrtWeightLM σ' F, ιL H⟫_ℂ := (inner_sqrtWeightLM hσ' _ F).symm
  have hHerm : H.IsHermitian := Matrix.conjTranspose_cfc_sqrt _
  have him : αc.im = 0 :=
    im_trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor hHerm hσ'.isHermitian
  have hαre : αc = (αc.re : ℂ) := (Complex.ext rfl (by simp [him]))
  have hα1 : αc.re ≤ 1 := by
    rw [hαι]
    exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (by rw [hιF, hιq q, one_mul]))
  have hαsq : 1 - αc.re ≤ δ ^ 2 := by
    have h := one_sub_re_inner_eq_norm_sub_sq_div_two (𝕜 := ℂ) hιF (hιq q)
    rw [← hαι, norm_sub_rev] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hιd 2
    have h3 : (Kι * K₁ * x ^ q) ^ 2 ≤ δ ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      simp only [δ, K']
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap Ψ)) hK₁)
        (pow_nonneg hx0 q)]
    have h4 : RCLike.re αc = αc.re := rfl
    nlinarith only [h, h2, h3, h4]
  have hcomp : R * Ψ H * R = (αc.re : ℂ) • R := by
    rw [← hαre]
    exact mixedTransferMatrixLeft_blockSumPosLimit_mul_mul hι hdisj hσs j H
  -- Conclusion.
  have hy : (M : ℝ) * δ ^ 2 = K' ^ 2 * (M * (x ^ 2) ^ q) := by
    simp only [δ]; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]; ring
  set y := (M : ℝ) * (x ^ 2) ^ q
  have hy0 : 0 ≤ y := by positivity
  have hsmall' : C₀ * (M * δ ^ 2) < 1 := by
    rw [hy]
    calc C₀ * (K' ^ 2 * y) = C₀ * K' ^ 2 * y := by ring
      _ ≤ (C₀ * K' ^ 2 + 1) * y := mul_le_mul_of_nonneg_right (by linarith) hy0
      _ < 1 := hsmall
  have h := hG (Ψ H) αc.re δ M hM2 hcomp hT hα1 hαsq hsmall'
  have hover : Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (Ψ H ^ M) =
      mpvOverlap (polarPosTensor (blockTensor A q)) F M :=
    trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap _ _ M
  rw [hover, hy] at h
  refine h.trans ?_
  have hC : C₀ * K' ^ 2 ≤ C₀ * K' ^ 2 + 1 := by linarith
  calc C₀ * (K' ^ 2 * y) * Real.exp (C₀ * (K' ^ 2 * y))
      = C₀ * K' ^ 2 * y * Real.exp (C₀ * K' ^ 2 * y) := by ring_nf
    _ ≤ (C₀ * K' ^ 2 + 1) * y * Real.exp ((C₀ * K' ^ 2 + 1) * y) := by
        have h0 : 0 ≤ C₀ * K' ^ 2 := by positivity
        gcongr

end MPSTensor
