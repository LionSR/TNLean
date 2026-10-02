/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockOverlap
import TNLean.MPS.Preparation.RepeatedBlockSum

/-!
# Overlaps for repeated blocks with overlapping states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") write a tensor that is not normal as
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)). Its `q`-site blocked map is
`B = ∑ⱼ cⱼ B_j L_jᴴ`, with `cⱼ = (∑ₖ |μ_{j,k}|^{2q})^{1/2}` and the isometries `L_j` that place a
bond pair on all copies of block `j` (`TNLean.MPS.Preparation.RepeatedBlockSum`). This file proves
the estimates for the corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` when the `q`-site
states of distinct blocks overlap:

* the positive part `P` of `B` is close to `P_∞ = ∑ⱼ cⱼ L_j ((√σ_j)ᵀ ⊗ 1) L_jᴴ`,
  `‖P - P_∞‖ ≤ K e^{-γ q/ξ}` for `0 < γ < 1/2` and weights `|μ_{j,k}| ≤ 1`
  (`exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le`), from the Gram estimate
  `exists_norm_gram_sum_sub_le` and the Hölder bound `Matrix.norm_polarPos_sub_le_sqrt` shared
  with blocks of multiplicity one;
* `L_jᴴ P_∞ = ∑ₖ μ_{j,k}^q ((√σ_j)ᵀ ⊗ 1) K_{j,k}ᴴ` (`conjTranspose_copyIsometry_mul_copyPosLimit`),
  whose mixed transfer map against the fixed-point tensor of `σ_j` is
  `ρ ↦ ∑ₖ μ_{j,k}^q Tr(E_{j,k}ᴴ ρ) E_{j,k} σ_j` (`mixedMapLM_copyPosLimitRow_apply`): a combination
  of orthogonal rank-one idempotents of trace one, whose `M`-th power has trace
  `βⱼ = ∑ₖ μ_{j,k}^{qM}`;
* the telescoping estimate for tensors of different bond dimensions, shared with blocks of
  multiplicity one (`exists_norm_mpvOverlap_sub_trace_pow_le`), then gives
  `|⟨Ω_j|φ_M(L_jᴴ P)⟩ - βⱼ| ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`
  (`exists_norm_mpvOverlap_sub_bntWeight_le_of_norm_sub_copyPosLimitRow_le`).

**Local fix (rate of the overlapping blocks):** the rate includes the correlation lengths of the
mixed transfer maps of distinct blocks, in place of the block form (S5) and the rate
`e^{-γ q/ξ_diag}` of the source. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Local fix (corrected fixed-point state):** the fixed-point state is the corrected state
`∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` of eq. (S7). Documented in
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSTensor.copyPosLimit`, `MPSTensor.copyPosLimitRow` — the limit `P_∞` and its rows `L_jᴴ P_∞`.
* `MPSTensor.exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le` — the rate of `P → P_∞`.
* `MPSTensor.mixedMapLM_copyPosLimitRow_apply` — the mixed transfer map of `L_jᴴ P_∞`.
* `MPSTensor.exists_norm_mpvOverlap_sub_bntWeight_le_of_norm_sub_copyPosLimitRow_le` — the
  overlaps of one block.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and the proof of Lemma 1'(ii).
* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*,
  arXiv:2103.13367, Supplemental Material, eq. (26) and eqs. `final_eq` to `finished`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The limit of the positive parts -/

/-- The row `L_jᴴ P_∞ = ∑ₖ μ_{j,k}^q ((√σ_j)ᵀ ⊗ 1) K_{j,k}ᴴ` of the limit of the positive parts of
the blocked direct sum with multiplicities (`conjTranspose_copyIsometry_mul_copyPosLimit`): the
fixed-point tensor of block `j`, read from the bond pairs of each copy with the weight of the copy
on `q` sites (arXiv:2307.01696, Supplemental Material, eq. (S5), corrected as in
`TNLean.MPS.Preparation.RepeatedBlockSum`, in the limit `q → ∞`). -/
noncomputable def copyPosLimitRow (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D)
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j : Fin b) :
    Matrix (Fin (Dj j) × Fin (Dj j)) (Fin D × Fin D) ℂ :=
  ∑ k, μ j k ^ q • (((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
    (pairEmbedding (ι j k))ᴴ)

/-- The limit `P_∞ = ∑ⱼ cⱼ L_j ((√σ_j)ᵀ ⊗ 1) L_jᴴ` of the positive parts of the `q`-site blocked
direct sum with multiplicities, with `cⱼ = copyNorm μ q j` and `L_j = copyIsometry ι μ q j`: the
corrected block form `P = ∑ⱼ cⱼ L_j P_j L_jᴴ` of arXiv:2307.01696, Supplemental Material,
eq. (S5) (`polarPos_blockTensor_repeatedBlockSum`) with each `P_j` replaced by its limit. -/
noncomputable def copyPosLimit (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D)
    (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ j, (copyNorm μ q j : ℂ) • (copyIsometry ι μ q j *
    ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (copyIsometry ι μ q j)ᴴ)

variable {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

section Limit

variable (hι : ∀ j k, Function.Injective (ι j k))
  (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
include hι hdisj

/-- `L_jᴴ P_∞ = ∑ₖ μ_{j,k}^q ((√σ_j)ᵀ ⊗ 1) K_{j,k}ᴴ` for blocks with nonzero weights. -/
theorem conjTranspose_copyIsometry_mul_copyPosLimit (μ : CopyWeights b m) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (j : Fin b) :
    (copyIsometry ι μ q j)ᴴ * copyPosLimit ι μ q σ = copyPosLimitRow ι μ q σ j := by
  set Y : (j : Fin b) → Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j) × Fin (Dj j)) ℂ :=
    fun j => (CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)
  have hc0 : (copyNorm μ q j : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (copyNorm_pos (μ.weight_fun_ne_zero j) q).ne'
  have h := conjTranspose_mul_sum_of_isometry
    (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)
    (fun j k h => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h)
    (fun k => (copyNorm μ q k : ℂ) • (Y k * (copyIsometry ι μ q k)ᴴ)) j
  have hP : copyPosLimit ι μ q σ = ∑ k, copyIsometry ι μ q k *
      ((copyNorm μ q k : ℂ) • (Y k * (copyIsometry ι μ q k)ᴴ)) := by
    simp only [copyPosLimit, Matrix.mul_smul, Matrix.mul_assoc, Y]
  rw [hP, h, ← Matrix.mul_smul, conjTranspose_copyIsometry, Finset.smul_sum, Matrix.mul_sum,
    copyPosLimitRow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, mul_div_cancel₀ _ hc0, Matrix.mul_smul]

omit hι hdisj in
/-- `P_∞` is positive semidefinite. -/
theorem posSemidef_copyPosLimit (μ : CopyWeights b m) (q : ℕ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    (copyPosLimit ι μ q σ).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun j _ => ?_
  refine (Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _).smul
    (Complex.zero_le_real.2 (Real.sqrt_nonneg _))
  exact (Matrix.posSemidef_transpose_iff.2
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (σ j)))).kronecker Matrix.PosSemidef.one

/-- `P_∞² = ∑ⱼ cⱼ² L_j (σ_jᵀ ⊗ 1) L_jᴴ`, the limit of the Gram matrices. -/
theorem copyPosLimit_mul_self (μ : CopyWeights b m) (q : ℕ)
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef) :
    copyPosLimit ι μ q σ * copyPosLimit ι μ q σ =
      ∑ j, ((‖(copyNorm μ q j : ℂ)‖ ^ 2 : ℝ) : ℂ) • (copyIsometry ι μ q j *
        ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (copyIsometry ι μ q j)ᴴ) := by
  have hP : ∀ (t : Fin b → ℂ) (Y : (j : Fin b) →
      Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j) × Fin (Dj j)) ℂ),
      ∑ j, t j • (copyIsometry ι μ q j * Y j * (copyIsometry ι μ q j)ᴴ) =
        ∑ j, copyIsometry ι μ q j * (t j • Y j) * (copyIsometry ι μ q j)ᴴ := fun t Y => by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [copyPosLimit, hP, sum_mul_conjTranspose_mul_sum_of_isometry
    (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)
    (fun j k h => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h), hP]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [smul_mul_smul_comm, ← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.transpose_mul,
    CFC.sqrt_mul_sqrt_self (σ j) (hσ j).nonneg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ copyNorm μ q j from Real.sqrt_nonneg _)]
  congr 1
  push_cast
  ring

end Limit

/-! ### The rate of the positive part -/

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

open scoped Matrix.Norms.L2Operator in
/-- **Rate of the positive part for blocks with multiplicities.** Let the blocks `A_j` be normal
in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, and let `λ₂` with
`|λ₂| < 1` bound the moduli of the eigenvalues other than `1` of every `E_{A_j}` and of all
eigenvalues of the mixed transfer maps `E_{jj'}` of distinct blocks. For `0 < γ < 1/2` there is
`K` such that for all weights with `|μ_{j,k}| ≤ 1` the positive part `P` of the `q`-site blocked
direct sum `⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_j` satisfies `‖P - P_∞‖ ≤ K e^{-γ q/ξ}` for
`q ≥ 1`, with `P_∞ = ∑ⱼ cⱼ L_j ((√σ_j)ᵀ ⊗ 1) L_jᴴ` (`copyPosLimit`).

The Gram estimate `exists_norm_gram_sum_sub_le` applies to `B = ∑ⱼ cⱼ B_j L_jᴴ` with
`cⱼ ≤ (∑ⱼ m_j)^{1/2}`, and the Hölder bound `Matrix.norm_polarPos_sub_le_sqrt` (arXiv:2103.13367,
Supplemental Material, eq. (26)) halves the rate `e^{-2γ q/ξ}` of the Gram matrices. -/
theorem exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : CopyWeights b m, (∀ j k, ‖μ j k‖ ≤ 1) → ∀ q : ℕ, q ≠ 0 →
      ‖Matrix.polarPos (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q)) -
        copyPosLimit ι μ q σ‖ ≤ K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, hG⟩ := exists_norm_gram_sum_sub_le (D := D) hN hA hσ htr hfix hl hlam hmix
    (by linarith : 0 < 2 * γ) (by linarith : 2 * γ < 1)
  set R := Real.sqrt (∑ j, (m j : ℝ))
  refine ⟨R * Real.sqrt K, by positivity, fun μ hμ q hq => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hc : ∀ j, ‖(copyNorm μ q j : ℂ)‖ ≤ R := fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ copyNorm μ q j from Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt (show ∑ k, ‖μ j k‖ ^ (2 * q) ≤ ∑ j, (m j : ℝ) from ?_)
    calc ∑ k, ‖μ j k‖ ^ (2 * q) ≤ ∑ _k : Fin (m j), (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => pow_le_one₀ (norm_nonneg _) (hμ j k)
      _ = (m j : ℝ) := by simp
      _ ≤ ∑ j, (m j : ℝ) := Finset.single_le_sum (f := fun j => (m j : ℝ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
  have h := hG R (fun j => (copyNorm μ q j : ℂ)) (copyIsometry ι μ q) hc
    (fun j => Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
      (conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)) q
  rw [← physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hq,
    ← copyPosLimit_mul_self hι hdisj μ q fun j => (hσ j).posSemidef] at h
  have hhol := Matrix.norm_polarPos_sub_le_sqrt
    (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q))
    (posSemidef_copyPosLimit (ι := ι) μ q σ)
  have hx2 : Real.exp (-(2 * γ) / correlationLength lam₂) ^ q = (x ^ q) ^ 2 := by
    rw [exp_neg_two_mul_div_correlationLength, ← pow_mul, ← pow_mul, mul_comm]
  refine hhol.trans ?_
  calc _ ≤ Real.sqrt (R ^ 2 * K * (x ^ q) ^ 2) := by gcongr; rw [← hx2]; exact h
    _ = R * Real.sqrt K * x ^ q := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (pow_nonneg (Real.exp_pos _).le q)]

/-! ### The mixed transfer map of the limit -/

/-- The letter of the tensor read from `((√σ)ᵀ ⊗ 1) K_ιᴴ` is `E_ι (√σ |l⟩⟨r|) E_ιᴴ`: the letter of
the fixed-point tensor placed on the bond coordinates `ι`. -/
private theorem ofPhysicalMatrixLM_transpose_kronecker_mul_pairEmbedding {D' : ℕ}
    (ι' : Fin D' → Fin D) (σ : Matrix (Fin D') (Fin D') ℂ) (i : Fin (D' * D')) :
    ofPhysicalMatrixLM (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) *
        (pairEmbedding ι')ᴴ) i =
      coordEmbedding ι' * fixedPointTensor σ i * (coordEmbedding ι')ᴴ := by
  have hG : ((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) * (pairEmbedding ι')ᴴ =
      (coordEmbedding ι' * CFC.sqrt σ)ᵀ ⊗ₖ (coordEmbedding ι')ᴴ := by
    rw [pairEmbedding, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, conjTranspose_coordEmbedding, ← Matrix.transpose_mul]
  ext a c
  change (((CFC.sqrt σ)ᵀ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) * (pairEmbedding ι')ᴴ)
    (virtualPairEquiv D' i) (a, c) = _
  rw [hG, transpose_kronecker_apply_eq_mul_single_mul]
  simp only [fixedPointTensor, virtualPairEquiv, Matrix.mul_assoc]

/-- The mixed transfer map of the tensor read from `((√σ)ᵀ ⊗ 1) K_ιᴴ` against the fixed-point
tensor of `σ` is `ρ ↦ Tr(E_ιᴴ ρ) E_ι σ`. -/
private theorem mixedMapLM_ofPhysicalMatrixLM_pairEmbedding_apply {D' : ℕ} (ι' : Fin D' → Fin D)
    {σ : Matrix (Fin D') (Fin D') ℂ} (hσ : σ.PosSemidef) (ρ : Matrix (Fin D) (Fin D') ℂ) :
    Kraus.mixedMapLM (ofPhysicalMatrixLM (((CFC.sqrt σ)ᵀ ⊗ₖ
        (1 : Matrix (Fin D') (Fin D') ℂ)) * (pairEmbedding ι')ᴴ)) (fixedPointTensor σ) ρ =
      ((coordEmbedding ι')ᴴ * ρ).trace • (coordEmbedding ι' * σ) := by
  rw [Kraus.mixedMapLM_apply]
  simp_rw [ofPhysicalMatrixLM_transpose_kronecker_mul_pairEmbedding]
  calc ∑ i, coordEmbedding ι' * fixedPointTensor σ i * (coordEmbedding ι')ᴴ * ρ *
        (fixedPointTensor σ i)ᴴ
      = coordEmbedding ι' * Kraus.transferMap (fixedPointTensor σ)
          ((coordEmbedding ι')ᴴ * ρ) := by
        rw [Kraus.transferMap_apply, Matrix.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [transferMap_fixedPointTensor_apply hσ, Matrix.mul_smul]

/-- The rank-one map `ρ ↦ Tr(E_ιᴴ ρ) E_ι σ` on matrices from the bond space of the direct sum to
that of a block. -/
private noncomputable def copyFixedProj {D' : ℕ} (ι' : Fin D' → Fin D)
    (σ : Matrix (Fin D') (Fin D') ℂ) : Module.End ℂ (Matrix (Fin D) (Fin D') ℂ) :=
  ((Matrix.traceLinearMap (Fin D') ℂ ℂ) ∘ₗ
    mulLeftLinearMap (n := Fin D') (R := ℂ) (coordEmbedding ι')ᴴ).smulRight
      (coordEmbedding ι' * σ)

private theorem copyFixedProj_apply {D' : ℕ} (ι' : Fin D' → Fin D)
    (σ : Matrix (Fin D') (Fin D') ℂ) (ρ : Matrix (Fin D) (Fin D') ℂ) :
    copyFixedProj ι' σ ρ = ((coordEmbedding ι')ᴴ * ρ).trace • (coordEmbedding ι' * σ) := rfl

/-- The maps `R_k` of distinct copies of a block multiply to zero, and each is idempotent. -/
private theorem copyFixedProj_mul {D' : ℕ} {m' : ℕ} {ι' : Fin m' → Fin D' → Fin D}
    (hι' : ∀ k, Function.Injective (ι' k)) (hdisj' : ∀ k k', k ≠ k' → ∀ a a', ι' k a ≠ ι' k' a')
    {σ : Matrix (Fin D') (Fin D') ℂ} (htr : σ.trace = 1) (k k' : Fin m') :
    copyFixedProj (ι' k) σ * copyFixedProj (ι' k') σ =
      if k = k' then copyFixedProj (ι' k) σ else 0 := by
  ext1 ρ
  rw [Module.End.mul_apply, copyFixedProj_apply, copyFixedProj_apply, Matrix.mul_smul,
    Matrix.trace_smul, ← Matrix.mul_assoc]
  split_ifs with h
  · subst h
    rw [conjTranspose_coordEmbedding_mul_self (hι' k), Matrix.one_mul, htr, smul_eq_mul, mul_one,
      copyFixedProj_apply]
  · rw [conjTranspose_coordEmbedding_mul_eq_zero (hdisj' k k' h), Matrix.zero_mul,
      Matrix.trace_zero, smul_zero, zero_smul, LinearMap.zero_apply]

private theorem trace_copyFixedProj {D' : ℕ} {ι' : Fin D' → Fin D} (hι' : Function.Injective ι')
    {σ : Matrix (Fin D') (Fin D') ℂ} (htr : σ.trace = 1) :
    LinearMap.trace ℂ (Matrix (Fin D) (Fin D') ℂ) (copyFixedProj ι' σ) = 1 := by
  rw [copyFixedProj, LinearMap.trace_smulRight]
  simp only [LinearMap.comp_apply, mulLeftLinearMap_apply, Matrix.traceLinearMap_apply]
  rw [← Matrix.mul_assoc, conjTranspose_coordEmbedding_mul_self hι', Matrix.one_mul, htr]

/-- Powers of a combination `∑ₖ aₖ R_k` of the maps of the copies are `∑ₖ aₖⁿ R_k`, `n ≥ 1`. -/
private theorem sum_smul_copyFixedProj_pow {D' : ℕ} {m' : ℕ} {ι' : Fin m' → Fin D' → Fin D}
    (hι' : ∀ k, Function.Injective (ι' k)) (hdisj' : ∀ k k', k ≠ k' → ∀ a a', ι' k a ≠ ι' k' a')
    {σ : Matrix (Fin D') (Fin D') ℂ} (htr : σ.trace = 1) (a : Fin m' → ℂ) (n : ℕ) :
    (∑ k, a k • copyFixedProj (ι' k) σ) ^ (n + 1) =
      ∑ k, a k ^ (n + 1) • copyFixedProj (ι' k) σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single k]
    · rw [smul_mul_smul_comm, copyFixedProj_mul hι' hdisj' htr, ← pow_succ]
      simp
    · intro k' _ hk'
      rw [smul_mul_smul_comm, copyFixedProj_mul hι' hdisj' htr]
      simp [Ne.symm hk']
    · simp

section Mixed

variable (hι : ∀ j k, Function.Injective (ι j k))
  (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
include hι hdisj

omit hι hdisj in
/-- **The mixed transfer map of the limit row.** The mixed transfer map of the tensor read from
`L_jᴴ P_∞ = ∑ₖ μ_{j,k}^q ((√σ_j)ᵀ ⊗ 1) K_{j,k}ᴴ` against the fixed-point tensor of `σ_j` is
`ρ ↦ ∑ₖ μ_{j,k}^q Tr(E_{j,k}ᴴ ρ) E_{j,k} σ_j` (compare `E_{P_∞} = |ρ⟩⟨1|` in arXiv:2307.01696,
eq. `eq:B_TM`, and `mixedMapLM_blockSumPosLimit_smul_apply` for multiplicity one). -/
theorem mixedMapLM_copyPosLimitRow_apply (μ : (j : Fin b) → Fin (m j) → ℂ) (q : ℕ)
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (j : Fin b) (ρ : Matrix (Fin D) (Fin (Dj j)) ℂ) :
    Kraus.mixedMapLM (ofPhysicalMatrixLM (copyPosLimitRow ι μ q σ j)) (fixedPointTensor (σ j)) ρ =
      ∑ k, μ j k ^ q • (((coordEmbedding (ι j k))ᴴ * ρ).trace •
        (coordEmbedding (ι j k) * σ j)) := by
  have hlin : ∀ G : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin D × Fin D) ℂ,
      Kraus.mixedMapLM (ofPhysicalMatrixLM G) (fixedPointTensor (σ j)) =
        mixedMapLMLeft (D₁ := D) (fixedPointTensor (σ j)) (ofPhysicalMatrixLM G) := fun _ => rfl
  rw [hlin, copyPosLimitRow, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, ← hlin,
    mixedMapLM_ofPhysicalMatrixLM_pairEmbedding_apply _ (hσ j)]

open scoped Matrix.Norms.L2Operator in
/-- **The overlap of one block near the limit.** For blocks with multiplicities placed on
disjoint bond coordinates, positive semidefinite `σ_j` of trace one, and a block `j` with at
least one copy, there is `C > 0` such that the following holds for all weights with
`|μ_{j,k}| ≤ 1`, all `q`, all `δ`, and all `M ≥ 1`. Let `G` be a matrix from the bond pairs of the
direct sum to those of block `j` with `‖G - L_jᴴ P_∞‖ ≤ δ` (`copyPosLimitRow`). Then the overlap of
the tensor read from `G` with the fixed-point tensor of `σ_j` on `M` sites is
`βⱼ = ∑ₖ μ_{j,k}^{qM}` up to `C (M δ) e^{C M δ}`.

The mixed transfer map of the limit is `∑ₖ μ_{j,k}^q R_k` with orthogonal rank-one idempotents
`R_k` of trace one (`mixedMapLM_copyPosLimitRow_apply`), so its powers are bounded uniformly in
the weights and its `M`-th power has trace `βⱼ`; the telescoping estimate
`exists_norm_mpvOverlap_sub_trace_pow_le` applies. -/
theorem exists_norm_mpvOverlap_sub_bntWeight_le_of_norm_sub_copyPosLimitRow_le
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (j : Fin b) (hm : 0 < m j) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : (j : Fin b) → Fin (m j) → ℂ, (∀ k, ‖μ j k‖ ≤ 1) →
      ∀ (q : ℕ) (G : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin D × Fin D) ℂ) (δ : ℝ) (M : ℕ)
        [NeZero M], ‖G - copyPosLimitRow ι μ q σ j‖ ≤ δ →
      ‖mpvOverlap (ofPhysicalMatrixLM G) (fixedPointTensor (σ j)) M - bntWeight μ (M * q) j‖ ≤
        C * (M * δ) * Real.exp (C * (M * δ)) := by
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero D := ⟨fun h => by subst h; exact (ι j ⟨0, hm⟩ 0).elim0⟩
  have hι' : ∀ k, Function.Injective (ι j k) := hι j
  have hdisj' : ∀ k k', k ≠ k' → ∀ a a', ι j k a ≠ ι j k' a' := fun k k' h =>
    hdisj ⟨j, k⟩ ⟨j, k'⟩ fun h' => h (eq_of_heq (Sigma.mk.inj h').2)
  set R : Fin (m j) → Module.End ℂ (Matrix (Fin D) (Fin (Dj j)) ℂ) :=
    fun k => copyFixedProj (ι j k) (σ j)
  set c : ℝ := 1 + ∑ k, ‖LinearMap.toContinuousLinearMap (R k)‖
  have hc : 0 ≤ c := by positivity
  obtain ⟨C, hC, hgen⟩ := exists_norm_mpvOverlap_sub_trace_pow_le (D₁ := D)
    (fixedPointTensor (σ j)) hc
  refine ⟨C, hC, fun μ hμ q G δ M _ hG => ?_⟩
  have hT : Kraus.mixedMapLM (ofPhysicalMatrixLM (copyPosLimitRow ι μ q σ j))
      (fixedPointTensor (σ j)) = ∑ k, μ j k ^ q • R k := by
    ext1 ρ
    rw [mixedMapLM_copyPosLimitRow_apply μ q hσ j ρ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply]
    rfl
  have hpow : ∀ (k : ℕ) (ρ : Matrix (Fin D) (Fin (Dj j)) ℂ),
      ‖(Kraus.mixedMapLM (ofPhysicalMatrixLM (copyPosLimitRow ι μ q σ j))
        (fixedPointTensor (σ j)) ^ k) ρ‖ ≤ c * ‖ρ‖ := fun k ρ => by
    rw [hT]
    rcases k with _ | n
    · rw [pow_zero, Module.End.one_apply]
      exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right (by positivity))
    · rw [sum_smul_copyFixedProj_pow hι' hdisj' (htr j), LinearMap.sum_apply]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k, ‖(μ j k ^ q) ^ (n + 1) • R k ρ‖
          ≤ ∑ k, ‖LinearMap.toContinuousLinearMap (R k)‖ * ‖ρ‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_smul]
            have h1 : ‖(μ j k ^ q) ^ (n + 1)‖ ≤ 1 := by
              rw [norm_pow, norm_pow]
              exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) (hμ k))
            calc ‖(μ j k ^ q) ^ (n + 1)‖ * ‖R k ρ‖ ≤ 1 * ‖R k ρ‖ := by gcongr
              _ ≤ _ := by
                rw [one_mul]
                exact (LinearMap.toContinuousLinearMap (R k)).le_opNorm ρ
        _ = (∑ k, ‖LinearMap.toContinuousLinearMap (R k)‖) * ‖ρ‖ := by rw [Finset.sum_mul]
        _ ≤ c * ‖ρ‖ := by gcongr; exact le_add_of_nonneg_left zero_le_one
  have htrace : LinearMap.trace ℂ (Matrix (Fin D) (Fin (Dj j)) ℂ)
      (Kraus.mixedMapLM (ofPhysicalMatrixLM (copyPosLimitRow ι μ q σ j))
        (fixedPointTensor (σ j)) ^ M) = bntWeight μ (M * q) j := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
    rw [hT, hn, sum_smul_copyFixedProj_pow hι' hdisj' (htr j), map_sum, bntWeight]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, trace_copyFixedProj (hι' k) (htr j), smul_eq_mul, mul_one, ← pow_mul,
      mul_comm q]
  have h := hgen G _ δ M hpow hG
  rwa [htrace] at h

end Mixed

end MPSTensor
