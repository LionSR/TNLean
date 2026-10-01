/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockGram
import TNLean.MPS.Preparation.OrthogonalBlockError

/-!
# Overlaps for a direct sum of blocks with overlapping states

This file collects the ingredients of the approximation error of arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), for a direct sum `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` of normal blocks
whose `q`-site states need not be orthogonal. The approximating state of eq. (S7) is
`V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩`; after `V^{⊗M}` its overlap with the target is a
combination of the overlaps `zⱼ = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` of the positive part `P` of the whole
blocked tensor with the fixed-point tensors `P'_{j,∞}` of the blocks placed in the full bond
space. The results are:

* the partial isometry `V^{⊗M}` does not increase norms
  (`sum_norm_sq_tensorPower_mulVec_le`), so the normalization of the approximating state can only
  increase the overlap;
* the mixed transfer matrix of the limit `P_∞` against `P'_{j,∞}` is the rank-one idempotent
  `ρ ↦ Tr(Π_j ρ) σ'_j` (`mixedMapLM_blockSumPosLimit_apply`), and `t_j` times it for the limit
  `∑ₖ t_k K_k ((√σ_k)ᵀ ⊗ 1) K_kᴴ` with weights `t_k ≥ 0`
  (`mixedMapLM_blockSumPosLimit_smul_apply`), so `zⱼ` is `t_j^M` up to the telescoping error of
  `‖P - P_∞‖` (`exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le`, and
  `exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le` for unit weights);
* the norm of the target is `∑ⱼ |μⱼ^N|²` up to the self-overlaps of the blocks and the overlaps of
  distinct blocks, which decay at the rate of the mixed transfer maps
  (`exists_abs_norm_mpvState_blockSum_weight_sq_sub_le`, and
  `exists_abs_norm_mpvState_blockSum_sq_sub_le` for unit weights).

**Scope restriction (multiplicity one):** every block occurs once.
`exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le` and
`exists_abs_norm_mpvState_blockSum_sq_sub_le` are stated for unit weights `μⱼ = 1`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Local fix (rate of the overlapping blocks):** the overlaps `zⱼ` and the norm of the target
are estimated at the rate `e^{-γ/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`, which includes the
correlation lengths of the mixed transfer maps, in place of the block form (S5) and the rate
`e^{-γ/ξ_diag}` of the source. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.embeddedBlockState` — the fixed point `σ'_j = E_j σ_j E_jᴴ` in the full bond space.
* `Matrix.sum_star_tensorPower_mulVec_mul`, `Matrix.sum_norm_sq_tensorPower_mulVec_le` —
  inner products and norms after a tensor power of a partial isometry.
* `MPSTensor.embedPair_fixedPointPair` — embedded pairs are the pairs of the embedded fixed points.
* `MPSTensor.mixedMapLM_blockSumPosLimit_smul_apply`, `MPSTensor.mixedMapLM_blockSumPosLimit_apply`
* `MPSTensor.exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le`,
  `MPSTensor.exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le`
* `MPSTensor.exists_norm_mpvOverlap_le_of_mixedMapLM` — overlaps of distinct blocks decay.
* `MPSTensor.exists_abs_norm_mpvState_blockSum_weight_sq_sub_le`,
  `MPSTensor.exists_abs_norm_mpvState_blockSum_sq_sub_le`

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7) and the proof of Lemma 1'(ii).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### The fixed points of the blocks in the full bond space -/

/-- A coordinate isometry has real entries: `E_ιᴴ = E_ιᵀ`. -/
theorem conjTranspose_coordEmbedding {D' : ℕ} (ι : Fin D' → Fin D) :
    (coordEmbedding ι)ᴴ = (coordEmbedding ι)ᵀ := by
  ext a x
  by_cases h : x = ι a <;> simp [coordEmbedding, conjTranspose_apply, h]

/-- The entries of `E_ι X E_ιᴴ`. -/
private theorem coordEmbedding_mul_mul_conjTranspose_apply {D' : ℕ} (ι : Fin D' → Fin D)
    (X : Matrix (Fin D') (Fin D') ℂ) (x y : Fin D) :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) x y =
      ∑ a, ∑ c, if x = ι a ∧ y = ι c then X a c else 0 := by
  simp only [mul_apply, coordEmbedding, conjTranspose_apply, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : x = ι a <;> by_cases h2 : y = ι c <;> simp [h1, h2]

/-- `(E_ι X E_ιᴴ)_{ι a, ι c} = X_{a c}` for an injective `ι`. -/
private theorem coordEmbedding_mul_mul_conjTranspose_apply_self {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) (X : Matrix (Fin D') (Fin D') ℂ) (a c : Fin D') :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) (ι a) (ι c) = X a c := by
  rw [coordEmbedding_mul_mul_conjTranspose_apply, Finset.sum_eq_single a, Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    exact ite_eq_right_iff.2 fun h => absurd (hι h.2).symm hc'
  · simp
  · intro a' _ ha'
    exact Finset.sum_eq_zero fun c' _ => ite_eq_right_iff.2 fun h => absurd (hι h.1).symm ha'
  · simp

/-- `E_ι X E_ιᴴ` vanishes off the range of `ι`. -/
private theorem coordEmbedding_mul_mul_conjTranspose_apply_eq_zero {D' : ℕ} (ι : Fin D' → Fin D)
    (X : Matrix (Fin D') (Fin D') ℂ) {x y : Fin D} (h : x ∉ Set.range ι ∨ y ∉ Set.range ι) :
    (coordEmbedding ι * X * (coordEmbedding ι)ᴴ) x y = 0 := by
  rw [coordEmbedding_mul_mul_conjTranspose_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 ?_
  rintro ⟨rfl, rfl⟩
  rcases h with h | h
  · exact absurd ⟨a, rfl⟩ h
  · exact absurd ⟨c, rfl⟩ h

/-- `√(E σ Eᴴ) = E √σ Eᴴ` for a coordinate isometry `E`. -/
private theorem cfc_sqrt_coordEmbedding_mul_mul {D' : ℕ} {ι : Fin D' → Fin D}
    (hι : Function.Injective ι) {σ : Matrix (Fin D') (Fin D') ℂ} (hσ : σ.PosSemidef) :
    CFC.sqrt (coordEmbedding ι * σ * (coordEmbedding ι)ᴴ) =
      coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ := by
  refine CFC.sqrt_unique ?_ ((Matrix.nonneg_iff_posSemidef.1
    (CFC.sqrt_nonneg σ)).mul_mul_conjTranspose_same _).nonneg
  calc coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ *
        (coordEmbedding ι * CFC.sqrt σ * (coordEmbedding ι)ᴴ)
      = coordEmbedding ι * (CFC.sqrt σ * ((coordEmbedding ι)ᴴ * coordEmbedding ι) *
          CFC.sqrt σ) * (coordEmbedding ι)ᴴ := by simp only [Matrix.mul_assoc]
    _ = coordEmbedding ι * σ * (coordEmbedding ι)ᴴ := by
        rw [conjTranspose_coordEmbedding_mul_self hι, Matrix.mul_one,
          CFC.sqrt_mul_sqrt_self σ hσ.nonneg]

/-- The fixed point `σ' = E_ι σ E_ιᴴ` of a block, placed in the full bond space along `ι`. -/
noncomputable def embeddedBlockState {D' : ℕ} (ι : Fin D' → Fin D)
    (σ : Matrix (Fin D') (Fin D') ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  coordEmbedding ι * σ * (coordEmbedding ι)ᴴ

private theorem posSemidef_embeddedBlockState {D' : ℕ} (ι : Fin D' → Fin D)
    {σ : Matrix (Fin D') (Fin D') ℂ} (hσ : σ.PosSemidef) :
    (embeddedBlockState ι σ).PosSemidef :=
  hσ.mul_mul_conjTranspose_same _

private theorem trace_embeddedBlockState {D' : ℕ} {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    (σ : Matrix (Fin D') (Fin D') ℂ) : (embeddedBlockState ι σ).trace = σ.trace := by
  rw [embeddedBlockState, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    conjTranspose_coordEmbedding_mul_self hι, Matrix.one_mul]

/-- The pair of a block embedded along `ι` is the pair of the embedded fixed point:
`ι_* ω(σ) = ω(E σ Eᴴ)`. -/
theorem embedPair_fixedPointPair {D' : ℕ} {ι : Fin D' → Fin D} (hι : Function.Injective ι)
    {σ : Matrix (Fin D') (Fin D') ℂ} (hσ : σ.PosSemidef) :
    embedPair ι (fixedPointPair σ) = fixedPointPair (embeddedBlockState ι σ) := by
  funext p
  rw [fixedPointPair, embeddedBlockState, cfc_sqrt_coordEmbedding_mul_mul hι hσ]
  by_cases hp : p.1 ∈ Set.range ι ∧ p.2 ∈ Set.range ι
  · obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := hp
    rcases p with ⟨x, y⟩
    simp only at ha hc
    subst ha hc
    rw [embedPair_apply hι, coordEmbedding_mul_mul_conjTranspose_apply_self hι]
    rfl
  · rw [embedPair_eq_zero _ (not_and_or.1 hp),
      coordEmbedding_mul_mul_conjTranspose_apply_eq_zero _ _ (not_and_or.1 hp)]

/-- `K (Xᵀ ⊗ 1) Kᴴ = (E X Eᴴ)ᵀ ⊗ (E Eᴴ)` for `K = E ⊗ E`. -/
private theorem pairEmbedding_mul_transpose_kronecker_one_mul {D' : ℕ} (ι : Fin D' → Fin D)
    (X : Matrix (Fin D') (Fin D') ℂ) :
    pairEmbedding ι * (Xᵀ ⊗ₖ (1 : Matrix (Fin D') (Fin D') ℂ)) * (pairEmbedding ι)ᴴ =
      (coordEmbedding ι * X * (coordEmbedding ι)ᴴ)ᵀ ⊗ₖ
        (coordEmbedding ι * (coordEmbedding ι)ᴴ) := by
  rw [pairEmbedding, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.transpose_mul, Matrix.transpose_mul,
    conjTranspose_coordEmbedding, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

variable {Dj : Fin b → ℕ} {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- The limit `P_∞` in terms of the embedded roots: `P_∞ = ∑ⱼ (E_j √σ_j E_jᴴ)ᵀ ⊗ Π_j` with
`Π_j = E_j E_jᴴ`. -/
private theorem blockSumPosLimit_eq_sum_kronecker
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    blockSumPosLimit ι σ = ∑ j, (embeddedBlockState (ι j) (CFC.sqrt (σ j)))ᵀ ⊗ₖ
      (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ) := by
  simp only [blockSumPosLimit, pairEmbedding_mul_transpose_kronecker_one_mul, embeddedBlockState]

/-- The entries of `Xᵀ ⊗ Y` read as letters: at the physical pair `(l, r)` the letter is
`X |l⟩⟨r| Y`. -/
theorem transpose_kronecker_apply_eq_mul_single_mul {α β γ δ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (X : Matrix α β ℂ) (Y : Matrix γ δ ℂ) (l : β) (r : γ) (a : α)
    (c : δ) :
    (Xᵀ ⊗ₖ Y) (l, r) (a, c) = (X * Matrix.single l r (1 : ℂ) * Y) a c := by
  rw [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single l]
  · rw [Matrix.single_mul_apply_same, one_mul]
  · intro f _ hf
    rw [Matrix.single_mul_apply_of_ne (h := hf), mul_zero]
  · simp

/-- `∑_{(l, r)} |l⟩⟨r| X |r⟩⟨l| = Tr X · 1`. -/
private theorem sum_single_mul_mul_conjTranspose_single (X : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin (D * D), Matrix.single (virtualPairEquiv D i).1 (virtualPairEquiv D i).2 (1 : ℂ) *
        X * (Matrix.single (virtualPairEquiv D i).1 (virtualPairEquiv D i).2 (1 : ℂ))ᴴ =
      X.trace • 1 := by
  rw [← (virtualPairEquiv D).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  have h : ∀ l r : Fin D, Matrix.single l r (1 : ℂ) * X * (Matrix.single l r (1 : ℂ))ᴴ =
      X r r • Matrix.single l l (1 : ℂ) := fun l r => by
    rw [Matrix.conjTranspose_single, Matrix.single_mul_mul_single, Matrix.smul_single]
    simp
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, Matrix.sum_single_one, ← Finset.sum_smul]
  rfl

/-- `√(t² σ) = t √σ` for `t ≥ 0`. -/
private theorem cfc_sqrt_ofReal_sq_smul {D' : ℕ} {σ : Matrix (Fin D') (Fin D') ℂ}
    (hσ : σ.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt ((((t ^ 2 : ℝ)) : ℂ) • σ) = (t : ℂ) • CFC.sqrt σ := by
  refine CFC.sqrt_unique ?_ (smul_nonneg (Complex.zero_le_real.2 ht) (CFC.sqrt_nonneg σ))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
  push_cast
  ring_nf

/-! ### The mixed transfer matrices of the limit -/

section Limit

variable (hι : ∀ j, Function.Injective (ι j))
  (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
  {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
include hι hdisj

/-- The embedded roots `r_j = E_j √σ_j E_jᴴ` multiply as `r_k r_j = δ_{kj} σ'_j`. -/
private theorem embeddedBlockState_sqrt_mul (hσ : ∀ j, (σ j).PosSemidef) (k j : Fin b) :
    embeddedBlockState (ι k) (CFC.sqrt (σ k)) * embeddedBlockState (ι j) (CFC.sqrt (σ j)) =
      if k = j then embeddedBlockState (ι j) (σ j) else 0 := by
  unfold embeddedBlockState
  split_ifs with h
  · subst h
    calc coordEmbedding (ι k) * CFC.sqrt (σ k) * (coordEmbedding (ι k))ᴴ *
          (coordEmbedding (ι k) * CFC.sqrt (σ k) * (coordEmbedding (ι k))ᴴ)
        = coordEmbedding (ι k) * (CFC.sqrt (σ k) * ((coordEmbedding (ι k))ᴴ *
            coordEmbedding (ι k)) * CFC.sqrt (σ k)) * (coordEmbedding (ι k))ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [conjTranspose_coordEmbedding_mul_self (hι k), Matrix.mul_one,
            CFC.sqrt_mul_sqrt_self (σ k) (hσ k).nonneg]
  · calc coordEmbedding (ι k) * CFC.sqrt (σ k) * (coordEmbedding (ι k))ᴴ *
          (coordEmbedding (ι j) * CFC.sqrt (σ j) * (coordEmbedding (ι j))ᴴ)
        = coordEmbedding (ι k) * (CFC.sqrt (σ k) * ((coordEmbedding (ι k))ᴴ *
            coordEmbedding (ι j)) * CFC.sqrt (σ j)) * (coordEmbedding (ι j))ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [conjTranspose_coordEmbedding_mul_eq_zero (hdisj k j h)]
          simp

omit hdisj in
/-- `Tr(Π_j σ'_j) = Tr σ_j`. -/
private theorem trace_coordEmbedding_mul_conjTranspose_mul_embeddedBlockState (j : Fin b) :
    (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ * embeddedBlockState (ι j) (σ j)).trace =
      (σ j).trace := by
  rw [← trace_embeddedBlockState (hι j) (σ j), embeddedBlockState]
  congr 1
  calc coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ *
        (coordEmbedding (ι j) * σ j * (coordEmbedding (ι j))ᴴ)
      = coordEmbedding (ι j) * ((coordEmbedding (ι j))ᴴ * coordEmbedding (ι j)) * σ j *
          (coordEmbedding (ι j))ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [conjTranspose_coordEmbedding_mul_self (hι j), Matrix.mul_one]

/-- **The mixed transfer map of the weighted limit.** For weights `t_k ≥ 0`, the mixed transfer
map of `P_∞ = ∑ₖ t_k K_k ((√σ_k)ᵀ ⊗ 1) K_kᴴ`, written as `∑ₖ K_k ((√(t_k² σ_k))ᵀ ⊗ 1) K_kᴴ`,
against the fixed-point tensor `P'_{j,∞}` of block `j`, placed in the full bond space, is
`ρ ↦ t_j Tr(Π_j ρ) σ'_j`, where `Π_j = E_j E_jᴴ` and `σ'_j = E_j σ_j E_jᴴ` (compare
`E_{P_∞} = |ρ⟩⟨1|` in arXiv:2307.01696, eq. `eq:B_TM`). -/
theorem mixedMapLM_blockSumPosLimit_smul_apply (hσ : ∀ j, (σ j).PosSemidef) (t : Fin b → ℝ)
    (ht : ∀ k, 0 ≤ t k) (j : Fin b) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.mixedMapLM
        (ofPhysicalMatrixLM (blockSumPosLimit ι fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k))
        (fixedPointTensor (embeddedBlockState (ι j) (σ j))) ρ =
      (t j : ℂ) • ((coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ * ρ).trace •
        embeddedBlockState (ι j) (σ j)) := by
  set r : (k : Fin b) → Matrix (Fin D) (Fin D) ℂ :=
    fun k => embeddedBlockState (ι k) (CFC.sqrt (σ k))
  set Q : (k : Fin b) → Matrix (Fin D) (Fin D) ℂ :=
    fun k => coordEmbedding (ι k) * (coordEmbedding (ι k))ᴴ
  set s : Fin (D * D) → Matrix (Fin D) (Fin D) ℂ :=
    fun i => Matrix.single (virtualPairEquiv D i).1 (virtualPairEquiv D i).2 (1 : ℂ)
  have hletter : ∀ i, ofPhysicalMatrixLM
      (blockSumPosLimit ι fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k) i =
        ∑ k, (t k : ℂ) • (r k * s i * Q k) := by
    intro i
    ext a c
    change (blockSumPosLimit ι fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k)
      (virtualPairEquiv D i) (a, c) = _
    rw [blockSumPosLimit_eq_sum_kronecker, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cfc_sqrt_ofReal_sq_smul (hσ k) (ht k), embeddedBlockState, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.transpose_smul, Matrix.smul_kronecker, Matrix.smul_apply,
      Matrix.smul_apply]
    exact congrArg _ (transpose_kronecker_apply_eq_mul_single_mul _ _ (virtualPairEquiv D i).1
      (virtualPairEquiv D i).2 a c)
  have hfix : ∀ i, fixedPointTensor (embeddedBlockState (ι j) (σ j)) i = r j * s i := by
    intro i
    change CFC.sqrt (embeddedBlockState (ι j) (σ j)) * _ = _
    rw [embeddedBlockState, cfc_sqrt_coordEmbedding_mul_mul (hι j) (hσ j)]
    rfl
  have hrH : (r j)ᴴ = r j := by
    simp only [r, embeddedBlockState, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_cfc_sqrt, Matrix.mul_assoc]
  rw [Kraus.mixedMapLM_apply]
  simp_rw [hletter, hfix, Matrix.conjTranspose_mul, hrH, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hk : ∀ k, ∑ i, (t k : ℂ) • (r k * s i * Q k) * ρ * ((s i)ᴴ * r j) =
      (t k : ℂ) • ((Q k * ρ).trace • (r k * r j)) := fun k => by
    calc ∑ i, (t k : ℂ) • (r k * s i * Q k) * ρ * ((s i)ᴴ * r j)
        = (t k : ℂ) • (r k * (∑ i, s i * (Q k * ρ) * (s i)ᴴ) * r j) := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (t k : ℂ) • ((Q k * ρ).trace • (r k * r j)) := by
          rw [sum_single_mul_mul_conjTranspose_single, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one]
  have hrr : ∀ k, r k * r j = if k = j then embeddedBlockState (ι j) (σ j) else 0 :=
    fun k => embeddedBlockState_sqrt_mul hι hdisj hσ k j
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp_rw [hrr, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

/-- **The mixed transfer map of the limit.** The mixed transfer map of the limit `P_∞` of the
positive parts against the fixed-point tensor `P'_{j,∞}` of block `j`, placed in the full bond
space, is the rank-one map `ρ ↦ Tr(Π_j ρ) σ'_j`, where `Π_j = E_j E_jᴴ` and `σ'_j = E_j σ_j E_jᴴ`
(compare `E_{P_∞} = |ρ⟩⟨1|` in arXiv:2307.01696, eq. `eq:B_TM`). -/
theorem mixedMapLM_blockSumPosLimit_apply (hσ : ∀ j, (σ j).PosSemidef) (j : Fin b)
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.mixedMapLM (ofPhysicalMatrixLM (blockSumPosLimit ι σ))
        (fixedPointTensor (embeddedBlockState (ι j) (σ j))) ρ =
      (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ * ρ).trace •
        embeddedBlockState (ι j) (σ j) := by
  simpa using mixedMapLM_blockSumPosLimit_smul_apply hι hdisj hσ (fun _ => 1)
    (fun _ => zero_le_one) j ρ

end Limit

/-- A linear map `ρ ↦ Tr(Q ρ) σ` with `Tr(Q σ) = 1` has an idempotent transfer matrix. -/
private theorem isIdempotentElem_transferMatrix_of_apply_eq_trace_smul
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {Q σ : Matrix (Fin D) (Fin D) ℂ} (hT : ∀ ρ, T ρ = (Q * ρ).trace • σ)
    (h1 : (Q * σ).trace = 1) : IsIdempotentElem (transferMatrix T) := by
  rw [IsIdempotentElem, ← transferMatrix_comp]
  congr 1
  ext ρ : 1
  simp only [LinearMap.comp_apply, hT, Matrix.mul_smul, Matrix.trace_smul, h1, smul_eq_mul,
    mul_one]

/-- A linear map `ρ ↦ Tr(Q ρ) σ` has transfer matrix of trace `Tr(Q σ)`. -/
private theorem trace_transferMatrix_of_apply_eq_trace_smul [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {Q σ : Matrix (Fin D) (Fin D) ℂ} (hT : ∀ ρ, T ρ = (Q * ρ).trace • σ) :
    (transferMatrix T).trace = (Q * σ).trace := by
  have e : T = ((Matrix.traceLinearMap (Fin D) ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ Q).smulRight σ := by
    ext1 ρ
    simp [hT]
  rw [trace_transferMatrix_eq_linearMap_trace, e, LinearMap.trace_smulRight]
  simp

/-! ### The overlap of the positive part with the fixed point of one block -/

open scoped Matrix.Norms.L2Operator in
/-- **The overlap of one block near the weighted limit.** For blocks placed with orthogonal
ranges, positive semidefinite `σ_k` of trace one, and a block `j`, there is `C > 0` such that the
following holds for all weights `t_k ≥ 0` with `t_j ≤ 1`, all `δ`, and all `M ≥ 1`. Let `P` be a
matrix on the bond pairs with `‖P - P_∞‖ ≤ δ`, where `P_∞ = ∑ₖ t_k K_k ((√σ_k)ᵀ ⊗ 1) K_kᴴ` is
written as `∑ₖ K_k ((√(t_k² σ_k))ᵀ ⊗ 1) K_kᴴ`. Then the overlap
`z = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` with the fixed-point tensor of block `j` placed in the full bond space
satisfies `|z - t_j^M| ≤ C (M δ) e^{C M δ}`.

The mixed transfer matrix of `P_∞` against `P'_{j,∞}` is `t_j R` with `R` idempotent of trace one
(`mixedMapLM_blockSumPosLimit_smul_apply`), so its powers are bounded uniformly in `t_j ≤ 1`, and
the telescoping estimate of arXiv:2103.13367, Supplemental Material, eqs. `final_eq` to
`finished`, applies (`norm_prod_range_sub_pow_le_of_forall_norm_pow_le`). -/
theorem exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (j : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : Fin b → ℝ, (∀ k, 0 ≤ t k) → t j ≤ 1 →
      ∀ (P : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (δ : ℝ) (M : ℕ) [NeZero M],
      ‖P - blockSumPosLimit ι (fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k)‖ ≤ δ →
      ‖mpvOverlap (ofPhysicalMatrixLM P) (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M -
          (t j : ℂ) ^ M‖ ≤ C * (M * δ) * Real.exp (C * (M * δ)) := by
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero D := ⟨fun h => by subst h; exact (ι j 0).elim0⟩
  set F := fixedPointTensor (embeddedBlockState (ι j) (σ j))
  set Ψ := mixedTransferMatrixLeft F
  set K₃ := ‖LinearMap.toContinuousLinearMap Ψ‖
  have hK₃ : 0 ≤ K₃ := norm_nonneg _
  have hΨ : ∀ G, ‖Ψ G‖ ≤ K₃ * ‖G‖ := (LinearMap.toContinuousLinearMap Ψ).le_opNorm
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  set K₄ := ‖trL‖
  have hK₄ : 0 ≤ K₄ := norm_nonneg _
  have htrace : ∀ G, ‖Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ G‖ ≤ K₄ * ‖G‖ := trL.le_opNorm
  set R := Ψ (blockSumPosLimit ι σ)
  have hR := mixedMapLM_blockSumPosLimit_apply hι hdisj hσ j
  have h1 : (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ *
      embeddedBlockState (ι j) (σ j)).trace = 1 := by
    rw [trace_coordEmbedding_mul_conjTranspose_mul_embeddedBlockState hι, htr j]
  have hidem : IsIdempotentElem R := isIdempotentElem_transferMatrix_of_apply_eq_trace_smul hR h1
  have htr1 : R.trace = 1 := (trace_transferMatrix_of_apply_eq_trace_smul hR).trans h1
  set c := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ + ‖R‖
  have hc : 0 ≤ c := by positivity
  set C := K₄ * c * (c * K₃) + c * K₃ + 1
  refine ⟨C, by positivity, fun t ht htj P δ M _ hP => ?_⟩
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hP
  set Tinf := Ψ (blockSumPosLimit ι fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k)
  have hTinf : Tinf = (t j : ℂ) • R := by
    have hmap : mixedMapLMLeft F
        (ofPhysicalMatrixLM (blockSumPosLimit ι fun k => (((t k ^ 2 : ℝ)) : ℂ) • σ k)) =
        (t j : ℂ) • mixedMapLMLeft F (ofPhysicalMatrixLM (blockSumPosLimit ι σ)) :=
      LinearMap.ext fun ρ => by
        change Kraus.mixedMapLM _ F ρ = (t j : ℂ) • Kraus.mixedMapLM _ F ρ
        rw [mixedMapLM_blockSumPosLimit_smul_apply hι hdisj hσ t ht, hR]
    simp only [Tinf, R, Ψ, mixedTransferMatrixLeft, LinearMap.comp_apply, hmap, map_smul]
  have hpow : ∀ k : ℕ, ‖Tinf ^ k‖ ≤ c := fun k => by
    rcases k with _ | k
    · rw [pow_zero]; exact le_add_of_nonneg_right (norm_nonneg _)
    · rw [hTinf, smul_pow, hidem.pow_succ_eq, norm_smul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ht j)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (ht j) htj)).trans
        (le_add_of_nonneg_left (norm_nonneg _))
  set T := Ψ P
  have hδ' : ∀ k : ℕ, ‖(fun _ : ℕ => T) k - Tinf‖ ≤ K₃ * δ := fun _ => by
    rw [← map_sub]
    exact (hΨ _).trans (mul_le_mul_of_nonneg_left hP hK₃)
  have htel := norm_prod_range_sub_pow_le_of_forall_norm_pow_le hpow hδ' M
  rw [List.map_const', List.length_range, List.prod_replicate] at htel
  have hTM : Tinf ^ M = (t j : ℂ) ^ M • R := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
    rw [hTinf, smul_pow, hn, hidem.pow_succ_eq]
  have hover : mpvOverlap (ofPhysicalMatrixLM P) F M - (t j : ℂ) ^ M =
      Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ (T ^ M - Tinf ^ M) := by
    rw [map_sub, Matrix.traceLinearMap_apply, Matrix.traceLinearMap_apply, hTM, Matrix.trace_smul,
      htr1, smul_eq_mul, mul_one, ← trace_transferMatrix_mixedMapLM_pow_eq_mpvOverlap]
    rfl
  have hy : 0 ≤ c * (K₃ * δ) := by positivity
  have hgeom := one_add_pow_sub_one_le_mul_exp hy M
  have hu : 0 ≤ (M : ℝ) * δ := by positivity
  calc ‖mpvOverlap (ofPhysicalMatrixLM P) F M - (t j : ℂ) ^ M‖
      ≤ K₄ * ‖T ^ M - Tinf ^ M‖ := by rw [hover]; exact htrace _
    _ ≤ K₄ * (c * ((1 + c * (K₃ * δ)) ^ M - 1)) := by gcongr
    _ ≤ K₄ * (c * (M * (c * (K₃ * δ)) * Real.exp (M * (c * (K₃ * δ))))) := by gcongr
    _ = K₄ * c * (c * K₃) * (M * δ) * Real.exp (c * K₃ * (M * δ)) := by ring_nf
    _ ≤ C * (M * δ) * Real.exp (C * (M * δ)) := by
        have hC1 : K₄ * c * (c * K₃) ≤ C := by
          simp only [C]; nlinarith [mul_nonneg hc hK₃]
        have hC2 : c * K₃ ≤ C := by
          simp only [C]; nlinarith [mul_nonneg (mul_nonneg hK₄ hc) (mul_nonneg hc hK₃)]
        gcongr

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

open scoped Matrix.Norms.L2Operator in
/-- **The overlap of one block.** In the setting of
`exists_norm_polarPos_blockTensor_blockSum_sub_le`, with `0 < γ < 1`, the overlap
`zⱼ = ⟨φ_M(P'_{j,∞})|φ_M(P)⟩` of the positive part `P` of the `q`-site blocked direct sum with the
fixed-point tensor of block `j` placed in the full bond space satisfies
`|zⱼ - 1| ≤ C u e^{C u}` with `u = M e^{-γ q/ξ}`, for `q ≥ 1` and `M ≥ 1`.

The mixed transfer matrix of `P_∞` against `P'_{j,∞}` is idempotent with trace one
(`mixedMapLM_blockSumPosLimit_apply`), and the telescoping estimate of arXiv:2103.13367,
Supplemental Material, eqs. `final_eq` to `finished`, applies as in the normal case
(`exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le` at unit weights). -/
theorem exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) (j : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M], q ≠ 0 →
      ‖mpvOverlap (polarPosTensor (blockTensor (blockSum Aj ι fun _ => 1) q))
          (fixedPointTensor (embeddedBlockState (ι j) (σ j))) M - 1‖ ≤
        C * (M * Real.exp (-γ / correlationLength lam₂) ^ q) *
          Real.exp (C * (M * Real.exp (-γ / correlationLength lam₂) ^ q)) := by
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_blockSum_sub_le hι hdisj hN hA hσ
    htr hfix hl hlam hmix hγ0 hγ
  obtain ⟨C₀, hC₀, hgen⟩ := exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le hι
    hdisj (fun j => (hσ j).posSemidef) htr j
  refine ⟨C₀ * K₁ + 1, by positivity, fun q M _ hq => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have h := hgen (fun _ => 1) (fun _ => zero_le_one) le_rfl _ (K₁ * x ^ q) M
    (by simpa using hpos q hq)
  simp only [Complex.ofReal_one, one_pow] at h
  have hu : 0 ≤ (M : ℝ) * x ^ q := by positivity
  have hre : C₀ * (M * (K₁ * x ^ q)) = C₀ * K₁ * (M * x ^ q) := by ring
  calc _ ≤ C₀ * (M * (K₁ * x ^ q)) * Real.exp (C₀ * (M * (K₁ * x ^ q))) := h
    _ = C₀ * K₁ * (M * x ^ q) * Real.exp (C₀ * K₁ * (M * x ^ q)) := by rw [hre]
    _ ≤ (C₀ * K₁ + 1) * (M * x ^ q) * Real.exp ((C₀ * K₁ + 1) * (M * x ^ q)) := by
        gcongr <;> linarith

/-! ### Overlaps of distinct blocks and the norm of the target -/

open scoped Matrix.Norms.L2Operator in
/-- **Decay of the overlaps of distinct blocks.** In the setting of
`exists_norm_mixedMapLM_pow_apply_le`, `|⟨φ_N(Y)|φ_N(X)⟩| ≤ K e^{-γ N/ξ}`.

arXiv:2307.01696, Supplemental Material, eq. (S14) (`eq:app_decay_mixed`):
`|⟨v_j|v_{j'}⟩| = O(e^{-N/ξ_{jj'}})`. -/
theorem exists_norm_mpvOverlap_le_of_mixedMapLM {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (X : MPSTensor d D₁) (Y : MPSTensor d D₂) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM X Y) μ → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      ‖mpvOverlap X Y N‖ ≤ K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  obtain ⟨C, hC, hpow⟩ := exists_norm_mixedMapLM_pow_apply_le X Y hl hlam hγ0 hγ
  obtain ⟨K₂, hK₂, hent⟩ := Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D₁) (n := Fin D₂)
  set x := Real.exp (-γ / correlationLength lam₂)
  refine ⟨∑ p : Fin D₁, ∑ r : Fin D₂,
    K₂ * C * ‖(Matrix.single p r 1 : Matrix (Fin D₁) (Fin D₂) ℂ)‖, by positivity, fun N => ?_⟩
  rw [← trace_mixedMapLM_rect_pow_eq_mpvOverlap, Matrix.linearMap_trace_eq_sum_apply_single,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  calc ‖((Kraus.mixedMapLM X Y ^ N) (Matrix.single p r 1)) p r‖
      ≤ K₂ * (C * x ^ N * ‖(Matrix.single p r 1 : Matrix (Fin D₁) (Fin D₂) ℂ)‖) :=
        (hent _ _ _).trans (by gcongr; exact hpow N _)
    _ = K₂ * C * ‖(Matrix.single p r 1 : Matrix (Fin D₁) (Fin D₂) ℂ)‖ * x ^ N := by ring

/-- **The norm of a combination of block states.** In the setting of
`exists_norm_gram_blockTensor_blockSum_sub_le`, with `0 < γ < 1/2`, there is `K` such that for
all `R` and all coefficients `βⱼ` with `|βⱼ| ≤ R`, the vector `∑ⱼ βⱼ |φ_N(A_j)⟩` on `N` sites
satisfies `|‖∑ⱼ βⱼ |φ_N(A_j)⟩‖² - ∑ⱼ |βⱼ|²| ≤ R² K e^{-γ N/ξ}`: its squared norm is
`∑ⱼ ∑ₖ βⱼ conj(βₖ) ⟨φ_N(A_k)|φ_N(A_j)⟩`, the diagonal terms are `|βⱼ|²` up to the normalization
of the normal case (`exists_abs_norm_mpvState_sq_sub_one_le`), and the others decay at the rate
of the mixed transfer maps (`exists_norm_mpvOverlap_le_of_mixedMapLM`).

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the bound on
`|c_N²/\tilde c_N² - 1|`, with `\tilde c_N² = ∑ⱼ |βⱼ|²`. -/
theorem exists_abs_sum_norm_sq_sum_mpv_sub_le
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R : ℝ) (β : Fin b → ℂ), (∀ j, ‖β j‖ ≤ R) → ∀ N : ℕ,
      |∑ s : Fin N → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 - ∑ j, ‖β j‖ ^ 2| ≤
        R ^ 2 * K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hl.le
  choose K₅ hK₅ hc using fun j => exists_abs_norm_mpvState_sq_sub_one_le (Aj j) (hN j) (hA j)
    (hσ j) (htr j) (hfix j) (hlam j) hγ0 hγ
  have hoff : ∀ j k, ∃ K : ℝ, 0 ≤ K ∧ (j ≠ k → ∀ N : ℕ,
      ‖mpvOverlap (Aj j) (Aj k) N‖ ≤ K * x ^ N) := fun j k => by
    by_cases hjk : j = k
    · exact ⟨0, le_rfl, fun h => absurd hjk h⟩
    · obtain ⟨K, hK, h⟩ := exists_norm_mpvOverlap_le_of_mixedMapLM (Aj j) (Aj k) hl
        (hmix j k hjk) hγ0 (by linarith)
      exact ⟨K, hK, fun _ => h⟩
  choose Ko hKo hob using hoff
  refine ⟨∑ j, K₅ j + ∑ j, ∑ k, Ko j k,
    add_nonneg (Finset.sum_nonneg fun j _ => hK₅ j)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hKo j k),
    fun R β hβ N => ?_⟩
  set c : Fin b → Fin b → ℂ := fun j k => β j * star (β k)
  have hc1 : ∀ j k, ‖c j k‖ ≤ R ^ 2 := fun j k => by
    simp only [c, norm_mul, norm_star, sq]
    exact mul_le_mul (hβ j) (hβ k) (norm_nonneg _) ((norm_nonneg _).trans (hβ j))
  have hcjj : ∀ j, c j j = ((‖β j‖ ^ 2 : ℝ) : ℂ) := fun j => by
    simp only [c]
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  have hsum : ((∑ s : Fin N → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, c j k * mpvOverlap (Aj j) (Aj k) N := by
    rw [ofReal_sum_norm_sq]
    simp_rw [star_sum, star_mul', Finset.sum_mul_sum, mpvOverlap, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [c]
    ring
  have hexp : ((∑ s : Fin N → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 - ∑ j, ‖β j‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, c j j * ((‖mpvState (Aj j) N‖ ^ 2 - 1 : ℝ) : ℂ) +
        ∑ j, ∑ k ∈ Finset.univ.erase j, c j k * mpvOverlap (Aj j) (Aj k) N := by
    rw [Complex.ofReal_sub, hsum, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_sub, ofReal_norm_mpvState_sq, Complex.ofReal_one, mul_sub, mul_one]
    have hsplit : ∑ j, ∑ k, c j k * mpvOverlap (Aj j) (Aj k) N =
        ∑ j, c j j * mpvOverlap (Aj j) (Aj j) N +
          ∑ j, ∑ k ∈ Finset.univ.erase j, c j k * mpvOverlap (Aj j) (Aj k) N := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [hsplit, Finset.sum_sub_distrib]
    simp_rw [hcjj]
    ring
  have hxx : ∀ n : ℕ, (x ^ 2) ^ n ≤ x ^ n := fun n =>
    pow_le_pow_left₀ (by positivity) (by nlinarith) n
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hexp, mul_add, add_mul, Finset.mul_sum,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖c j j‖ * |‖mpvState (Aj j) N‖ ^ 2 - 1| ≤ R ^ 2 * (K₅ j * x ^ N) :=
          mul_le_mul (hc1 j j) ((hc j N).trans (mul_le_mul_of_nonneg_left (hxx N) (hK₅ j)))
            (abs_nonneg _) (sq_nonneg R)
      _ = R ^ 2 * K₅ j * x ^ N := by ring
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j Finset.univ)
        fun k _ _ => mul_nonneg (mul_nonneg (sq_nonneg R) (hKo j k)) (pow_nonneg hx0 N)))
    rw [norm_mul]
    calc ‖c j k‖ * ‖mpvOverlap (Aj j) (Aj k) N‖ ≤ R ^ 2 * (Ko j k * x ^ N) :=
          mul_le_mul (hc1 j k) (hob j k (Ne.symm (Finset.ne_of_mem_erase hk)) N)
            (norm_nonneg _) (sq_nonneg R)
      _ = R ^ 2 * Ko j k * x ^ N := by ring

/-- **The norm of the target with weights.** In the setting of
`exists_norm_gram_blockTensor_blockSum_sub_le`, with `0 < γ < 1/2`, there is `K` such that for all
weights `μⱼ` with `|μⱼ| ≤ 1` the periodic state of the direct sum `⊕ⱼ μⱼ A_j` on `N ≥ 1` sites
satisfies `|‖φ_N‖² - ∑ⱼ |μⱼ^N|²| ≤ K e^{-γ N/ξ}`: it is `∑ⱼ μⱼ^N |φ_N(A_j)⟩` (`mpv_blockSum`),
and `exists_abs_sum_norm_sq_sum_mpv_sub_le` applies with `R = 1`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the bound on
`|c_N²/\tilde c_N² - 1|`, with `\tilde c_N² = ∑ⱼ |βⱼ|²` and `βⱼ = μⱼ^N` (eq. (S4) for
multiplicity one). -/
theorem exists_abs_norm_mpvState_blockSum_weight_sq_sub_le
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : Fin b → ℂ, (∀ j, ‖μ j‖ ≤ 1) → ∀ N : ℕ, N ≠ 0 →
      |‖mpvState (blockSum Aj ι μ) N‖ ^ 2 - ∑ j, ‖μ j ^ N‖ ^ 2| ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  obtain ⟨K, hK, h⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix hl hlam hmix hγ0 hγ
  refine ⟨K, hK, fun μ hμ N hN0 => ?_⟩
  have h' := h 1 (fun j => μ j ^ N)
    (fun j => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hμ j)) N
  rw [one_pow, one_mul] at h'
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [mpvState_apply, mpv_blockSum hι hdisj μ hN0] using h'

/-- **The norm of the target.** In the setting of `exists_norm_gram_blockTensor_blockSum_sub_le`,
with `0 < γ < 1/2`, the periodic state of the direct sum with unit weights on `N ≥ 1` sites
satisfies `|‖φ_N‖² - b| ≤ K e^{-γ N/ξ}`: its squared norm is `∑ⱼ ∑ₖ ⟨φ_N(A_j)|φ_N(A_k)⟩`, the
diagonal terms are `1` up to the normalization of the normal case
(`exists_abs_norm_mpvState_sq_sub_one_le`), and the others decay at the rate of the mixed
transfer maps (`exists_abs_norm_mpvState_blockSum_weight_sq_sub_le` at unit weights).

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the bound on
`|c_N²/\tilde c_N² - 1|`. -/
theorem exists_abs_norm_mpvState_blockSum_sq_sub_le
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N ≠ 0 →
      |‖mpvState (blockSum Aj ι fun _ => 1) N‖ ^ 2 - b| ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ N := by
  obtain ⟨K, hK, h⟩ := exists_abs_norm_mpvState_blockSum_weight_sq_sub_le hι hdisj hN hA hσ htr
    hfix hl hlam hmix hγ0 hγ
  exact ⟨K, hK, fun N hN0 => by simpa using h (fun _ => 1) (fun _ => norm_one.le) N hN0⟩

end MPSTensor
