/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalBlockSum
import TNLean.MPS.Preparation.PositivePartRate
import QICLean.Analysis.MatrixFramePerturbation

/-!
# The positive part of a direct sum of blocks with overlapping states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") block `q` sites of a tensor `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` and use that the
positive part `P` of the blocked map `B = V P` is the direct sum of the positive parts of the
blocks (eq. (S5)). When the `q`-site states of distinct blocks are not orthogonal this fails
(`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`). This file proves the estimate that
replaces it for unit weights `μⱼ = 1`: with `ξ = -1/log|λ₂|`, where `λ₂` bounds the moduli of
the eigenvalues other than `1` of the transfer maps `E_{jj}` of the blocks and the moduli of all
eigenvalues of the mixed transfer maps `E_{jj'}`, `j ≠ j'`, and `0 < γ < 1`,

  `‖P - P_∞‖ ≤ K e^{-γ q/ξ}`, with `P_∞ = ∑ⱼ K_j ((√σ_j)ᵀ ⊗ 1) K_jᴴ`,

where `K_j = E_j ⊗ E_j` embeds the bond pairs of block `j`. The mixed transfer maps enter
through the off-diagonal blocks `B_jᴴ B_{j'}` of the Gram matrix `Bᴴ B`, which are the
`q`-th powers of `E_{j'j}` with the legs regrouped.

The proof follows `MPSTensor.exists_norm_polarPos_blockTensor_sub_le` for one normal tensor. The
limit `P_∞² = ∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ` of the Gram matrices vanishes on the bond pairs `(a, b)`
with `a` and `b` in different blocks, as does `Bᴴ B`; adding the projector `Q` onto those pairs
to both makes the limit strictly positive, and `√(Bᴴ B + Q) = P + Q` because `P Q = 0`. The
Lipschitz bound of the square root at a strictly positive point
(`CFC.norm_sqrt_sub_sqrt_le_div`) then transfers the rate of the Gram matrices to `P`.

For weights `|μⱼ| ≤ 1` the Gram estimate holds with the limit
`∑ⱼ |μⱼ|^{2q} K_j (σ_jᵀ ⊗ 1) K_jᴴ` (`exists_norm_gram_blockTensor_blockSum_sub_le`), which is
not bounded below on the blocks of smaller weight; the positive part for weights is estimated
relative to the weights in `TNLean.MPS.Preparation.RelativePositivePart`.

**Scope restriction (multiplicity one):** every block occurs once. The Lipschitz estimate
`exists_norm_polarPos_blockTensor_blockSum_sub_le` is stated for unit weights `μⱼ = 1`.
Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Local fix (positive part of overlapping blocks):** the block form (S5) of the positive part,
false for finite `q` when the blocks overlap, is replaced by the estimate
`‖P - P_∞‖ ≤ K e^{-γ q/ξ}`, whose rate includes the correlation lengths of the mixed transfer
maps. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.exists_norm_mixedMapLM_pow_apply_le` — the rate `e^{-γ/ξ}` for the powers of a
  mixed transfer map whose eigenvalues are bounded by `|λ₂| < 1`.
* `MPSTensor.exists_norm_gram_blockTensor_mixed_le` — the off-diagonal Gram blocks
  `B_jᴴ B_{j'}` decay at that rate.
* `MPSTensor.conjTranspose_mul_sum_of_isometry`,
  `MPSTensor.sum_mul_conjTranspose_mul_sum_of_isometry` — products along isometries with
  orthogonal ranges.
* `Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one` — isometries have norm at most one.
* `MPSTensor.exists_norm_gram_sum_sub_le` — the rate of the Gram matrix of `∑ⱼ cⱼ B_j L_jᴴ`.
* `Matrix.norm_polarPos_sub_le_sqrt` — the Hölder bound for positive parts.
* `MPSTensor.blockSumGramLimit`, `MPSTensor.blockSumPosLimit` — the limits
  `∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ` and `∑ⱼ K_j ((√σ_j)ᵀ ⊗ 1) K_jᴴ`.
* `MPSTensor.gram_blockTensor_blockSum`, `MPSTensor.exists_norm_gram_blockTensor_blockSum_sub_le` —
  the Gram matrix of the weighted direct sum and its rate.
* `MPSTensor.exists_norm_polarPos_blockTensor_blockSum_sub_le` — the rate of `P → P_∞` for unit
  weights, `0 < γ < 1`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S5) and the mixed transfer matrices
  `E_{jj'}` of the proof of Lemma 1'(ii).
* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*,
  arXiv:2103.13367, Supplemental Material, eq. (26) (the Hölder bound for square roots).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D : ℕ}

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-! ### Mixed transfer maps of blocked tensors -/

/-- The mixed transfer map of two `L`-site blocked tensors is the `L`-th power of the mixed
transfer map of the tensors. -/
theorem mixedMapLM_blockTensor_apply {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂)
    (L : ℕ) (Z : Matrix (Fin D₁) (Fin D₂) ℂ) :
    Kraus.mixedMapLM (blockTensor X L) (blockTensor Y L) Z = (Kraus.mixedMapLM X Y ^ L) Z := by
  classical
  rw [Kraus.mixedMapLM_pow_apply, Kraus.mixedMapLM_apply]
  simp only [Kraus.blockTensor, Kraus.wordOfBlock]
  let e : Fin (blockPhysDim d L) ≃ (Fin L → Fin d) := decodeBlockEquiv d L
  simpa [Kraus.decodeBlockEquiv_apply, e] using
    (Fintype.sum_equiv e
      (f := fun i =>
        Kraus.evalWord X (List.ofFn (e i)) * Z * (Kraus.evalWord Y (List.ofFn (e i)))ᴴ)
      (g := fun σ => Kraus.evalWord X (List.ofFn σ) * Z * (Kraus.evalWord Y (List.ofFn σ))ᴴ)
      (by intro i; rfl))

open scoped Matrix.Norms.L2Operator in
/-- **Decay of a mixed transfer map.** If every eigenvalue of the mixed transfer map
`E_{XY}(Z) = ∑ᵢ Xⁱ Z (Yⁱ)†` has modulus at most `|λ₂| < 1` and `0 < γ < 1`, then
`‖E_{XY}^n(Z)‖ ≤ C e^{-γ n/ξ} ‖Z‖` with `ξ = -1/log|λ₂|`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the mixed transfer matrix
`E_{jj'}` has spectral radius `τ_max < 1`, and `ξ_{jj'} = -1/ln τ_max`. -/
theorem exists_norm_mixedMapLM_pow_apply_le {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (X : MPSTensor d D₁) (Y : MPSTensor d D₂) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM X Y) μ → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Z : Matrix (Fin D₁) (Fin D₂) ℂ),
      ‖(Kraus.mixedMapLM X Y ^ n) Z‖ ≤ C * Real.exp (-γ / correlationLength lam₂) ^ n * ‖Z‖ := by
  classical
  let Φ : Module.End ℂ (Matrix (Fin D₁) (Fin D₂) ℂ) ≃ₐ[ℂ] _ :=
    Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)
  set x := Real.exp (-γ / correlationLength lam₂)
  let r : ℝ≥0 := ⟨x, by positivity⟩
  have hrad : spectralRadius ℂ (Φ (Kraus.mixedMapLM X Y)) < (r : ℝ≥0∞) := by
    refine spectrum.spectralRadius_lt_of_forall_lt _ fun z hz => ?_
    rw [AlgEquiv.spectrum_eq] at hz
    have h := hlam z (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact lt_exp_neg_div_correlationLength hγ0 hγ (h.trans_lt hl) h
  obtain ⟨C, hC, hgeom⟩ := geometric_apply_bound_of_spectralRadius_lt _ r hrad
  refine ⟨C, hC, fun n Z => ?_⟩
  have h := hgeom n Z
  rwa [← map_pow] at h

open scoped Matrix.Norms.L2Operator in
/-- **Off-diagonal Gram blocks.** In the setting of `exists_norm_mixedMapLM_pow_apply_le` for the
mixed transfer map `E_{YX}`, the mixed Gram matrices `B_Xᴴ B_Y` of the `q`-site blocked tensors
satisfy `‖B_Xᴴ B_Y‖ ≤ K e^{-γ q/ξ}`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii): the overlaps of the states of
distinct blocks decay at the rate of the mixed transfer matrix. -/
theorem exists_norm_gram_blockTensor_mixed_le {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (X : MPSTensor d D₁) (Y : MPSTensor d D₂) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM Y X) μ → ‖μ‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ,
      ‖(physicalMatrix (blockTensor X q))ᴴ * physicalMatrix (blockTensor Y q)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  classical
  obtain ⟨C, hC, hpow⟩ := exists_norm_mixedMapLM_pow_apply_le Y X hl hlam hγ0 hγ
  obtain ⟨K₂, hK₂, hent⟩ := Matrix.exists_norm_entry_le_mul_l2_opNorm (m := Fin D₂) (n := Fin D₁)
  set x := Real.exp (-γ / correlationLength lam₂)
  refine ⟨∑ a : Fin D₁ × Fin D₁, ∑ c : Fin D₂ × Fin D₂,
    K₂ * C * ‖(Matrix.single c.2 a.2 1 : Matrix (Fin D₂) (Fin D₁) ℂ)‖ *
      ‖(Matrix.single a c 1 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)‖,
    by positivity, fun q => ?_⟩
  refine (Matrix.l2_opNorm_le_sum_norm_entry _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [conjTranspose_physicalMatrix_mul_physicalMatrix_apply, mixedMapLM_blockTensor_apply]
  calc ‖(Kraus.mixedMapLM Y X ^ q) (Matrix.single c.2 a.2 1) c.1 a.1‖ *
        ‖(Matrix.single a c 1 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)‖
      ≤ (K₂ * (C * x ^ q * ‖(Matrix.single c.2 a.2 1 : Matrix (Fin D₂) (Fin D₁) ℂ)‖)) *
          ‖(Matrix.single a c 1 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)‖ := by
        gcongr
        exact (hent _ _ _).trans (by gcongr; exact hpow q _)
    _ = K₂ * C * ‖(Matrix.single c.2 a.2 1 : Matrix (Fin D₂) (Fin D₁) ℂ)‖ *
          ‖(Matrix.single a c 1 : Matrix (Fin D₁ × Fin D₁) (Fin D₂ × Fin D₂) ℂ)‖ * x ^ q := by
        ring

/-! ### The limits of the Gram matrix and of the positive part -/

variable {b : ℕ} {Dj : Fin b → ℕ}

/-- The limit `∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ` of the Gram matrices `Bᴴ B` of the blocked direct sum
with unit weights: the direct sum of the limits `σ_jᵀ ⊗ 1 = P_{j,∞}²` of the blocks, placed on
the bond pairs of block `j` by `K_j = E_j ⊗ E_j`. -/
noncomputable def blockSumGramLimit (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ j, pairEmbedding (ι j) * ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
    (pairEmbedding (ι j))ᴴ

/-- The limit `P_∞ = ∑ⱼ K_j ((√σ_j)ᵀ ⊗ 1) K_jᴴ` of the positive parts of the blocked direct sum
with unit weights: the fixed-point tensors `P_{j,∞}` of the blocks, placed on the bond pairs of
block `j` (arXiv:2307.01696, Supplemental Material, eq. (S5) in the limit `q → ∞`). -/
noncomputable def blockSumPosLimit (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ j, pairEmbedding (ι j) * ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
    (pairEmbedding (ι j))ᴴ

/-- The matrix `Q = 1 - ∑ⱼ K_j K_jᴴ`. When every `ι_j` is injective and distinct `ι_j` have
disjoint ranges, it is the orthogonal projector onto the bond pairs that do not lie in one block,
as proved below under these hypotheses; for arbitrary embeddings it need not be a projector. -/
noncomputable def offBlockProj (ι : (j : Fin b) → Fin (Dj j) → Fin D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  1 - ∑ j, pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ

variable {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-! ### Isometries with orthogonal ranges -/

section OrthogonalIsometries

variable {κ : Fin b → Type*} [∀ j, Fintype (κ j)] {n : Type*} [Fintype n]
  {L : (j : Fin b) → Matrix n (κ j) ℂ}

/-- `L_jᴴ ∑ₖ L_k Y_k = Y_j` for isometries `L_k` with orthogonal ranges. -/
theorem conjTranspose_mul_sum_of_isometry [∀ j, DecidableEq (κ j)] {γ : Type*}
    (hiso : ∀ j, (L j)ᴴ * L j = 1) (horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0)
    (Y : (k : Fin b) → Matrix (κ k) γ ℂ) (j : Fin b) :
    (L j)ᴴ * ∑ k, L k * Y k = Y j := by
  rw [Matrix.mul_sum, Finset.sum_eq_single j]
  · rw [← Matrix.mul_assoc, hiso j, Matrix.one_mul]
  · intro k _ hk
    rw [← Matrix.mul_assoc, horth j k (Ne.symm hk), Matrix.zero_mul]
  · simp

/-- `(∑ⱼ L_j Y_j L_jᴴ)(∑ⱼ L_j Z_j L_jᴴ) = ∑ⱼ L_j Y_j Z_j L_jᴴ` for isometries `L_j` with
orthogonal ranges. -/
theorem sum_mul_conjTranspose_mul_sum_of_isometry [∀ j, DecidableEq (κ j)]
    (hiso : ∀ j, (L j)ᴴ * L j = 1) (horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0)
    (Y Z : (j : Fin b) → Matrix (κ j) (κ j) ℂ) :
    (∑ j, L j * Y j * (L j)ᴴ) * (∑ j, L j * Z j * (L j)ᴴ) =
      ∑ j, L j * (Y j * Z j) * (L j)ᴴ := by
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := conjTranspose_mul_sum_of_isometry hiso horth (fun k => Z k * (L k)ᴴ) j
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h]

end OrthogonalIsometries

section Projector

variable (hι : ∀ j, Function.Injective (ι j))
  (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
include hι hdisj

/-- `K_jᴴ ∑ₖ K_k Y_k = Y_j` for embeddings with orthogonal ranges. -/
private theorem conjTranspose_pairEmbedding_mul_sum {γ : Type*}
    (Y : (k : Fin b) → Matrix (Fin (Dj k) × Fin (Dj k)) γ ℂ) (j : Fin b) :
    (pairEmbedding (ι j))ᴴ * ∑ k, pairEmbedding (ι k) * Y k = Y j :=
  conjTranspose_mul_sum_of_isometry (fun j => conjTranspose_pairEmbedding_mul_self (hι j))
    (fun j k h => conjTranspose_pairEmbedding_mul_eq_zero (hdisj j k h)) Y j

/-- `K_jᴴ Q = 0`. -/
private theorem conjTranspose_pairEmbedding_mul_offBlockProj (j : Fin b) :
    (pairEmbedding (ι j))ᴴ * offBlockProj ι = 0 := by
  have h := conjTranspose_pairEmbedding_mul_sum hι hdisj
    (fun k => (pairEmbedding (ι k))ᴴ) j
  rw [offBlockProj, Matrix.mul_sub, Matrix.mul_one, h, sub_self]

/-- `Q K_j = 0`. -/
private theorem offBlockProj_mul_pairEmbedding (j : Fin b) :
    offBlockProj ι * pairEmbedding (ι j) = 0 := by
  have h : (offBlockProj ι)ᴴ = offBlockProj ι := by
    simp [offBlockProj, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
  have := congrArg Matrix.conjTranspose (conjTranspose_pairEmbedding_mul_offBlockProj hι hdisj j)
  rwa [Matrix.conjTranspose_mul, h, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] at this

/-- `X Q = 0` for `X = ∑ⱼ K_j Y_j K_jᴴ`. -/
private theorem sum_mul_offBlockProj {γ : Type*}
    (Y : (j : Fin b) → Matrix γ (Fin (Dj j) × Fin (Dj j)) ℂ) :
    (∑ j, Y j * (pairEmbedding (ι j))ᴴ) * offBlockProj ι = 0 := by
  rw [Matrix.sum_mul]
  simp only [Matrix.mul_assoc, conjTranspose_pairEmbedding_mul_offBlockProj hι hdisj,
    Matrix.mul_zero, Finset.sum_const_zero]

/-- `Q X = 0` for `X = ∑ⱼ K_j Y_j`. -/
private theorem offBlockProj_mul_sum {γ : Type*}
    (Y : (j : Fin b) → Matrix (Fin (Dj j) × Fin (Dj j)) γ ℂ) :
    offBlockProj ι * ∑ j, pairEmbedding (ι j) * Y j = 0 := by
  rw [Matrix.mul_sum]
  simp only [← Matrix.mul_assoc, offBlockProj_mul_pairEmbedding hι hdisj, Matrix.zero_mul,
    Finset.sum_const_zero]

omit hι hdisj in
/-- `Q` is Hermitian. -/
private theorem isHermitian_offBlockProj : (offBlockProj ι).IsHermitian := by
  simp [Matrix.IsHermitian, offBlockProj, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]

/-- `Q` is idempotent. -/
private theorem offBlockProj_mul_self : offBlockProj ι * offBlockProj ι = offBlockProj ι := by
  have h := sum_mul_offBlockProj hι hdisj (γ := Fin D × Fin D) fun j => pairEmbedding (ι j)
  calc offBlockProj ι * offBlockProj ι =
        (1 - ∑ j, pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ) * offBlockProj ι := rfl
    _ = offBlockProj ι - (∑ j, pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ) * offBlockProj ι := by
        rw [Matrix.sub_mul, Matrix.one_mul]
    _ = offBlockProj ι := by rw [h, sub_zero]

/-- `Q` is positive semidefinite. -/
private theorem posSemidef_offBlockProj : (offBlockProj ι).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (offBlockProj ι)
  rwa [(isHermitian_offBlockProj (ι := ι)).eq, offBlockProj_mul_self hι hdisj] at h

/-- `(∑ⱼ K_j Y_j K_jᴴ)(∑ⱼ K_j Z_j K_jᴴ) = ∑ⱼ K_j Y_j Z_j K_jᴴ`. -/
private theorem sum_pairEmbedding_mul_sum_pairEmbedding
    (Y Z : (j : Fin b) → Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj j) × Fin (Dj j)) ℂ) :
    (∑ j, pairEmbedding (ι j) * Y j * (pairEmbedding (ι j))ᴴ) *
        (∑ j, pairEmbedding (ι j) * Z j * (pairEmbedding (ι j))ᴴ) =
      ∑ j, pairEmbedding (ι j) * (Y j * Z j) * (pairEmbedding (ι j))ᴴ :=
  sum_mul_conjTranspose_mul_sum_of_isometry (fun j => conjTranspose_pairEmbedding_mul_self (hι j))
    (fun j k h => conjTranspose_pairEmbedding_mul_eq_zero (hdisj j k h)) Y Z

end Projector

/-! ### The Gram matrix of the blocked direct sum -/

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

/-- For `q ≥ 1` the physical matrix of the `q`-site blocked direct sum with unit weights is
`B = ∑ⱼ B_j K_jᴴ` (`physicalMatrix_blockTensor_blockSum` at `μⱼ = 1`). -/
theorem physicalMatrix_blockTensor_blockSum_one (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q) =
      ∑ j, physicalMatrix (blockTensor (Aj j) q) * (pairEmbedding (ι j))ᴴ := by
  rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hq]
  simp only [one_pow, one_smul]

/-- The Gram matrix of the `q`-site blocked direct sum with weights `μⱼ`, `q ≥ 1`, is
`Bᴴ B = ∑ⱼ ∑ₖ conj(μⱼ^q) μₖ^q K_j (B_jᴴ B_k) K_kᴴ`: its blocks are the mixed Gram matrices of the
blocks. -/
theorem gram_blockTensor_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {q : ℕ} (hq : q ≠ 0) :
    (physicalMatrix (blockTensor (blockSum Aj ι μ) q))ᴴ *
        physicalMatrix (blockTensor (blockSum Aj ι μ) q) =
      ∑ j, ∑ k, (star (μ j ^ q) * μ k ^ q) • (pairEmbedding (ι j) *
        ((physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj k) q)) *
          (pairEmbedding (ι k))ᴴ) := by
  rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hq, Matrix.conjTranspose_sum,
    Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, mul_comm (μ k ^ q)]

/-- The limit of the Gram matrices for the rescaled fixed points `cⱼ σⱼ`:
`∑ⱼ K_j ((cⱼ σⱼ)ᵀ ⊗ 1) K_jᴴ = ∑ⱼ cⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ`. -/
private theorem blockSumGramLimit_smul (c : Fin b → ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    blockSumGramLimit ι (fun j => c j • σ j) =
      ∑ j, c j • (pairEmbedding (ι j) * ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) *
        (pairEmbedding (ι j))ᴴ) := by
  simp only [blockSumGramLimit, Matrix.transpose_smul, Matrix.smul_kronecker, Matrix.mul_smul,
    Matrix.smul_mul]

open scoped Matrix.Norms.L2Operator in
/-- **Rate of the Gram matrices of a sum along embeddings.** Let the blocks `A_j` be normal in
the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, and let `λ₂`
with `|λ₂| < 1` bound the moduli of the eigenvalues other than `1` of every `E_{A_j}` and of all
eigenvalues of the mixed transfer maps `E_{jj'}` of distinct blocks. For `0 < γ < 1` there is
`K` such that for all `R`, all coefficients `cⱼ` with `|cⱼ| ≤ R` and all matrices `L_j` with
`‖L_j‖ ≤ 1`, the matrix `B = ∑ⱼ cⱼ B_j L_jᴴ`, with `B_j` the physical matrix of the `q`-site
blocked tensor of `A_j`, satisfies
`‖Bᴴ B - ∑ⱼ |cⱼ|² L_j (σ_jᵀ ⊗ 1) L_jᴴ‖ ≤ R² K e^{-γ q/ξ}` for every `q`.

The blocks of `Bᴴ B` are `conj(cⱼ) c_k L_j (B_jᴴ B_k) L_kᴴ`: the diagonal ones are `σ_jᵀ ⊗ 1` up
to the normal case (`exists_norm_gram_blockTensor_sub_le`), and the others decay at the rate of
the mixed transfer maps (`exists_norm_gram_blockTensor_mixed_le`; arXiv:2307.01696,
Supplemental Material, proof of Lemma 1'(ii)). For the blocked direct sum `L_j = K_j` and
`cⱼ = μⱼ^q`; for blocks with multiplicities `L_j` is the isometry placing a bond pair on all
copies of block `j` (`MPSTensor.copyIsometry`). -/
theorem exists_norm_gram_sum_sub_le
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R : ℝ) (c : Fin b → ℂ)
      (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ),
      (∀ j, ‖c j‖ ≤ R) → (∀ j, ‖L j‖ ≤ 1) → ∀ q : ℕ,
      ‖(∑ j, c j • (physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ))ᴴ *
          ∑ j, c j • (physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ) -
        ∑ j, ((‖c j‖ ^ 2 : ℝ) : ℂ) • (L j *
          ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (L j)ᴴ)‖ ≤
        R ^ 2 * K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  classical
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set x := Real.exp (-γ / correlationLength lam₂)
  choose Kd hKd hdiag using fun j => exists_norm_gram_blockTensor_sub_le (Aj j) (hN j) (hA j)
    (hσ j) (htr j) (hfix j) (hlam j) hγ0 hγ
  have hoff : ∀ j k, ∃ K : ℝ, 0 ≤ K ∧ (j ≠ k → ∀ q : ℕ,
      ‖(physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj k) q)‖ ≤
        K * x ^ q) := fun j k => by
    by_cases hjk : j = k
    · exact ⟨0, le_rfl, fun h => absurd hjk h⟩
    · obtain ⟨K, hK, h⟩ := exists_norm_gram_blockTensor_mixed_le (Aj j) (Aj k) hl
        (hmix k j (Ne.symm hjk)) hγ0 hγ
      exact ⟨K, hK, fun _ => h⟩
  choose Ko hKo hoffb using hoff
  have hx : 0 ≤ x := (Real.exp_pos _).le
  refine ⟨∑ j, Kd j + ∑ j, ∑ k, Ko j k,
    add_nonneg (Finset.sum_nonneg fun j _ => hKd j)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hKo j k),
    fun R c L hc hL q => ?_⟩
  set G : (j k : Fin b) → Matrix (Fin (Dj j) × Fin (Dj j)) (Fin (Dj k) × Fin (Dj k)) ℂ :=
    fun j k => (physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj k) q)
  have hcoef : ∀ j k, ‖star (c j) * c k‖ ≤ R ^ 2 := fun j k => by
    rw [norm_mul, norm_star, sq]
    exact mul_le_mul (hc j) (hc k) (norm_nonneg _) ((norm_nonneg _).trans (hc j))
  -- A term `a • (L_j X L_kᴴ)` with `|a| ≤ R²` has norm at most `R² ‖X‖`.
  have hterm : ∀ (j k : Fin b) (a : ℂ) (X : Matrix (Fin (Dj j) × Fin (Dj j))
      (Fin (Dj k) × Fin (Dj k)) ℂ), ‖a‖ ≤ R ^ 2 →
      ‖a • (L j * X * (L k)ᴴ)‖ ≤ R ^ 2 * ‖X‖ := fun j k a X ha => by
    rw [norm_smul]
    refine mul_le_mul ha ?_ (norm_nonneg _) (sq_nonneg R)
    calc ‖L j * X * (L k)ᴴ‖ ≤ ‖L j‖ * ‖X‖ * ‖(L k)ᴴ‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (by gcongr; exact Matrix.l2_opNorm_mul _ _)
      _ ≤ 1 * ‖X‖ * 1 := by
          rw [Matrix.l2_opNorm_conjTranspose]
          gcongr
          exacts [hL j, hL k]
      _ = ‖X‖ := by ring
  have hsplit : (∑ j, c j • (physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ))ᴴ *
        ∑ j, c j • (physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ) -
        ∑ j, ((‖c j‖ ^ 2 : ℝ) : ℂ) • (L j *
          ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (L j)ᴴ) =
      ∑ j, (star (c j) * c j) • (L j *
        (G j j - (σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (L j)ᴴ) +
      ∑ j, ∑ k ∈ Finset.univ.erase j, (star (c j) * c k) • (L j * G j k * (L k)ᴴ) := by
    have hprod : ∀ j k, (c j • (physicalMatrix (blockTensor (Aj j) q) * (L j)ᴴ))ᴴ *
        (c k • (physicalMatrix (blockTensor (Aj k) q) * (L k)ᴴ)) =
          (star (c j) * c k) • (L j * G j k * (L k)ᴴ) := fun j k => by
      simp only [G, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc, mul_comm (c k)]
    have hnorm : ∀ j, ((‖c j‖ ^ 2 : ℝ) : ℂ) = star (c j) * c j := fun j => by
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [Matrix.conjTranspose_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hprod, hnorm,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    simp only [hprod]
    abel
  rw [hsplit, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (hterm j j _ _ (hcoef j j)).trans ?_
    calc R ^ 2 * ‖G j j - (σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)‖
        ≤ R ^ 2 * (Kd j * x ^ q) := by gcongr; exact hdiag j q
      _ = R ^ 2 * Kd j * x ^ q := by ring
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j Finset.univ)
        fun k _ _ => mul_nonneg (mul_nonneg (sq_nonneg R) (hKo j k)) (pow_nonneg hx q)))
    refine (hterm j k _ _ (hcoef j k)).trans ?_
    calc R ^ 2 * ‖G j k‖ ≤ R ^ 2 * (Ko j k * x ^ q) := by
          gcongr; exact hoffb j k (Ne.symm (Finset.ne_of_mem_erase hk)) q
      _ = R ^ 2 * Ko j k * x ^ q := by ring

open scoped Matrix.Norms.L2Operator in
/-- **Rate of the Gram matrices.** Let the blocks `A_j` be normal in the gauge
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`, and let `λ₂` with
`|λ₂| < 1` bound the moduli of the eigenvalues other than `1` of every `E_{A_j}` and of all
eigenvalues of the mixed transfer maps `E_{jj'}` of distinct blocks. For `0 < γ < 1` there is `K`
such that for all weights `μⱼ` with `|μⱼ| ≤ 1` the Gram matrix of the `q`-site blocked direct sum
`⊕ⱼ μⱼ A_j` satisfies `‖Bᴴ B - ∑ⱼ |μⱼ|^{2q} K_j (σ_jᵀ ⊗ 1) K_jᴴ‖ ≤ K e^{-γ q/ξ}` for `q ≥ 1`;
the limit is written as `∑ⱼ K_j ((|μⱼ|^{2q} σ_j)ᵀ ⊗ 1) K_jᴴ`. This is
`exists_norm_gram_sum_sub_le` with `L_j = K_j` and `cⱼ = μⱼ^q`. -/
theorem exists_norm_gram_blockTensor_blockSum_sub_le (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : Fin b → ℂ, (∀ j, ‖μ j‖ ≤ 1) → ∀ q : ℕ, q ≠ 0 →
      ‖(physicalMatrix (blockTensor (blockSum Aj ι μ) q))ᴴ *
          physicalMatrix (blockTensor (blockSum Aj ι μ) q) -
        blockSumGramLimit ι (fun j => (((‖μ j‖ ^ q) ^ 2 : ℝ) : ℂ) • σ j)‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, h⟩ := exists_norm_gram_sum_sub_le (D := D) hN hA hσ htr hfix hl hlam hmix hγ0 hγ
  refine ⟨K, hK, fun μ hμ q hq => ?_⟩
  have h' := h 1 (fun j => μ j ^ q) (fun j => pairEmbedding (ι j))
    (fun j => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hμ j))
    (fun j => Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
      (conjTranspose_pairEmbedding_mul_self (hι j))) q
  rw [one_pow, one_mul] at h'
  rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hq, blockSumGramLimit_smul]
  simpa only [norm_pow] using h'

/-! ### The limits -/

section Limits

variable (hι : ∀ j, Function.Injective (ι j))
  (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
  {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
include hι hdisj

omit hι hdisj in
/-- `P_∞` is positive semidefinite. -/
private theorem posSemidef_blockSumPosLimit : (blockSumPosLimit ι σ).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun j _ => ?_
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
  exact (Matrix.posSemidef_transpose_iff.2
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (σ j)))).kronecker Matrix.PosSemidef.one

/-- `P_∞² = ∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ`. -/
private theorem blockSumPosLimit_mul_self (hσ : ∀ j, (σ j).PosSemidef) :
    blockSumPosLimit ι σ * blockSumPosLimit ι σ = blockSumGramLimit ι σ := by
  rw [blockSumPosLimit, sum_pairEmbedding_mul_sum_pairEmbedding hι hdisj, blockSumGramLimit]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.transpose_mul,
    CFC.sqrt_mul_sqrt_self (σ j) (hσ j).nonneg]

/-- `P_∞ Q = 0`. -/
private theorem blockSumPosLimit_mul_offBlockProj : blockSumPosLimit ι σ * offBlockProj ι = 0 := by
  have h := sum_mul_offBlockProj hι hdisj (γ := Fin D × Fin D) fun j => pairEmbedding (ι j) *
    ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ))
  exact h

/-- `Q P_∞ = 0`. -/
private theorem offBlockProj_mul_blockSumPosLimit : offBlockProj ι * blockSumPosLimit ι σ = 0 := by
  have h := offBlockProj_mul_sum hι hdisj (γ := Fin D × Fin D) fun j =>
    ((CFC.sqrt (σ j))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)) * (pairEmbedding (ι j))ᴴ
  simpa only [blockSumPosLimit, Matrix.mul_assoc] using h

omit hι hdisj in
/-- `∑ⱼ K_j K_jᴴ + Q = 1`. -/
private theorem sum_pairEmbedding_mul_conjTranspose_add_offBlockProj :
    ∑ j, pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ + offBlockProj ι = 1 := by
  rw [offBlockProj, add_sub_cancel]

/-- **Strict positivity of the limit.** If every `ι_j` is injective, distinct `ι_j` have
disjoint ranges, and every `σ_j` is positive definite with trace one, then
`∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ + Q ≥ c` for some `c > 0`. -/
theorem exists_pos_algebraMap_le_blockSumGramLimit_add (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) :
    ∃ c : ℝ, 0 < c ∧
      algebraMap ℝ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) c ≤
        blockSumGramLimit ι σ + offBlockProj ι := by
  have hc : ∀ j, ∃ c : ℝ, 0 < c ∧
      algebraMap ℝ (Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) c ≤ σ j := fun j => by
    have := Matrix.neZero_of_trace_eq_one (htr j)
    have hsp : IsStrictlyPositive (σ j) := (hσ j).isStrictlyPositive
    obtain ⟨c, hc, hcb⟩ := (CFC.exists_pos_algebraMap_le_iff (σ j)
      hsp.nonneg.isSelfAdjoint).2 fun x hx => hsp.spectrum_pos hx
    exact ⟨c, hc, hcb⟩
  choose c hc0 hcσ using hc
  set c₀ : ℝ := 1 / (1 + ∑ j, 1 / c j)
  have hS : 0 ≤ ∑ j, 1 / c j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hc0 j)).le
  have hc₀ : 0 < c₀ := by positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hc₀j : ∀ j, c₀ ≤ c j := fun j => by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / c j ≤ ∑ j, 1 / c j :=
      Finset.single_le_sum (f := fun j => 1 / c j) (fun j _ => (one_div_pos.2 (hc0 j)).le)
        (Finset.mem_univ j)
    have h1 : c j * (1 / c j) = 1 := mul_one_div_cancel (hc0 j).ne'
    nlinarith [hc0 j]
  refine ⟨c₀, hc₀, ?_⟩
  -- Each block: `σ_j - c₀ ≥ 0`.
  have hblock : ∀ j, (σ j - c₀ • (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)).PosSemidef :=
    fun j => by
      have h := (algebraMap_mono (Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) (hc₀j j)).trans (hcσ j)
      rwa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  have hkron : ∀ j, (σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) - c₀ • 1 =
      (σ j - c₀ • 1)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) := fun j => by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_eq_add_neg,
      sub_eq_add_neg, Matrix.add_kronecker, ← neg_smul, ← neg_smul, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one]
  have hone := sum_pairEmbedding_mul_conjTranspose_add_offBlockProj (ι := ι)
  have hexp : blockSumGramLimit ι σ + offBlockProj ι -
      c₀ • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) =
      ∑ j, pairEmbedding (ι j) * ((σ j)ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) -
        c₀ • 1) * (pairEmbedding (ι j))ᴴ + (1 - c₀) • offBlockProj ι := by
    rw [← hone, smul_add, Finset.smul_sum, blockSumGramLimit, sub_smul, one_smul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Finset.sum_sub_distrib]
    abel
  rw [hexp]
  refine Matrix.PosSemidef.add (Matrix.posSemidef_sum _ fun j _ => ?_) ?_
  · rw [hkron]
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same
      ((Matrix.posSemidef_transpose_iff.2 (hblock j)).kronecker Matrix.PosSemidef.one) _
  · exact (posSemidef_offBlockProj hι hdisj).smul (sub_nonneg.2 hc₀1)

end Limits

open scoped Matrix.Norms.L2Operator in
/-- **Hölder bound for positive parts.** For every matrix `B` and every positive semidefinite
`P`, `‖(Bᴴ B)^{1/2} - P‖ ≤ ‖Bᴴ B - P²‖^{1/2}`: the bound `‖√a - √b‖ ≤ √‖a - b‖`
(`CFC.norm_sqrt_sub_sqrt_le`; arXiv:2103.13367, Supplemental Material, eq. (26)) at `b = P²`. -/
theorem _root_.Matrix.norm_polarPos_sub_le_sqrt {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : Matrix m n ℂ) {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    ‖Matrix.polarPos B - P‖ ≤ Real.sqrt ‖Bᴴ * B - P * P‖ := by
  have hsq : CFC.sqrt (P * P) = P := CFC.sqrt_unique rfl hP.nonneg
  have hnn : 0 ≤ P * P := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rw [hP.isHermitian.eq] at h
    exact h.nonneg
  have h := CFC.norm_sqrt_sub_sqrt_le (Matrix.posSemidef_conjTranspose_mul_self B).nonneg hnn
  rwa [hsq] at h

/-! ### The rate of the positive part -/

open scoped Matrix.Norms.L2Operator in
/-- **Rate of the positive part** for a direct sum of blocks with overlapping states. In the
setting of `exists_norm_gram_blockTensor_blockSum_sub_le`, the positive part `P` of the
`q`-site blocked direct sum with unit weights satisfies `‖P - P_∞‖ ≤ K e^{-γ q/ξ}` for `q ≥ 1`,
with `P_∞ = ∑ⱼ K_j ((√σ_j)ᵀ ⊗ 1) K_jᴴ`.

This replaces arXiv:2307.01696, Supplemental Material, eq. (S5), which asserts `P = P_∞`'s
finite-`q` analogue `⊕ⱼ P_j` exactly; that identity fails when the `q`-site states of distinct
blocks overlap (`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`). -/
theorem exists_norm_polarPos_blockTensor_blockSum_sub_le (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ, q ≠ 0 →
      ‖Matrix.polarPos (physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q)) -
        blockSumPosLimit ι σ‖ ≤ K * Real.exp (-γ / correlationLength lam₂) ^ q := by
  obtain ⟨K, hK, hG₀⟩ := exists_norm_gram_blockTensor_blockSum_sub_le hι hdisj hN hA hσ htr
    hfix hl hlam hmix hγ0 hγ
  have hG : ∀ q : ℕ, q ≠ 0 →
      ‖(physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q))ᴴ *
          physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q) - blockSumGramLimit ι σ‖ ≤
        K * Real.exp (-γ / correlationLength lam₂) ^ q := fun q hq => by
    simpa using hG₀ (fun _ => 1) (fun _ => norm_one.le) q hq
  obtain ⟨c, hc, hcb⟩ := exists_pos_algebraMap_le_blockSumGramLimit_add hι hdisj hσ htr
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨K / Real.sqrt c, by positivity, fun q hq => ?_⟩
  set B := physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q)
  set P := Matrix.polarPos B
  set Q := offBlockProj ι
  have hQ := posSemidef_offBlockProj hι hdisj (ι := ι)
  have hQH : Qᴴ = Q := (isHermitian_offBlockProj (ι := ι)).eq
  have hQQ : Q * Q = Q := offBlockProj_mul_self hι hdisj
  have hBQ : B * Q = 0 := by
    rw [show B = _ from physicalMatrix_blockTensor_blockSum_one hι hdisj hq]
    exact sum_mul_offBlockProj hι hdisj _
  have hPQ : P * Q = 0 := by
    rw [show P = (Matrix.polarIso B)ᴴ * B from (Matrix.conjTranspose_polarIso_mul_self B).symm,
      Matrix.mul_assoc, hBQ, Matrix.mul_zero]
  have hPH : Pᴴ = P := (Matrix.posSemidef_polarPos B).isHermitian.eq
  have hQP : Q * P = 0 := by
    have := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, hPH, hQH, Matrix.conjTranspose_zero] at this
  have hsq : CFC.sqrt (Bᴴ * B + Q) = P + Q := by
    refine CFC.sqrt_unique ?_ ((Matrix.posSemidef_polarPos B).add hQ).nonneg
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPQ, hQP, hQQ, Matrix.polarPos_mul_polarPos]
    abel
  have hsqLim : CFC.sqrt (blockSumGramLimit ι σ + Q) = blockSumPosLimit ι σ + Q := by
    refine CFC.sqrt_unique ?_ ((posSemidef_blockSumPosLimit (ι := ι) (σ := σ)).add hQ).nonneg
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, blockSumPosLimit_mul_offBlockProj hι hdisj,
      offBlockProj_mul_blockSumPosLimit hι hdisj, hQQ,
      blockSumPosLimit_mul_self hι hdisj fun j => (hσ j).posSemidef]
    abel
  have hlip := CFC.norm_sqrt_sub_sqrt_le_div
    ((Matrix.posSemidef_conjTranspose_mul_self B).add hQ).nonneg hc hcb
  rw [hsq, hsqLim, add_sub_add_right_eq_sub, add_sub_add_right_eq_sub] at hlip
  calc ‖P - blockSumPosLimit ι σ‖ ≤ ‖Bᴴ * B - blockSumGramLimit ι σ‖ / Real.sqrt c := hlip
    _ ≤ K * Real.exp (-γ / correlationLength lam₂) ^ q / Real.sqrt c := by
        gcongr; exact hG q hq
    _ = K / Real.sqrt c * Real.exp (-γ / correlationLength lam₂) ^ q := by ring

end MPSTensor
