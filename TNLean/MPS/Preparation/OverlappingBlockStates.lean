/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.OverlappingBlockError
import TNLean.MPS.Preparation.OverlappingBlockInjectivity

/-!
# Overlapping blocks of unequal lengths with arbitrary weights

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares the fixed point of a
translation-invariant MPS that is not normal as `∑ⱼ αⱼ (⊗ₖ |ω_j⟩)` followed by the isometries of
the blocked tensor. This file bounds the error of such a state for a direct sum of normal blocks
`A_j` whose `q`-site states may overlap, for blocks of unequal lengths `ℓ_k ≥ q`, as in the
Supplemental Material, proof of Theorem 1 ("all of the same size, `q_N`, except for the last
one, which may be larger"), and for every vector of weights.

Let `V_k` be the isometric factor of the polar decomposition of the `ℓ_k`-site blocked tensor of
the direct sum `⊕ⱼ A_j` with unit weights, the blocks placed on the bond coordinates `ι_j`, and
let `ω_j` be the pair of the fixed point `σ_j` of block `j`, placed along `ι_j`. For weights
`βⱼ`, not all zero, and the amplitudes `αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}`, the state
`|ψ⟩ = ∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` approximates the normalized vector `∑ⱼ βⱼ |φ_N(A_j)⟩` with error
`1 - |⟨ψ|φ⟩| ≤ C M e^{-γ q/ξ}` (`MPSTensor.exists_one_sub_norm_inner_sum_blockIsometryState_le`),
where `ξ` bounds the correlation lengths of the blocks and of their mixed transfer maps. The
constant `C` does not depend on the weights. For the canonical form
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of eq. (S2), `|φ_N(A)⟩ = ∑ⱼ βⱼ |φ_N(A_j)⟩` with
`βⱼ = ∑ₖ μ_{j,k}^N` (eqs. (S3) and (S4)), so this bounds the error for every multiplicity and
every complex weight, without the factor `(min(1, ∑ⱼ |βⱼ|²))^{-1/2}` of
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`.

The steps:

* the `ℓ`-site blocked tensor of `A_j`, placed along `ι_j`, is `V P K_j K_jᴴ`, with `V P` the
  polar decomposition of the blocked direct sum and `K_j` the isometry placing the bond pairs of
  block `j` (`MPSTensor.blockTensor_blockSum_single`), so `|φ_N(A_j)⟩` is `⊗ₖ V_k` applied to the
  periodic state of the tensors `P_k K_j K_jᴴ` (`MPSTensor.mpvState_eq_blockIsoVector`);
* since `V_k` is an isometry on the bond pairs of the blocks
  (`MPSTensor.exists_isInjectiveOn_blockTensor_blockSum`), the overlaps
  `z_{jj'} = ⟨(⊗ₖ V_k) ⊗ₖ ω_j | φ_N(A_{j'})⟩` are traces of products of mixed transfer matrices
  (`MPSTensor.inner_blockIsometryState_embedPair_mpvState`);
* `P_k` is within `K e^{-γ ℓ_k/ξ}` of the limit `P_∞`
  (`MPSTensor.exists_norm_polarPos_blockTensor_blockSum_sub_le`), whose mixed transfer matrix
  against the fixed point of block `j` after `K_{j'} K_{j'}ᴴ` is the idempotent of trace one for
  `j = j'` and zero otherwise (`MPSTensor.mixedMapLM_blockSumPosLimit_mul_apply`), so
  `|z_{jj'} - δ_{jj'}| ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`
  (`MPSTensor.exists_norm_trace_prod_blockPosTensor_sub_le`, by the telescoping estimate
  `Matrix.exists_norm_trace_prod_ofFn_sub_trace_pow_le`);
* the squared norm of `∑ⱼ βⱼ |φ_N(A_j)⟩` is `∑ⱼ |βⱼ|²` up to the relative error
  `K e^{-γ N/ξ}` (`MPSTensor.exists_abs_sum_norm_sq_sum_mpv_sub_le`).

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Local fix (isometry of the unweighted direct sum):** the isometries `V_k` are those of the
direct sum `⊕ⱼ A_j` with unit weights and one copy of each block, and the weights enter only
through the amplitudes `αⱼ`; the source applies the isometry of the blocked tensor of `A`
itself, whose positive part does not have the block form (S5) when the blocks overlap or repeat.
Documented in `docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

## Main declarations

* `MPSTensor.blockPosTensor` — the tensor `P K_j K_jᴴ` of block `j`.
* `MPSTensor.blockTensor_blockSum_single`, `MPSTensor.mpvState_eq_blockIsoVector` — the states of
  the blocks after the isometries of the direct sum.
* `MPSTensor.inner_blockIsometryState_embedPair_mpvState` — the overlaps `z_{jj'}`.
* `MPSTensor.norm_sum_smul_blockIsometryState` — `|ψ⟩` is a unit vector.
* `MPSTensor.exists_norm_trace_prod_blockPosTensor_sub_le` — `|z_{jj'} - δ_{jj'}|`.
* `MPSTensor.exists_one_sub_norm_inner_sum_blockIsometryState_le` — the error.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, paragraph "Long-range MPS using measurements", Supplemental Material,
  eqs. (S2)–(S7), Lemma 1'(ii) and the proof of Theorem 1.
* [PSC21] L. Piroli, G. Styliaris, J. I. Cirac,
  *Quantum circuits assisted by local operations and classical communication:
  transformations and phases of matter*,
  arXiv:2103.13367, Supplemental Material, eqs. `final_eq` to `finished`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators InnerProductSpace
open Matrix

/-! ### Telescoping for products of different matrices -/

open scoped Matrix.Norms.L2Operator in
/-- **Telescoping for the trace of a product.** For a finite index type there is `K ≥ 0` such
that for every matrix `E` whose powers have norm at most `c` and all matrices `X_0, …, X_{M-1}`
within `δ` of `E`, `|Tr(X_0 ⋯ X_{M-1}) - Tr E^M| ≤ K c² (M δ) e^{c M δ}`.

arXiv:2103.13367, Supplemental Material, eqs. `final_eq` to `finished`, for a product of
different matrices (`norm_prod_range_sub_pow_le_of_forall_norm_pow_le`). -/
theorem Matrix.exists_norm_trace_prod_ofFn_sub_trace_pow_le (κ : Type*) [Fintype κ]
    [DecidableEq κ] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Matrix κ κ ℂ) (c : ℝ), (∀ n : ℕ, ‖E ^ n‖ ≤ c) →
      ∀ (M : ℕ) (X : Fin M → Matrix κ κ ℂ) (δ : ℝ), (∀ k, ‖X k - E‖ ≤ δ) →
        ‖Matrix.trace (List.ofFn X).prod - Matrix.trace (E ^ M)‖ ≤
          K * c ^ 2 * (M * δ) * Real.exp (c * (M * δ)) := by
  set trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap κ ℂ ℂ)
  refine ⟨‖trL‖, norm_nonneg _, fun E c hE M X δ hX => ?_⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hc : 0 ≤ c := (norm_nonneg _).trans (hE 0)
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hX ⟨0, hM⟩)
  set Y : ℕ → Matrix κ κ ℂ := fun n => if h : n < M then X ⟨n, h⟩ else E
  have hY : ∀ n, ‖Y n - E‖ ≤ δ := fun n => by
    simp only [Y]
    split_ifs with h
    · exact hX _
    · rw [sub_self, norm_zero]; exact hδ
  have hprod : List.ofFn X = (List.range M).map Y := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < M := by simpa using h1
    simp [Y, hi]
  have htel := norm_prod_range_sub_pow_le_of_forall_norm_pow_le hE hY M
  have hgeom := one_add_pow_sub_one_le_mul_exp (mul_nonneg hc hδ) M
  have htr : ‖Matrix.trace (List.ofFn X).prod - Matrix.trace (E ^ M)‖ ≤
      ‖trL‖ * ‖(List.ofFn X).prod - E ^ M‖ := by
    rw [← Matrix.trace_sub]
    exact trL.le_opNorm _
  rw [hprod] at htr ⊢
  calc _ ≤ ‖trL‖ * ‖((List.range M).map Y).prod - E ^ M‖ := htr
    _ ≤ ‖trL‖ * (c * ((1 + c * δ) ^ M - 1)) := by gcongr
    _ ≤ ‖trL‖ * (c * (M * (c * δ) * Real.exp (M * (c * δ)))) := by gcongr
    _ = ‖trL‖ * c ^ 2 * (M * δ) * Real.exp (c * (M * δ)) := by ring_nf

namespace MPSTensor

variable {d D b : ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-! ### The states of the blocks after the isometries of the direct sum -/

/-- The tensor `P K_j K_jᴴ` of block `j`, with physical index the bond pair of the direct sum:
the positive part `P` of a tensor `B` of bond dimension `D`, restricted on the right to the bond
pairs of block `j` placed along `ι_j`. -/
noncomputable def blockPosTensor {n : ℕ} (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (B : MPSTensor n D) (j : Fin b) : MPSTensor (D * D) D :=
  ofPhysicalMatrixLM (Matrix.polarPos (physicalMatrix B) *
    (pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ))

/-- The blocked tensor of block `j` alone, placed along `ι_j`, is that of the direct sum with
unit weights followed by `K_j K_jᴴ`, for `q ≥ 1`. -/
private theorem physicalMatrix_blockTensor_blockSum_single
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (j : Fin b) {q : ℕ} (hq : q ≠ 0) :
    physicalMatrix (blockTensor (blockSum Aj ι (Pi.single j 1)) q) =
      physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q) *
        (pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ) := by
  classical
  have hL : physicalMatrix (blockTensor (blockSum Aj ι (Pi.single j 1)) q) =
      physicalMatrix (blockTensor (Aj j) q) * (pairEmbedding (ι j))ᴴ := by
    rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hq, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_pow, one_smul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_pow hq, zero_smul]
    · simp
  rw [hL, physicalMatrix_blockTensor_blockSum_one hι hdisj hq, Matrix.sum_mul,
    Finset.sum_eq_single j]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pairEmbedding (ι j))ᴴ,
      conjTranspose_pairEmbedding_mul_self (hι j), Matrix.one_mul]
  · intro k _ hk
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pairEmbedding (ι k))ᴴ,
      conjTranspose_pairEmbedding_mul_eq_zero (hdisj k j hk), Matrix.zero_mul, Matrix.mul_zero]
  · simp

/-- **The blocked tensor of one block through the isometry of the direct sum.** For `q ≥ 1`,
the `q`-site blocked tensor of block `j`, placed along `ι_j`, is `V` applied to the tensor
`P K_j K_jᴴ`, where `B = V P` is the polar decomposition of the blocked direct sum with unit
weights. -/
theorem blockTensor_blockSum_single (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (j : Fin b) {q : ℕ} (hq : q ≠ 0) :
    blockTensor (blockSum Aj ι (Pi.single j 1)) q =
      rotatePhysical (polarIsoMatrix (blockTensor (blockSum Aj ι fun _ => 1) q))
        (blockPosTensor ι (blockTensor (blockSum Aj ι fun _ => 1) q) j) := by
  apply physicalMatrix_injective
  rw [physicalMatrix_rotatePhysical, physicalMatrix_blockTensor_blockSum_single hι hdisj j hq]
  set B := blockTensor (blockSum Aj ι fun _ => 1) q
  change _ = polarIsoMatrix B * (Matrix.polarPos (physicalMatrix B) *
    (pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ)).submatrix (virtualPairEquiv D) id
  rw [polarIsoMatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    ← Matrix.mul_assoc (Matrix.polarIso _), Matrix.polarIso_mul_polarPos]

/-- **The state of one block after the isometries of the direct sum.** For a ring of `N ≥ 1`
sites cut into blocks of lengths `ℓ_k ≥ 1`, `|φ_N(A_j)⟩ = (⊗ₖ V_k) |φ_M(P_k K_j K_jᴴ)⟩`, where
`V_k P_k` is the polar decomposition of the `ℓ_k`-site blocked direct sum with unit weights and
`|φ_M(P_k K_j K_jᴴ)⟩` is the periodic state of the family of tensors `P_k K_j K_jᴴ` on the blocks.
-/
theorem mpvState_eq_blockIsoVector (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (j : Fin b) {M : ℕ} {ℓ : Fin M → ℕ}
    {N : ℕ} (hN : ∑ k, ℓ k = N) (hN0 : N ≠ 0) (hℓ : ∀ k, ℓ k ≠ 0) :
    mpvState (Aj j) N = blockIsoVector (fun k => blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)) hN
      ((EuclideanSpace.equiv (ι := Cfg (D * D) M) (𝕜 := ℂ)).symm fun τ =>
        mpvFamily (n := fun _ => D * D)
          (fun k => blockPosTensor ι (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)) j) τ) := by
  classical
  ext s
  rw [mpvState_apply, blockIsoVector_apply]
  have h1 : mpv (Aj j) s = mpv (blockSum Aj ι (Pi.single j 1)) s := by
    rw [mpv_blockSum hι hdisj _ hN0, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_pow, one_mul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_pow hN0, zero_mul]
    · simp
  rw [h1, mpv_eq_mpvFamily_blockTensor _ hN,
    show (fun k => blockTensor (blockSum Aj ι (Pi.single j 1)) (ℓ k)) = fun k =>
      rotatePhysical (polarIsoMatrix (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)))
        (blockPosTensor ι (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)) j) from
      funext fun k => blockTensor_blockSum_single hι hdisj j (hℓ k),
    mpvFamily_rotatePhysical]
  simp [EuclideanSpace.equiv, PiLp.toLp_apply]

/-- A configuration of bond pairs on which the product of the pairs `ω` of block `j`, placed
along `ι_j`, does not vanish lies in the bond pairs of the blocks. -/
theorem mem_blockPairs_of_pairProductState_embedPair_ne_zero (j : Fin b)
    (ω : Fin (Dj j) × Fin (Dj j) → ℂ) {M : ℕ} {c : Fin M → Fin D × Fin D}
    (hc : pairProductState (embedPair (ι j) ω) c ≠ 0) (k : Fin M) : c k ∈ blockPairs ι := by
  have hne := Finset.prod_ne_zero_iff.1 hc
  have h1 := hne k (Finset.mem_univ _)
  have h2 := hne ((finRotate M).symm k) (Finset.mem_univ _)
  rw [Equiv.apply_symm_apply] at h2
  obtain ⟨a, ha⟩ : (c k).1 ∈ Set.range (ι j) := by
    by_contra h
    exact h2 (embedPair_eq_zero ω (Or.inr h))
  obtain ⟨a', ha'⟩ : (c k).2 ∈ Set.range (ι j) := by
    by_contra h
    exact h1 (embedPair_eq_zero ω (Or.inl h))
  exact mem_blockPairs.2 ⟨j, a, a', Prod.ext ha ha'⟩

/-- The state `(⊗ₖ V_k) ⊗ₖ |ω⟩` of the blocked direct sum, written with the isometries of its
blocked tensors applied to the product of the pairs. -/
theorem blockIsometryState_eq_blockIsoVector (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ)
    {M : ℕ} {ℓ : Fin M → ℕ} {N : ℕ} (hN : ∑ k, ℓ k = N) :
    blockIsometryState A ω hN =
      blockIsoVector (fun k => blockTensor A (ℓ k)) hN (pairFamilyVector fun _ => ω) := by
  rw [blockIsometryState_eq_chainBlockIsometryState, chainBlockIsometryState]
  congr 1
  funext k
  exact chainBlockTensor_const A hN k

/-! ### The overlaps of the blocks -/

variable {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}

/-- **The overlaps of the blocks.** If the blocked direct sum with unit weights is injective on
the bond pairs of the blocks for every block length `ℓ_k ≥ 1`, then the overlap of
`(⊗ₖ V_k) ⊗ₖ |ω_j⟩`, with `ω_j` the pair of `σ_j ≥ 0` placed along `ι_j`, with `|φ_N(A_{j'})⟩`
is the trace of the ordered product of the mixed transfer matrices of `P_k K_{j'} K_{j'}ᴴ`
against the fixed-point tensor of `σ_j` placed along `ι_j`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii), with `V_k†V_k` the projector onto
the bond pairs of the blocks (`MPSTensor.inner_blockIsoVector_of_isInjectiveOn`). -/
theorem inner_blockIsometryState_embedPair_mpvState (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (hσ : ∀ j, (σ j).PosSemidef)
    (j j' : Fin b) {M : ℕ} [NeZero M] {ℓ : Fin M → ℕ} {N : ℕ} (hN : ∑ k, ℓ k = N)
    (hℓ : ∀ k, ℓ k ≠ 0)
    (hinj : ∀ k, IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))
      (blockPairs ι : Set (Fin D × Fin D))) :
    ⟪blockIsometryState (blockSum Aj ι fun _ => 1) (embedPair (ι j) (fixedPointPair (σ j))) hN,
        mpvState (Aj j') N⟫_ℂ =
      Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
        (blockPosTensor ι (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)) j')
        (fixedPointTensor (embeddedBlockState (ι j) (σ j))))).prod := by
  classical
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact (Finset.sum_pos (fun k _ => Nat.pos_of_ne_zero (hℓ k))
      ⟨0, Finset.mem_univ _⟩).ne'
  rw [blockIsometryState_eq_blockIsoVector, mpvState_eq_blockIsoVector hι hdisj j' hN hN0 hℓ,
    inner_blockIsoVector_of_isInjectiveOn hN (S := fun _ => (blockPairs ι : Set _)) hinj,
    ← sum_mpvFamily_mul_star_mpv, PiLp.inner_apply]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [RCLike.inner_apply, pairFamilyVector_apply, pairFamilyState_const,
      embedPair_fixedPointPair (hι j) (hσ j), ← mpv_fixedPointTensor]
    simp [EuclideanSpace.equiv, PiLp.toLp_apply]
  · rintro τ ⟨k, hk⟩
    by_cases h : pairFamilyVector (fun _ => embedPair (ι j) (fixedPointPair (σ j))) τ = 0
    · rw [h, star_zero, zero_mul]
    · exact absurd (mem_blockPairs_of_pairProductState_embedPair_ne_zero j _
        (by simpa only [pairFamilyVector_apply, pairFamilyState_const] using h) k) hk

/-- The states `(⊗ₖ V_k) ⊗ₖ |ω_j⟩` of distinct blocks are orthonormal when the blocked direct sum
is injective on the bond pairs of the blocks. -/
theorem inner_blockIsometryState_embedPair (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) (j j' : Fin b) {M : ℕ} [NeZero M] {ℓ : Fin M → ℕ} {N : ℕ}
    (hN : ∑ k, ℓ k = N)
    (hinj : ∀ k, IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))
      (blockPairs ι : Set (Fin D × Fin D))) :
    ⟪blockIsometryState (blockSum Aj ι fun _ => 1) (embedPair (ι j) (fixedPointPair (σ j))) hN,
        blockIsometryState (blockSum Aj ι fun _ => 1)
          (embedPair (ι j') (fixedPointPair (σ j'))) hN⟫_ℂ = if j = j' then 1 else 0 := by
  classical
  rw [blockIsometryState_eq_blockIsoVector, blockIsometryState_eq_blockIsoVector,
    inner_blockIsoVector_of_isInjectiveOn hN (S := fun _ => (blockPairs ι : Set _)) hinj,
    PiLp.inner_apply]
  · simp only [RCLike.inner_apply, pairFamilyVector_apply, pairFamilyState_const]
    trans ∑ c : Fin M → Fin D × Fin D, star (pairProductState
      (embedPair (ι j) (fixedPointPair (σ j))) c) *
        pairProductState (embedPair (ι j') (fixedPointPair (σ j'))) c
    · exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _
        fun _ => mul_comm _ _
    rw [pairProductState_inner]
    split_ifs with hjj
    · subst hjj
      rw [inner_embedPair_self (hι j), fixedPointPair_norm_sq (hσ j), htr j, one_pow]
    · rw [inner_embedPair_eq_zero_of_disjoint (hdisj j j' hjj), zero_pow (NeZero.ne M)]
  · rintro τ ⟨k, hk⟩
    by_cases h : pairFamilyVector (fun _ => embedPair (ι j) (fixedPointPair (σ j))) τ = 0
    · rw [h, star_zero, zero_mul]
    · exact absurd (mem_blockPairs_of_pairProductState_embedPair_ne_zero j _
        (by simpa only [pairFamilyVector_apply, pairFamilyState_const] using h) k) hk

/-- **The approximating state is a unit vector.** For unit amplitudes `α`, positive semidefinite
`σ_j` of trace one, and a blocked direct sum injective on the bond pairs of the blocks,
`∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ |ω_j⟩` is a unit vector. -/
theorem norm_sum_smul_blockIsometryState (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) {α : Fin b → ℂ} (hα : ∑ j, star (α j) * α j = 1) {M : ℕ}
    [NeZero M] {ℓ : Fin M → ℕ} {N : ℕ} (hN : ∑ k, ℓ k = N)
    (hinj : ∀ k, IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))
      (blockPairs ι : Set (Fin D × Fin D))) :
    ‖∑ j, α j • blockIsometryState (blockSum Aj ι fun _ => 1)
      (embedPair (ι j) (fixedPointPair (σ j))) hN‖ = 1 := by
  classical
  set ψ := ∑ j, α j • blockIsometryState (blockSum Aj ι fun _ => 1)
    (embedPair (ι j) (fixedPointPair (σ j))) hN
  have h : ⟪ψ, ψ⟫_ℂ = 1 := by
    simp only [ψ, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_blockIsometryState_embedPair hι hdisj hσ htr _ _ hN hinj, mul_ite, mul_one, mul_zero]
    rw [← hα]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]; simp [mul_comm]
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖ψ‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (Complex.ofReal_eq_one.1 h2)

/-! ### The overlaps near the limit -/

/-- `P_∞ K_{j'} K_{j'}ᴴ` is the limit `P_∞` of the weights `t = e_{j'}`, which keeps only the
block `j'`. -/
private theorem blockSumPosLimit_mul_pairEmbedding
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ)
    (j' : Fin b) :
    blockSumPosLimit ι σ * (pairEmbedding (ι j') * (pairEmbedding (ι j'))ᴴ) =
      blockSumPosLimit ι (fun k => ((((Pi.single j' 1 : Fin b → ℝ) k ^ 2 : ℝ)) : ℂ) • σ k) := by
  classical
  have hR : blockSumPosLimit ι (fun k => ((((Pi.single j' 1 : Fin b → ℝ) k ^ 2 : ℝ)) : ℂ) • σ k) =
      pairEmbedding (ι j') * ((CFC.sqrt (σ j'))ᵀ ⊗ₖ (1 : Matrix (Fin (Dj j')) (Fin (Dj j')) ℂ)) *
        (pairEmbedding (ι j'))ᴴ := by
    rw [blockSumPosLimit, Finset.sum_eq_single j']
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  rw [hR, blockSumPosLimit, Matrix.sum_mul, Finset.sum_eq_single j']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pairEmbedding (ι j'))ᴴ,
      conjTranspose_pairEmbedding_mul_self (hι j'), Matrix.one_mul]
  · intro k _ hk
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pairEmbedding (ι k))ᴴ,
      conjTranspose_pairEmbedding_mul_eq_zero (hdisj k j' hk), Matrix.zero_mul, Matrix.mul_zero]
  · simp

/-- **The mixed transfer maps of the limit.** The mixed transfer map of `P_∞ K_{j'} K_{j'}ᴴ`
against the fixed-point tensor of block `j`, placed along `ι_j`, is `ρ ↦ Tr(Π_j ρ) σ'_j` for
`j = j'`, with `Π_j = E_j E_jᴴ` and `σ'_j = E_j σ_j E_jᴴ`, and zero for `j ≠ j'`
(`MPSTensor.mixedMapLM_blockSumPosLimit_smul_apply` at the weights `t = e_{j'}`). -/
theorem mixedMapLM_blockSumPosLimit_mul_apply (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (hσ : ∀ j, (σ j).PosSemidef)
    (j j' : Fin b) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.mixedMapLM (ofPhysicalMatrixLM (blockSumPosLimit ι σ *
        (pairEmbedding (ι j') * (pairEmbedding (ι j'))ᴴ)))
        (fixedPointTensor (embeddedBlockState (ι j) (σ j))) ρ =
      if j = j' then (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ * ρ).trace •
        embeddedBlockState (ι j) (σ j) else 0 := by
  classical
  rw [blockSumPosLimit_mul_pairEmbedding hι hdisj σ j',
    mixedMapLM_blockSumPosLimit_smul_apply hι hdisj hσ _ (fun k => by
      rw [Pi.single_apply]; split_ifs <;> norm_num) j ρ]
  by_cases h : j = j'
  · subst h; simp
  · simp [h]

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)}

open scoped Matrix.Norms.L2Operator in
/-- **The overlaps of the blocks near the limit.** In the setting of
`exists_norm_polarPos_blockTensor_blockSum_sub_le`, for blocks `j, j'` there is `C > 0` such that
for every cutting of a ring into `M ≥ 1` blocks of lengths `ℓ_k ≥ q ≥ 1`, the trace `z_{jj'}` of
the ordered product of the mixed transfer matrices of `P_k K_{j'} K_{j'}ᴴ` against the
fixed-point tensor of block `j` satisfies `|z_{jj'} - δ_{jj'}| ≤ C y e^{C y}` with
`y = M e^{-γ q/ξ}`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii), and arXiv:2103.13367,
Supplemental Material, eqs. `final_eq` to `finished`: the limit of the mixed transfer matrices
is idempotent with trace one for `j = j'` and zero otherwise
(`mixedMapLM_blockSumPosLimit_mul_apply`), and the telescoping estimate
`Matrix.exists_norm_trace_prod_ofFn_sub_trace_pow_le` bounds the product. -/
theorem exists_norm_trace_prod_blockPosTensor_sub_le (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j) {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) (j j' : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) (q : ℕ), q ≠ 0 → (∀ k, q ≤ ℓ k) →
      ‖Matrix.trace (List.ofFn fun k => transferMatrix (Kraus.mixedMapLM
          (blockPosTensor ι (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k)) j')
          (fixedPointTensor (embeddedBlockState (ι j) (σ j))))).prod -
            (if j = j' then 1 else 0)‖ ≤
        C * (M * Real.exp (-γ / correlationLength lam₂) ^ q) *
          Real.exp (C * (M * Real.exp (-γ / correlationLength lam₂) ^ q)) := by
  classical
  have : NeZero (Dj j) := Matrix.neZero_of_trace_eq_one (htr j)
  have : NeZero D := ⟨fun h => by subst h; exact (ι j 0).elim0⟩
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_blockSum_sub_le hι hdisj hN hA hσ
    htr hfix hl hlam hmix hγ0 hγ
  set F := fixedPointTensor (embeddedBlockState (ι j) (σ j))
  set Ψ := mixedTransferMatrixLeft F
  set K₃ := ‖LinearMap.toContinuousLinearMap Ψ‖
  have hK₃ : 0 ≤ K₃ := norm_nonneg _
  have hΨ : ∀ G, ‖Ψ G‖ ≤ K₃ * ‖G‖ := (LinearMap.toContinuousLinearMap Ψ).le_opNorm
  set Pj := pairEmbedding (ι j') * (pairEmbedding (ι j'))ᴴ
  have hPj : ‖Pj‖ ≤ 1 := by
    have h1 := Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
      (conjTranspose_pairEmbedding_mul_self (hι j'))
    calc ‖Pj‖ ≤ ‖pairEmbedding (ι j')‖ * ‖(pairEmbedding (ι j'))ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- The limit `τ_∞` of the mixed transfer matrices.
  set R : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.mixedMapLM (ofPhysicalMatrixLM
    (blockSumPosLimit ι σ * (pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ))) F
  have hR : ∀ ρ, R ρ = (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ * ρ).trace •
      embeddedBlockState (ι j) (σ j) := fun ρ => by
    have h := mixedMapLM_blockSumPosLimit_mul_apply hι hdisj (fun j => (hσ j).posSemidef) j j ρ
    rwa [ite_eq_left rfl] at h
  have h1 : (coordEmbedding (ι j) * (coordEmbedding (ι j))ᴴ *
      embeddedBlockState (ι j) (σ j)).trace = 1 := by
    rw [trace_coordEmbedding_mul_conjTranspose_mul_embeddedBlockState hι, htr j]
  have hidemR : IsIdempotentElem (transferMatrix R) := by
    rw [IsIdempotentElem, ← transferMatrix_comp]
    exact congrArg transferMatrix (isIdempotentElem_of_apply_eq_trace_smul hR h1)
  have htrR : Matrix.trace (transferMatrix R) = 1 := by
    rw [trace_transferMatrix_eq_linearMap_trace, trace_of_apply_eq_trace_smul hR, h1]
  set E := Ψ (blockSumPosLimit ι σ * Pj)
  have hE : E = if j = j' then transferMatrix R else 0 := by
    split_ifs with h
    · subst h; rfl
    · change transferMatrix (Kraus.mixedMapLM (ofPhysicalMatrixLM
        (blockSumPosLimit ι σ * Pj)) F) = 0
      have h0 : Kraus.mixedMapLM (ofPhysicalMatrixLM (blockSumPosLimit ι σ * Pj)) F = 0 :=
        LinearMap.ext fun ρ => by
          rw [mixedMapLM_blockSumPosLimit_mul_apply hι hdisj (fun j => (hσ j).posSemidef) j j' ρ,
            ite_eq_right h, LinearMap.zero_apply]
      rw [h0]
      exact map_zero (transferMatrixLM (D := D))
  set c := ‖(1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ + ‖transferMatrix R‖
  have hc : 0 ≤ c := by positivity
  have hEpow : ∀ n : ℕ, ‖E ^ n‖ ≤ c := fun n => by
    rcases n with _ | n
    · rw [pow_zero]; exact le_add_of_nonneg_right (norm_nonneg _)
    · rw [hE]
      split_ifs
      · rw [hidemR.pow_succ_eq]; exact le_add_of_nonneg_left (norm_nonneg _)
      · rw [zero_pow (Nat.succ_ne_zero n), norm_zero]; exact hc
  obtain ⟨K, hK, htel⟩ := Matrix.exists_norm_trace_prod_ofFn_sub_trace_pow_le (Fin D × Fin D)
  refine ⟨K * c ^ 2 * (K₃ * K₁) + c * (K₃ * K₁) + 1, by positivity,
    fun M _ ℓ q hq hℓ => ?_⟩
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hl.le
  have hδ : ∀ k, ‖Ψ (Matrix.polarPos (physicalMatrix
      (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))) * Pj) - E‖ ≤ K₃ * K₁ * x ^ q := fun k => by
    rw [← map_sub, ← Matrix.sub_mul]
    refine (hΨ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK₃
    calc ‖(Matrix.polarPos (physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))) -
          blockSumPosLimit ι σ) * Pj‖
        ≤ ‖Matrix.polarPos (physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))) -
          blockSumPosLimit ι σ‖ * ‖Pj‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ K₁ * x ^ (ℓ k) * 1 := mul_le_mul (hpos _ (by have := hℓ k; omega)) hPj (norm_nonneg _)
          (by positivity)
      _ ≤ K₁ * x ^ q := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (hℓ k)) hK₁
  have h := htel E c hEpow M _ _ hδ
  have hEM : Matrix.trace (E ^ M) = if j = j' then 1 else 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
    rw [hE, hn]
    split_ifs
    · rw [hidemR.pow_succ_eq, htrR]
    · rw [zero_pow (Nat.succ_ne_zero n), Matrix.trace_zero]
  rw [hEM] at h
  have hu : 0 ≤ (M : ℝ) * x ^ q := by positivity
  calc _ ≤ K * c ^ 2 * (M * (K₃ * K₁ * x ^ q)) * Real.exp (c * (M * (K₃ * K₁ * x ^ q))) := h
    _ = K * c ^ 2 * (K₃ * K₁) * (M * x ^ q) * Real.exp (c * (K₃ * K₁) * (M * x ^ q)) := by ring_nf
    _ ≤ (K * c ^ 2 * (K₃ * K₁) + c * (K₃ * K₁) + 1) * (M * x ^ q) *
        Real.exp ((K * c ^ 2 * (K₃ * K₁) + c * (K₃ * K₁) + 1) * (M * x ^ q)) := by
        have h1 : 0 ≤ K * c ^ 2 * (K₃ * K₁) := by positivity
        have h2 : 0 ≤ c * (K₃ * K₁) := by positivity
        gcongr <;> linarith

/-! ### The error -/

open scoped Matrix.Norms.L2Operator in
/-- **The error for overlapping blocks of unequal lengths and arbitrary weights.** Let the blocks
`A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`
(arXiv:2307.01696, eq. (5)), placed on the bond coordinates `ι_j`, let `λ₂` bound the moduli of
the eigenvalues other than `1` of every transfer map `E_{A_j}` and of all eigenvalues of the mixed
transfer maps `E_{jj'}`, `j ≠ j'`, with correlation length `ξ = -1/log|λ₂|`, and let
`0 < γ < 1`. There is `C > 0` such that the following holds for all weights `βⱼ`, not all
zero, and every cutting of a ring of `N` sites into `M ≥ 1` blocks of lengths `ℓ_k ≥ q` at which
the blocked direct sum with unit weights is injective on the bond pairs of the blocks. With
`αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}`, `ω_j` the pair of `σ_j` placed along `ι_j`, `V_k` the isometric
factor of the polar decomposition of the `ℓ_k`-site blocked direct sum, and
`|φ⟩ = ∑ⱼ βⱼ |φ_N(A_j)⟩`,
`1 - |⟨∑ⱼ αⱼ (⊗ₖ V_k) ⊗ₖ ω_j | φ/‖φ‖⟩| ≤ C M e^{-γ q/ξ}`.

arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the state of the paragraph
"Long-range MPS using measurements" in the scope of the module docstring: blocks of unequal
lengths as in the proof of Theorem 1, the rate of the mixed transfer maps, and the isometries of
the direct sum with unit weights. The constant does not depend on the weights, and there is no
factor `(min(1, ∑ⱼ |βⱼ|²))^{-1/2}`: the overlap is `∑_{j,j'} conj(βⱼ) β_{j'} z_{jj'}` divided by
`(∑ₗ |βₗ|²)^{1/2}`, with `|z_{jj'} - δ_{jj'}| ≤ C y e^{C y}`
(`exists_norm_trace_prod_blockPosTensor_sub_le`), and the squared norm of `|φ⟩` is
`∑ⱼ |βⱼ|²` up to a relative error (`exists_abs_sum_norm_sq_sum_mpv_sub_le`). The source states
the bound for `0 < γ < 1/2`; the range `γ < 1` is a project result. -/
theorem exists_one_sub_norm_inner_sum_blockIsometryState_le (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j) {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : Fin b → ℂ, β ≠ 0 → ∀ (M : ℕ) [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ}
      (hNs : ∑ k, ℓ k = N) (q : ℕ), (∀ k, q ≤ ℓ k) →
      (∀ k, IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) (ℓ k))
        (blockPairs ι : Set (Fin D × Fin D))) →
      ∀ φ : MPVSpace d N, (∀ s, φ s = ∑ j, β j * mpv (Aj j) s) →
        1 - ‖⟪∑ j, ghzAmplitude β j • blockIsometryState (blockSum Aj ι fun _ => 1)
            (embedPair (ι j) (fixedPointPair (σ j))) hNs, ((‖φ‖ : ℂ)⁻¹) • φ⟫_ℂ‖ ≤
          C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  classical
  set x := Real.exp (-γ / correlationLength lam₂) with hx_def
  have hxq : ∀ q : ℕ, Real.exp (-γ * q / correlationLength lam₂) = x ^ q := fun q =>
    Real.exp_neg_mul_div_eq_pow _ _ q
  simp_rw [hxq]
  have htriv : ∀ (C : ℝ), 1 ≤ C → ∀ (M : ℕ) (q : ℕ), 1 ≤ (M : ℝ) * x ^ q → ∀ v : ℂ,
      1 - ‖v‖ ≤ C * (M * x ^ q) := fun C hC M q hu v => by
    nlinarith [norm_nonneg v]
  rcases le_or_gt 1 ‖lam₂‖ with hl | hl
  · -- For `|λ₂| ≥ 1` the rate is at least `1` and the bound is trivial.
    have hx1 : 1 ≤ x := by
      rw [hx_def, neg_div_correlationLength]
      exact Real.one_le_exp (mul_nonneg hγ0.le (Real.log_nonneg hl))
    refine ⟨1, one_pos, fun β _ M _ ℓ N hNs q _ _ φ _ => htriv 1 le_rfl M q ?_ _⟩
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith [one_le_pow₀ hx1 (n := q)]
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hl.le
  have hz := fun j j' => exists_norm_trace_prod_blockPosTensor_sub_le (Aj := Aj) hι hdisj hN hA hσ
    htr hfix hl hlam hmix hγ0 hγ j j'
  choose Cz hCz hzb using hz
  set Cs := ∑ j, ∑ j', Cz j j'
  have hCs : ∀ j j', Cz j j' ≤ Cs := fun j j' =>
    (Finset.single_le_sum (f := fun j' => Cz j j') (fun _ _ => (hCz j _).le)
      (Finset.mem_univ j')).trans (Finset.single_le_sum (f := fun j => ∑ j', Cz j j')
        (fun _ _ => Finset.sum_nonneg fun _ _ => (hCz _ _).le) (Finset.mem_univ j))
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (hCz _ _).le
  obtain ⟨Kt, hKt, hnorm⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix hl hlam
    hmix hγ0 hγ
  set C' := (b : ℝ) ^ 2 * Cs + Cs + Kt + 1
  have hC' : 1 ≤ C' := by have : 0 ≤ (b : ℝ) ^ 2 * Cs := by positivity
                          linarith
  refine ⟨C' * Real.exp C' + 1, by positivity, fun β hβ M _ ℓ N hNs q hℓ hinj φ hφ => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  set ψ := ∑ j, ghzAmplitude β j • blockIsometryState (blockSum Aj ι fun _ => 1)
    (embedPair (ι j) (fixedPointPair (σ j))) hNs
  have hle1 : 1 - ‖⟪ψ, ((‖φ‖ : ℂ)⁻¹) • φ⟫_ℂ‖ ≤ 1 := by
    linarith [norm_nonneg ⟪ψ, ((‖φ‖ : ℂ)⁻¹) • φ⟫_ℂ]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact htriv _ (by nlinarith [Real.exp_pos C', Real.add_one_le_exp C']) M 0
      (by simp [hM]) _
  -- The overlaps of the blocks.
  have hℓ0 : ∀ k, ℓ k ≠ 0 := fun k => by have := hℓ k; omega
  set z : Fin b → Fin b → ℂ := fun j j' => ⟪blockIsometryState (blockSum Aj ι fun _ => 1)
    (embedPair (ι j) (fixedPointPair (σ j))) hNs, mpvState (Aj j') N⟫_ℂ
  have hzj : ∀ j j', ‖z j j' - if j = j' then 1 else 0‖ ≤ Cs * u * Real.exp (Cs * u) :=
    fun j j' => by
      simp only [z]
      rw [inner_blockIsometryState_embedPair_mpvState hι hdisj (fun j => (hσ j).posSemidef) j j'
        hNs hℓ0 hinj]
      refine (hzb j j' M ℓ q hq.ne' hℓ).trans ?_
      gcongr
      · exact hCs j j'
      · exact hCs j j'
  -- The overlap with the unnormalized target.
  set bb : ℝ := ∑ l, ‖β l‖ ^ 2
  have hbb : 0 < bb := sum_norm_sq_pos_of_ne_zero hβ
  set sb := Real.sqrt bb
  have hsb : 0 < sb := Real.sqrt_pos.2 hbb
  have hβle : ∀ j, ‖β j‖ ≤ sb := fun j =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))
  set S := ∑ j, ∑ j', star (β j) * β j' * z j j'
  have hinner : ⟪ψ, φ⟫_ℂ = ((sb : ℂ))⁻¹ * S := by
    have hψφ : ∀ j, ⟪blockIsometryState (blockSum Aj ι fun _ => 1)
        (embedPair (ι j) (fixedPointPair (σ j))) hNs, φ⟫_ℂ = ∑ j', β j' * z j j' := fun j => by
      simp only [z, PiLp.inner_apply, RCLike.inner_apply, hφ, mpvState_apply, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun s _ => by ring
    simp only [ψ, sum_inner, inner_smul_left, hψφ, S, Finset.mul_sum, ghzAmplitude, map_div₀,
      Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    simp only [sb, bb, RCLike.star_def]
    ring
  -- `S` is `∑ⱼ |βⱼ|²` up to the errors of the overlaps.
  have hSbb : ‖S / (bb : ℂ) - 1‖ ≤ (b : ℝ) ^ 2 * (Cs * u * Real.exp (Cs * u)) := by
    have hbbC : (bb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbb.ne'
    have hdiag : ∑ j, ∑ j', star (β j) * β j' * (if j = j' then (1 : ℂ) else 0) = (bb : ℂ) := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, bb,
        Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    have hrw : S / (bb : ℂ) - 1 =
        (∑ j, ∑ j', star (β j) * β j' * (z j j' - if j = j' then 1 else 0)) / (bb : ℂ) := by
      rw [eq_div_iff hbbC, sub_mul, div_mul_cancel₀ _ hbbC, one_mul, ← hdiag]
      simp only [S, mul_sub, Finset.sum_sub_distrib]
    rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbb, div_le_iff₀ hbb]
    calc ‖∑ j, ∑ j', star (β j) * β j' * (z j j' - if j = j' then 1 else 0)‖
        ≤ ∑ j : Fin b, ∑ j' : Fin b, bb * (Cs * u * Real.exp (Cs * u)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
          rw [norm_mul, norm_mul, norm_star]
          have hββ : ‖β j‖ * ‖β j'‖ ≤ bb := by
            calc ‖β j‖ * ‖β j'‖ ≤ sb * sb :=
                  mul_le_mul (hβle j) (hβle j') (norm_nonneg _) hsb.le
              _ = bb := Real.mul_self_sqrt hbb.le
          exact mul_le_mul hββ (hzj j j') (norm_nonneg _) hbb.le
      _ = (b : ℝ) ^ 2 * (Cs * u * Real.exp (Cs * u)) * bb := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- The norm of the target.
  set t := ‖φ‖
  have hqN : q ≤ N := by
    rw [← hNs]
    exact (hℓ 0).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have ht : |(t / sb) ^ 2 - 1| ≤ Kt * u := by
    have h := hnorm sb β hβle N
    have hT : t ^ 2 = ∑ s : Fin N → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 := by
      simp only [t, EuclideanSpace.norm_sq_eq, hφ]
    rw [← hT, Real.sq_sqrt hbb.le] at h
    have he : (t / sb) ^ 2 - 1 = (t ^ 2 - bb) / bb := by
      rw [div_pow, Real.sq_sqrt hbb.le]
      field_simp
    rw [he, abs_div, abs_of_pos hbb, div_le_iff₀ hbb]
    calc |t ^ 2 - bb| ≤ bb * Kt * x ^ N := h
      _ ≤ bb * Kt * u := by
          gcongr
          calc x ^ N ≤ x ^ q := pow_le_pow_of_le_one hx0 hx1 hqN
            _ ≤ u := le_mul_of_one_le_left (by positivity) hM
      _ = Kt * u * bb := by ring
  have hmain := one_sub_norm_div_le_of_norm_sub_le
    (div_nonneg (norm_nonneg φ) hsb.le) (by simpa using hSbb) (by simpa using ht)
  rw [div_eq_inv_mul] at hmain
  have hkey : (t / sb)⁻¹ * ‖S / (bb : ℂ)‖ =
      ‖⟪ψ, ((t : ℂ)⁻¹) • φ⟫_ℂ‖ := by
    rw [inner_smul_right, hinner, norm_mul, norm_mul, norm_inv, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsb,
      abs_of_nonneg (norm_nonneg φ), norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hbb, inv_div]
    have htφ : ‖φ‖ = t := rfl
    rcases eq_or_ne t 0 with h0 | h0
    · simp [htφ, h0]
    · have hbbs : bb = sb * sb := (Real.mul_self_sqrt hbb.le).symm
      rw [hbbs, htφ]
      field_simp
  rw [hkey] at hmain
  -- Combine.
  have hcomb : 1 - ‖⟪ψ, ((‖φ‖ : ℂ)⁻¹) • φ⟫_ℂ‖ ≤ C' * u * Real.exp (C' * u) := by
    refine hmain.trans ?_
    have h1 : (b : ℝ) ^ 2 * (Cs * u * Real.exp (Cs * u)) ≤
        (b : ℝ) ^ 2 * Cs * u * Real.exp (C' * u) := by
      rw [← mul_assoc, ← mul_assoc]
      gcongr
      have : 0 ≤ (b : ℝ) ^ 2 * Cs := by positivity
      simp only [C']; linarith
    have h2 : Kt * u ≤ Kt * u * Real.exp (C' * u) :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
    have h3 : C' * u * Real.exp (C' * u) =
        (b : ℝ) ^ 2 * Cs * u * Real.exp (C' * u) + Kt * u * Real.exp (C' * u) +
          (Cs + 1) * u * Real.exp (C' * u) := by simp only [C']; ring
    have h4 : 0 ≤ (Cs + 1) * u * Real.exp (C' * u) := by positivity
    linarith
  exact le_mul_of_le_mul_exp_of_le (by linarith) zero_le_one hu hcomb hle1

end MPSTensor
