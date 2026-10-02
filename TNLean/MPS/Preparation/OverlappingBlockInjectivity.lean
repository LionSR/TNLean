/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockGram
import TNLean.MPS.Preparation.SupportedPolar

/-!
# The blocked direct sum of overlapping blocks is injective on the bond pairs of the blocks

Let `A_j` be normal blocks in the gauge of arXiv:2307.01696, eq. (5), placed on the bond
coordinates `ι_j` of the direct sum `⊕ⱼ A_j` with unit weights, and let the mixed transfer maps
of distinct blocks have spectral radius below one. The isometry of the source's construction for
a tensor that is not normal ("Long-range MPS using measurements") acts on the bond pairs
`(ι_j a, ι_j c)` of the blocks. This file proves that for every large block length `q` the
`q`-site blocked tensor of the direct sum is injective on these pairs
(`MPSTensor.exists_isInjectiveOn_blockTensor_blockSum`): its matrices vanish on the other pairs
and span every matrix unit on these. So the isometric factor of its polar decomposition is an
isometry on these pairs (`MPSTensor.sum_star_polarIsoMatrix_mul`) even when the `q`-site states
of distinct blocks overlap.

The proof is the one indicated in `docs/paper-gaps/mswc24_measurement_preparation_scope.tex`:
the Gram matrix `Bᴴ B` converges to `G_∞ = ∑ⱼ K_j (σ_jᵀ ⊗ 1) K_jᴴ`
(`MPSTensor.exists_norm_gram_blockTensor_blockSum_sub_le`), which is positive definite on the
bond pairs of the blocks (`MPSTensor.exists_pos_algebraMap_le_blockSumGramLimit_add`); so `B`
has no kernel on these pairs for large `q`, and by duality its matrices span all matrix units on
them (`MPSTensor.isInjectiveOn_of_eq_zero_of_mulVec_eq_zero`).

## Main declarations

* `MPSTensor.blockPairs` — the bond pairs `(ι_j a, ι_j c)` of the blocks.
* `MPSTensor.isInjectiveOn_of_eq_zero_of_mulVec_eq_zero` — injectivity on a set of bond pairs
  from the absence of a kernel on vectors supported there.
* `MPSTensor.exists_isInjectiveOn_blockTensor_blockSum` — injectivity of the blocked direct sum
  on the bond pairs of the blocks for large block lengths.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, eq. (5), Supplemental Material, eqs. (S2)–(S5), and the paragraph
  "Long-range MPS using measurements".
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {Dj : Fin b → ℕ}

/-! ### The bond pairs of the blocks -/

/-- The bond pairs `(ι_j a, ι_j c)` of the direct sum that lie in one block `j`. -/
def blockPairs (ι : (j : Fin b) → Fin (Dj j) → Fin D) : Finset (Fin D × Fin D) :=
  Finset.univ.biUnion fun j =>
    Finset.univ.image fun ac : Fin (Dj j) × Fin (Dj j) => (ι j ac.1, ι j ac.2)

theorem mem_blockPairs {ι : (j : Fin b) → Fin (Dj j) → Fin D} {p : Fin D × Fin D} :
    p ∈ blockPairs ι ↔ ∃ j a c, (ι j a, ι j c) = p := by
  simp only [blockPairs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.exists]

/-! ### Injectivity on a set of bond pairs by duality -/

/-- **Injectivity on a set of bond pairs from the absence of a kernel.** If the matrices of a
tensor vanish outside a set `S` of bond pairs and `B x = 0` has no solution `x ≠ 0` supported on
`S`, then the tensor is injective on `S`: its matrices span every matrix unit `|α⟩⟨β|` with
`(α, β) ∈ S`. This is the converse of `MPSTensor.IsInjectiveOn.eq_zero_of_mulVec_eq_zero`. -/
theorem isInjectiveOn_of_eq_zero_of_mulVec_eq_zero {n : ℕ} {B : MPSTensor n D}
    {S : Set (Fin D × Fin D)} (h0 : ∀ i p, p ∉ S → B i p.1 p.2 = 0)
    (hker : ∀ x : Fin D × Fin D → ℂ, (∀ p, p ∉ S → x p = 0) →
      (physicalMatrix B).mulVec x = 0 → x = 0) :
    IsInjectiveOn B S := by
  classical
  refine ⟨h0, fun p hp => ?_⟩
  by_contra hmem
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
  set x : Fin D × Fin D → ℂ := fun p' => if p' ∈ S then f (Matrix.single p'.1 p'.2 1) else 0
  -- `f` is the functional `Y ↦ ∑ Y_{p'} f(|p'⟩)`.
  have hfY : ∀ Y : Matrix (Fin D) (Fin D) ℂ,
      f Y = ∑ p' : Fin D × Fin D, Y p'.1 p'.2 * f (Matrix.single p'.1 p'.2 1) := fun Y => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hx : x = 0 := hker x (fun p' hp' => ite_eq_right hp') <| funext fun i => by
    have hBi : f (B i) = 0 := by
      have hmem' : f (B i) ∈ (Submodule.span ℂ (Set.range B)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hmap] at hmem'
      exact (Submodule.mem_bot ℂ).1 hmem'
    rw [hfY] at hBi
    rw [Pi.zero_apply, ← hBi]
    simp only [mulVec, dotProduct, physicalMatrix, x]
    refine Finset.sum_congr rfl fun p' _ => ?_
    by_cases hp' : p' ∈ S
    · rw [ite_eq_left hp']
    · rw [ite_eq_right hp', h0 i p' hp', mul_zero, zero_mul]
  apply hf
  have := congrFun hx p
  simpa [x, hp] using this

/-! ### The blocked direct sum -/

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- The matrices of the blocked direct sum vanish outside the bond pairs of the blocks. -/
theorem blockTensor_blockSum_apply_eq_zero (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') (μ : Fin b → ℂ) {q : ℕ} (hq : q ≠ 0)
    (i : Fin (blockPhysDim d q)) {p : Fin D × Fin D} (hp : p ∉ blockPairs ι) :
    blockTensor (blockSum Aj ι μ) q i p.1 p.2 = 0 := by
  change physicalMatrix (blockTensor (blockSum Aj ι μ) q) i p = 0
  rw [physicalMatrix_blockTensor_blockSum hι hdisj μ hq, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.mul_apply]
  refine (smul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_))
  rw [conjTranspose_apply, pairEmbedding_apply, ite_eq_right fun h => hp (mem_blockPairs.2
    ⟨j, r.1, r.2, h.symm⟩), star_zero, mul_zero]

/-- A vector supported on the bond pairs of the blocks is annihilated by the projector `Q` onto
the other pairs. -/
theorem offBlockProj_mulVec_eq_zero (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {x : Fin D × Fin D → ℂ}
    (hx : ∀ p, p ∉ blockPairs ι → x p = 0) : (offBlockProj ι).mulVec x = 0 := by
  classical
  -- `K_j K_jᴴ` keeps the coordinates of block `j`.
  have hK : ∀ j p, ((pairEmbedding (ι j) * (pairEmbedding (ι j))ᴴ).mulVec x) p =
      if ∃ a c, (ι j a, ι j c) = p then x p else 0 := fun j p => by
    simp only [mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, pairEmbedding_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    split_ifs with hp
    · obtain ⟨a, c, rfl⟩ := hp
      rw [Finset.sum_eq_single (a, c)]
      · rw [Finset.sum_eq_single (ι j a, ι j c)] <;> simp (config := { contextual := true })
      · intro r _ hr
        refine Finset.sum_eq_zero fun p' _ => ?_
        rw [ite_eq_right fun h => hr (Prod.ext (hι j (congrArg Prod.fst h)).symm
          (hι j (congrArg Prod.snd h)).symm)]
        simp
      · simp
    · refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun p' _ => ?_
      rw [ite_eq_right fun h => hp ⟨r.1, r.2, h.symm⟩]
      simp
  funext p
  rw [offBlockProj, sub_mulVec, one_mulVec, Matrix.sum_mulVec, Pi.sub_apply, Finset.sum_apply,
    Pi.zero_apply]
  simp only [hK]
  by_cases hp : p ∈ blockPairs ι
  · obtain ⟨j, a, c, rfl⟩ := mem_blockPairs.1 hp
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left ⟨a, c, rfl⟩, sub_self]
    · intro j' _ hj'
      rw [ite_eq_right]
      rintro ⟨a', c', h⟩
      exact hdisj j' j hj' a' a (congrArg Prod.fst h)
    · simp
  · rw [hx p hp, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun j _ => by simp

open scoped Matrix.Norms.L2Operator in
/-- **Injectivity of the blocked direct sum on the bond pairs of the blocks.** Let the blocks
`A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`,
`Tr σ_j = 1` (arXiv:2307.01696, eq. (5)), placed on the bond coordinates `ι_j`, and let
`|λ₂| < 1` bound the moduli of the eigenvalues other than `1` of every `E_{A_j}` and of all
eigenvalues of the mixed transfer maps of distinct blocks. There is `L₀` such that for every
`q ≥ L₀` the `q`-site blocked tensor of the direct sum `⊕ⱼ A_j` is injective on the bond pairs
`(ι_j a, ι_j c)` of the blocks: the `q`-site states of the blocks are jointly linearly
independent although they need not be orthogonal.

The Gram matrix converges to `G_∞` (`exists_norm_gram_blockTensor_blockSum_sub_le`), and
`G_∞ + Q ≥ c > 0` (`exists_pos_algebraMap_le_blockSumGramLimit_add`), so for `‖Bᴴ B - G_∞‖ < c` a
vector `x` supported on the pairs of the blocks with `B x = 0` satisfies
`0 = x†(Bᴴ B + Q)x ≥ (c - ‖Bᴴ B - G_∞‖) x†x`. -/
theorem exists_isInjectiveOn_blockTensor_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖) :
    ∃ L₀ : ℕ, ∀ q, L₀ ≤ q →
      IsInjectiveOn (blockTensor (blockSum Aj ι fun _ => 1) q) (blockPairs ι : Set _) := by
  classical
  -- A rate `0 < t < 1` bounding the eigenvalues, so that the Gram matrices converge.
  set t : ℝ := max ‖lam₂‖ (1 / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by norm_num)
  have ht1 : t < 1 := max_lt hl (by norm_num)
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, hG⟩ := exists_norm_gram_blockTensor_blockSum_sub_le hι hdisj hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (by rwa [hnt]) (fun j μ' h h1 => (hlam j μ' h h1).trans (by
      rw [hnt]; exact le_max_left _ _)) (fun j j' h μ' hμ => (hmix j j' h μ' hμ).trans (by
      rw [hnt]; exact le_max_left _ _)) (γ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hcb⟩ := exists_pos_algebraMap_le_blockSumGramLimit_add hι hdisj hσ htr
  set x₀ := Real.exp (-(1 / 2) / correlationLength (t : ℂ))
  have hx₀ : 0 ≤ x₀ := (Real.exp_pos _).le
  have hx₁ : x₀ < 1 := by
    rw [Real.exp_lt_one_iff, neg_div_correlationLength, hnt]
    exact mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg ht0 ht1)
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (show 0 < c / (K + 1) by positivity) hx₁
  refine ⟨L + 1, fun q hq => ?_⟩
  have hq0 : q ≠ 0 := by omega
  set B := physicalMatrix (blockTensor (blockSum Aj ι fun _ => 1) q)
  set G := blockSumGramLimit ι σ
  set Q := offBlockProj ι
  have hΔ : ‖Bᴴ * B - G‖ < c := by
    have h := hG (fun _ => 1) (fun _ => norm_one.le) q hq0
    simp only [norm_one, one_pow, Complex.ofReal_one, one_smul] at h
    calc ‖Bᴴ * B - G‖ ≤ K * x₀ ^ q := h
      _ ≤ K * x₀ ^ L := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx₀ hx₁.le (by omega)) hK
      _ ≤ K * (c / (K + 1)) := mul_le_mul_of_nonneg_left hL.le hK
      _ < (K + 1) * (c / (K + 1)) := mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = c := by field_simp
  refine isInjectiveOn_of_eq_zero_of_mulVec_eq_zero
    (fun i p hp => blockTensor_blockSum_apply_eq_zero hι hdisj _ hq0 i hp) fun x hx hBx => ?_
  -- `Bᴴ B + Q ≥ c - ‖Bᴴ B - G‖`.
  have hQx : Q.mulVec x = 0 := offBlockProj_mulVec_eq_zero hι hdisj hx
  have hH₀ : IsSelfAdjoint (G + Q) := by
    have h := (Matrix.le_iff.1 hcb).isHermitian
    have h1 : IsSelfAdjoint (algebraMap ℝ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) c) :=
      IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c)
    simpa using h.isSelfAdjoint.add h1
  have hQsa : IsSelfAdjoint Q :=
    (IsSelfAdjoint.one _).sub (isSelfAdjoint_sum _ fun j _ =>
      (Matrix.isHermitian_mul_conjTranspose_self (pairEmbedding (ι j))).isSelfAdjoint)
  have hsa : IsSelfAdjoint (Bᴴ * B - G) := by
    have hG' : IsSelfAdjoint G := by simpa using hH₀.sub hQsa
    exact (Matrix.isHermitian_conjTranspose_mul_self B).isSelfAdjoint.sub hG'
  have hle : algebraMap ℝ (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (c - ‖Bᴴ * B - G‖) ≤
      Bᴴ * B + Q := by
    have h := add_le_add hcb (IsSelfAdjoint.neg_algebraMap_norm_le_self _ hsa)
    rw [map_sub, sub_eq_add_neg]
    convert h using 1
    abel
  have hpsd := (Matrix.le_iff.1 hle).dotProduct_mulVec_nonneg x
  rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, Matrix.add_mulVec, hQx, add_zero,
    ← mulVec_mulVec, hBx, mulVec_zero, zero_sub, smul_mulVec, one_mulVec, dotProduct_neg,
    dotProduct_smul] at hpsd
  set r := c - ‖Bᴴ * B - G‖
  have hr : 0 < r := sub_pos.2 hΔ
  have hs0 : 0 ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
  by_contra hx0
  have hs : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.1 h)
  have hpos : 0 < r • (star x ⬝ᵥ x) := by
    rw [Complex.real_smul]
    exact mul_pos (by exact_mod_cast hr) (lt_of_le_of_ne hs0 (Ne.symm hs))
  exact hpos.not_ge (neg_nonneg.1 hpsd)

end MPSTensor
