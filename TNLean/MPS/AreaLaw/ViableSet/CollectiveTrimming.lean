/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic
import QICLean.Analysis.ViableSubspaceTrimming

/-!
# Collective trimming of a viable subspace on the chain

Let `S` be a subspace of vectors on the first `i` sites of a chain of `L` sites, and `T` a
subspace of vectors on the whole chain. Arad, Landau, Vazirani and Vidick trim `S` collectively,
cut by cut from the left (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition
`def:trimming`, lines 642–656): with an orthonormal basis `u_1, …, u_s` of `S` and
`ψ = ∑_k u_k ⊗ |k⟩`, the projection `P^j` at the cut after `j` sites keeps the left Schmidt
vectors of the partially trimmed `ψ` with Schmidt coefficient at least `ξ`, and `Trim_ξ(S)` is
the span of the trimmed `u_k`. Here `H_A = H_A^1 ⊗ ⋯ ⊗ H_A^i` is the first `i` sites and
`H_B` the last `L - i`, so the cuts `(j : j + 1)`, `1 ≤ j ≤ i - 1`, of the source are the cuts of
the chain after `j` sites.

Lemma `lem:trimming` (lines 660–697) bounds the loss of viability. The general statement is
`Entropy.isCloseTo_prodExt_trimSubspace` of QICLean, for a block of sites with an environment.
This file reads it on the chain: `Span(S) ⊗ H_R` is `leftSupportSubmodule S`, and the Schmidt
rank across the cut of the block after `j` sites, with the last `L - i` sites as environment, is
the rank of the chain cut matrix after `j` sites (`rank_cutEnvVector_blockSplit`).

**Local fix (the constant of Lemma `lem:trimming`):** the source states `δ' ≤ δ + √(ℓ b s) ξ`
for `ℓ = i` factors. The bound proved, `δ + 2 ξ √((i - 1) b)`, is the one its argument gives.
Documented in QICLean's `docs/paper-gaps/alvv16_trimming_constant.tex`
(https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf).

## Main definitions

* `TNLean.MPS.AreaLaw.blockSplit`: the chain in the coordinates of the first `i` sites and the
  rest, a linear isometry.
* `TNLean.MPS.AreaLaw.blockCut`: the first `j + 1` sites, as a region of the first `i` sites.
* `TNLean.MPS.AreaLaw.chainTrimVector`: the trimmed vectors `(P^1 ⊗ 1) ⋯ (P^{i-1} ⊗ 1) u_k`.
* `TNLean.MPS.AreaLaw.chainTrimSubspace`: the trimmed subspace `Trim_ξ(S)`.

## Main results

* `TNLean.MPS.AreaLaw.isCloseTo_leftSupportSubmodule_iff`: viability on the chain is viability
  in block coordinates.
* `TNLean.MPS.AreaLaw.rank_cutEnvVector_blockSplit`: the Schmidt rank across a cut of the block
  is that across the chain cut.
* `TNLean.MPS.AreaLaw.isCloseTo_leftSupportSubmodule_chainTrimSubspace`: Lemma `lem:trimming`
  on the chain, viability.
* `TNLean.MPS.AreaLaw.schmidtRank_cutVector_chainTrimVector_le`: Lemma `lem:trimming` on the
  chain, the Schmidt ranks of the spanning vectors.

## References

* I. Arad, Z. Landau, U. Vazirani, T. Vidick, *Rigorous RG algorithms and area laws for low
  energy eigenstates in 1D*, arXiv:1602.08828v2, `References/1602.08828/local_alg_arxiv_v2.tex`:
  Definition `def:trimming`, lines 642–656; Lemma `lem:trimming` and its proof, lines 660–697.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The chain in the coordinates `(x, y)` of the cut after `i` sites, with `x` the configuration
of the first `i` sites and `y` that of the rest, as a linear isometry. -/
noncomputable def blockSplit (L q i : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) ×
        ((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L i))

@[simp]
theorem blockSplit_apply (i : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i))
    (y : (v : {v : Fin L // v ∉ leftBlock L i}) → Fin q) :
    blockSplit L q i ψ (x, y) = cutMatrix ψ i x y :=
  rfl

/-- `Span(S) ⊗ H_R` is the coordinate extension of `S` in block coordinates. -/
theorem leftSupportSubmodule_eq_comap (i : ℕ) (S : Submodule ℂ (LeftBlockVector L q i)) :
    leftSupportSubmodule (S : Set (LeftBlockVector L q i)) =
      (Submodule.prodExt S (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q))).comap
        (blockSplit L q i).toLinearEquiv.toLinearMap := by
  ext ψ
  rw [mem_leftSupportSubmodule, Submodule.span_eq, Submodule.mem_comap, Submodule.mem_prodExt]
  rfl

/-- **Viability on the chain is viability in block coordinates.** `Span(S) ⊗ H_R` is `δ`-close
to `T` exactly when the coordinate extension of `S` is `δ`-close to the image of `T`. -/
theorem isCloseTo_leftSupportSubmodule_iff {i : ℕ} {δ : ℝ}
    (S : Submodule ℂ (LeftBlockVector L q i)) (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) :
    Submodule.IsCloseTo δ (leftSupportSubmodule (S : Set (LeftBlockVector L q i))) T ↔
      Submodule.IsCloseTo δ (Submodule.prodExt S (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)))
        (T.map (blockSplit L q i).toLinearEquiv.toLinearMap) := by
  rw [← Submodule.isCloseTo_map_iff (blockSplit L q i), leftSupportSubmodule_eq_comap,
    Submodule.map_comap_eq_of_surjective (blockSplit L q i).surjective]

/-- The first `j + 1` sites, as a region of the first `i` sites. -/
def blockCut (L i j : ℕ) : Finset {v : Fin L // v ∈ leftBlock L i} :=
  Finset.univ.filter fun v ↦ v.1.val < j + 1

@[simp]
theorem mem_blockCut {i j : ℕ} {v : {v : Fin L // v ∈ leftBlock L i}} :
    v ∈ blockCut L i j ↔ v.1.val < j + 1 := by
  simp [blockCut]

theorem blockCut_mono (L i : ℕ) : Monotone (blockCut L i) :=
  fun _ _ h _ hv ↦ mem_blockCut.2 (lt_of_lt_of_le (mem_blockCut.1 hv) (Nat.succ_le_succ h))

/-- The first `j + 1` sites, as a subtype of the first `i` sites and as a subtype of the
chain. -/
def blockCutSubtypeEquiv {i j : ℕ} (hj : j + 1 ≤ i) :
    {v : {v : Fin L // v ∈ leftBlock L i} // v ∈ blockCut L i j} ≃
      {v : Fin L // v ∈ leftBlock L (j + 1)} where
  toFun v := ⟨v.1.1, mem_leftBlock.2 (mem_blockCut.1 v.2)⟩
  invFun w := ⟨⟨w.1, mem_leftBlock.2 (lt_of_lt_of_le (mem_leftBlock.1 w.2) hj)⟩,
    mem_blockCut.2 (mem_leftBlock.1 w.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sites right of the first `j + 1`: those of the first `i` sites and those beyond. -/
def blockRestSubtypeEquiv {i j : ℕ} (hj : j + 1 ≤ i) :
    {v : {v : Fin L // v ∈ leftBlock L i} // v ∉ blockCut L i j} ⊕
        {v : Fin L // v ∉ leftBlock L i} ≃
      {v : Fin L // v ∉ leftBlock L (j + 1)} where
  toFun := Sum.elim (fun v ↦ ⟨v.1.1, fun h ↦ v.2 (mem_blockCut.2 (mem_leftBlock.1 h))⟩)
    fun v ↦ ⟨v.1, fun h ↦ v.2 (leftBlock_mono hj h)⟩
  invFun w :=
    if h : w.1 ∈ leftBlock L i then
      Sum.inl ⟨⟨w.1, h⟩, fun h' ↦ w.2 (mem_leftBlock.2 (mem_blockCut.1 h'))⟩
    else Sum.inr ⟨w.1, h⟩
  left_inv v := by
    rcases v with v | v
    · simp [v.1.2]
    · simp [v.2]
  right_inv w := by
    by_cases h : w.1 ∈ leftBlock L i <;> simp [h]

/-- **The Schmidt rank across a cut of the block is that across the chain cut.** For
`j + 1 ≤ i`, the Schmidt rank of `ψ` across the first `j + 1` sites of the block, with the last
`L - i` sites in the environment, is the rank of the chain cut matrix of `ψ` after `j + 1`
sites. -/
theorem rank_cutEnvVector_blockSplit {i j : ℕ} (hj : j + 1 ≤ i)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : {v : Fin L // v ∈ leftBlock L i} ↦ q)
        (blockCut L i j) (blockSplit L q i ψ))) = (cutMatrix ψ (j + 1)).rank := by
  classical
  rw [Matrix.schmidtRank]
  have h : schmidtCoeffMatrix (WithLp.ofLp
      (Entropy.cutEnvVector (n := fun _ : {v : Fin L // v ∈ leftBlock L i} ↦ q)
        (blockCut L i j) (blockSplit L q i ψ))) =
      (cutMatrix ψ (j + 1)).submatrix ((blockCutSubtypeEquiv hj).arrowCongr (Equiv.refl (Fin q)))
        ((Equiv.sumArrowEquivProdArrow _ _ (Fin q)).symm.trans
          ((blockRestSubtypeEquiv hj).arrowCongr (Equiv.refl (Fin q)))) := by
    ext x ⟨y, b⟩
    simp only [schmidtCoeffMatrix_apply, Entropy.cutEnvVector_apply, blockSplit_apply,
      cutMatrix_apply, submatrix_apply]
    refine congrArg (fun c : Fin L → Fin q ↦ ψ c) (funext fun v ↦ ?_)
    by_cases hv : v.val < j + 1
    · have hvi : v ∈ leftBlock L i := mem_leftBlock.2 (lt_of_lt_of_le hv hj)
      rw [Entropy.cutEquiv_symm_apply_mem _ _ (mem_leftBlock.2 hv),
        Entropy.cutEquiv_symm_apply_mem _ _ hvi,
        Entropy.cutEquiv_symm_apply_mem _ _ (mem_blockCut.2 hv)]
      rfl
    · have hv' : v ∉ leftBlock L (j + 1) := fun h ↦ hv (mem_leftBlock.1 h)
      rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hv']
      by_cases hvi : v ∈ leftBlock L i
      · rw [Entropy.cutEquiv_symm_apply_mem _ _ hvi,
          Entropy.cutEquiv_symm_apply_not_mem _ _ (fun h ↦ hv (mem_blockCut.1 h))]
        simp [blockRestSubtypeEquiv, mem_leftBlock.1 hvi, Equiv.sumArrowEquivProdArrow]
      · rw [Entropy.cutEquiv_symm_apply_not_mem _ _ hvi]
        have hvi' : ¬v.val < i := fun h ↦ hvi (mem_leftBlock.2 h)
        simp [blockRestSubtypeEquiv, hvi', Equiv.sumArrowEquivProdArrow]
  rw [h, rank_submatrix]

variable {i s : ℕ}

/-- The trimmed vectors `(P^1 ⊗ 1) ⋯ (P^{i-1} ⊗ 1) u_k` of a family `u` of vectors on the first
`i` sites, trimmed at the `i - 1` cuts of the chain after `1, …, i - 1` sites (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, Definition `def:trimming`, lines 646–655). -/
noncomputable def chainTrimVector (ξ : ℝ) (u : Fin s → LeftBlockVector L q i) (k : Fin s) :
    LeftBlockVector L q i :=
  toEuclideanLin (Entropy.trimProj (n := fun _ : {v : Fin L // v ∈ leftBlock L i} ↦ q)
    (blockCut L i) ξ u (i - 1)) (u k)

/-- The `ξ`-trimmed subspace `Trim_ξ(S)` of the first `i` sites, for an orthonormal basis `u` of
`S` (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `def:trimming`,
eq. `def-viable-trim`, line 654). -/
noncomputable def chainTrimSubspace (ξ : ℝ) (u : Fin s → LeftBlockVector L q i) :
    Submodule ℂ (LeftBlockVector L q i) :=
  Entropy.trimSubspace (n := fun _ : {v : Fin L // v ∈ leftBlock L i} ↦ q) (blockCut L i) ξ u
    (i - 1)

/-- `Trim_ξ(S)` is spanned by the trimmed vectors. -/
theorem chainTrimSubspace_eq_span (ξ : ℝ) (u : Fin s → LeftBlockVector L q i) :
    chainTrimSubspace ξ u = Submodule.span ℂ (Set.range (chainTrimVector ξ u)) :=
  rfl

/-- **Lemma `lem:trimming` on the chain, viability** (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, lines 660–697, with the local fix of the module docstring). Let `S` be
a subspace of vectors on the first `i` sites with orthonormal basis `u`, let `Span(S) ⊗ H_R` be
`δ`-close to `T`, and let every vector of `T` have rank at most `b` across each chain cut after
`1, …, i - 1` sites. Then for `ξ > 0`, `Trim_ξ(S) ⊗ H_R` is `(δ + 2 ξ √((i - 1) b))`-close
to `T`. -/
theorem isCloseTo_leftSupportSubmodule_chainTrimSubspace {b : ℕ} {ξ δ : ℝ} (hξ : 0 < ξ)
    {S : Submodule ℂ (LeftBlockVector L q i)} (u : OrthonormalBasis (Fin s) ℂ S)
    {T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))}
    (hT : Submodule.IsCloseTo δ (leftSupportSubmodule (S : Set (LeftBlockVector L q i))) T)
    (hb : ∀ t ∈ T, ∀ j, 0 < j → j < i → (cutMatrix t j).rank ≤ b) :
    Submodule.IsCloseTo (δ + 2 * (ξ * √(((i - 1 : ℕ) : ℝ) * b)))
      (leftSupportSubmodule
        (chainTrimSubspace ξ (fun k ↦ (u k : LeftBlockVector L q i)) :
          Set (LeftBlockVector L q i))) T := by
  rw [isCloseTo_leftSupportSubmodule_iff] at hT ⊢
  refine Entropy.isCloseTo_prodExt_trimSubspace (blockCut_mono L i) hξ u hT ?_
  rintro _ ⟨t, ht, rfl⟩ j hj
  exact (rank_cutEnvVector_blockSplit (by omega) t).trans_le (hb t ht (j + 1) j.succ_pos (by omega))

/-- **Lemma `lem:trimming` on the chain, Schmidt ranks** (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, lines 662–663 and 690–692). Each trimmed vector of an orthonormal basis
of `S` has Schmidt rank at most `s / ξ²` across the cut of the first `i` sites after `j + 1`
sites, for `j + 1 < i`: `ξ² · rank ≤ s`. -/
theorem schmidtRank_cutVector_chainTrimVector_le {ξ : ℝ} (hξ : 0 < ξ)
    {S : Submodule ℂ (LeftBlockVector L q i)} (u : OrthonormalBasis (Fin s) ℂ S) {j : ℕ}
    (hj : j + 1 < i) (k : Fin s) :
    ξ ^ 2 * Matrix.schmidtRank (WithLp.ofLp (Entropy.cutVector (blockCut L i j)
      (chainTrimVector ξ (fun k ↦ (u k : LeftBlockVector L q i)) k))) ≤ s :=
  Entropy.schmidtRank_cutVector_trimmed_le (blockCut_mono L i) hξ u (by omega) k

end TNLean.MPS.AreaLaw
