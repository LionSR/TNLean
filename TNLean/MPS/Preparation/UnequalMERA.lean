/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.IsometryTree
import TNLean.MPS.Preparation.PolarMerge

/-!
# MERA with unequal physical blocks

An `UnequalMERA d D R h N` consists of a nonempty forest of depth-`h` binary trees,
whose positive physical lengths sum to `N`. Every tree has virtual dimension `D²`,
and every leaf acts on at most `R` consecutive physical sites. The vertex isometries
may differ between vertices and between trees. A unitary top disentangler prepares
the pair joining the right root leg of each tree to the left root leg of the next.
All other disentanglers are identities. There are `h + 2` layers: `h` binary layers,
one finest isometry layer, and one top disentangler layer.

The state is the actual contraction of these tensors, via `MPSTensor.blockMatVector`.
It is normalized and equals the block-isometry state when the tree contractions are
the polar isometries of the blocks. Bounded chains also admit a single-leaf,
bond-one representation of every normalized state.

Source: arXiv:2307.01696, eqs. (10) and (16), the paragraph "Connection to MERA",
and the Supplemental Material, proof of Theorem 1, where the last block may be larger.
-/

open Matrix MPSTensor
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- A finite-range MERA on `N` sites, with unequal positive block lengths and binary
isometry trees of common coarse depth `h`. Its `h + 2` layers include the finest
isometries and the unitary top disentangler.

Source: arXiv:2307.01696, eq. (16) and the paragraph "Connection to MERA". -/
structure UnequalMERA (d D R h N : ℕ) where
  bond_pos : 0 < D
  numBlocks : ℕ
  numBlocks_pos : 0 < numBlocks
  blockLength : Fin numBlocks → ℕ
  sum_blockLength : ∑ k, blockLength k = N
  tree : ∀ k, IsometryTree d (D * D) R h (blockLength k)
  disentangler : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ
  disentangler_mem_unitaryGroup : disentangler ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ

namespace UnequalMERA

variable {d D R h N : ℕ} (𝓜 : UnequalMERA d D R h N)

/-- The pair prepared by the top unitary on `R_k L_{k+1}` from `|0⟩|0⟩`. -/
def topPair : Fin D × Fin D → ℂ :=
  fun p => 𝓜.disentangler p (⟨0, 𝓜.bond_pos⟩, ⟨0, 𝓜.bond_pos⟩)

/-- The contraction of tree `k`, with its physical configurations encoded as a single
blocked physical index. -/
noncomputable def treeMatrix (k : Fin 𝓜.numBlocks) :
    Matrix (Fin (blockPhysDim d (𝓜.blockLength k))) (Fin (D * D)) ℂ :=
  Matrix.reindex (decodeBlockEquiv d (𝓜.blockLength k)).symm (Equiv.refl _)
    (𝓜.tree k).matrix

@[simp] theorem treeMatrix_apply (k : Fin 𝓜.numBlocks)
    (s : Fin (blockPhysDim d (𝓜.blockLength k))) (x : Fin (D * D)) :
    𝓜.treeMatrix k s x =
      (𝓜.tree k).matrix (decodeBlockEquiv d (𝓜.blockLength k) s) x := rfl

/-- Every contracted tree is an isometry. -/
theorem isIsometry_treeMatrix (k : Fin 𝓜.numBlocks) : (𝓜.treeMatrix k).IsIsometry :=
  Matrix.IsIsometry.reindex _ (𝓜.tree k).isIsometry_matrix
    (decodeBlockEquiv d (𝓜.blockLength k)).symm (Equiv.refl _)

/-- The state obtained by contracting the forest against the cyclic product of pairs
prepared by the top disentanglers. -/
noncomputable def state : MPVSpace d N :=
  blockMatVector 𝓜.treeMatrix 𝓜.sum_blockLength (pairFamilyVector fun _ => 𝓜.topPair)

@[simp] theorem state_apply (s : Cfg d N) :
    𝓜.state s = ∑ τ : Fin 𝓜.numBlocks → Fin (D * D),
      (∏ k, 𝓜.treeMatrix k (blockIndexEquiv d 𝓜.sum_blockLength s k) (τ k)) *
        pairProductState 𝓜.topPair (fun k => finProdFinEquiv.symm (τ k)) := by
  simp only [state, blockMatVector_apply, pairFamilyVector_apply, pairFamilyState_const]

/-- The pair prepared by the top unitary is a unit vector. -/
theorem sum_star_topPair_mul : ∑ p, star (𝓜.topPair p) * 𝓜.topPair p = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1
    𝓜.disentangler_mem_unitaryGroup) (⟨0, 𝓜.bond_pos⟩, ⟨0, 𝓜.bond_pos⟩))
      (⟨0, 𝓜.bond_pos⟩, ⟨0, 𝓜.bond_pos⟩)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simpa [topPair, Matrix.star_apply] using h

/-- The forest isometries preserve the norm of the normalized pair product. -/
theorem norm_state : ‖𝓜.state‖ = 1 := by
  rw [state, norm_blockMatVector 𝓜.sum_blockLength 𝓜.isIsometry_treeMatrix]
  exact norm_pairFamilyVector fun _ => 𝓜.sum_star_topPair_mul

/-- Polar tree contractions give exactly the unequal-block approximating state of
eq. (10) of arXiv:2307.01696. -/
theorem state_eq_blockIsometryState (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ)
    (hT : ∀ k, (𝓜.tree k).matrix = cfgPolarIso A (𝓜.blockLength k))
    (hω : 𝓜.topPair = ω) :
    𝓜.state = blockIsometryState A ω 𝓜.sum_blockLength := by
  ext s
  simp only [state_apply, blockIsometryState_apply, hω]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp only [treeMatrix_apply, hT, cfgPolarIso, Equiv.symm_apply_apply]

/-- Assemble the forest and its top unitary from the specified isometry trees. -/
def ofTrees (hD : 0 < D) {M : ℕ} (hM : 0 < M) {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) (T : ∀ k, IsometryTree d (D * D) R h (ℓ k))
    (u : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ) : UnequalMERA d D R h N where
  bond_pos := hD
  numBlocks := M
  numBlocks_pos := hM
  blockLength := ℓ
  sum_blockLength := hN
  tree := T
  disentangler := u
  disentangler_mem_unitaryGroup := hu

/-- Every normalized pair can be prepared from `|0⟩|0⟩` by a unitary.

Source: arXiv:2307.01696, paragraph "Connection to MERA". -/
theorem exists_disentangler_pair (hD : 0 < D) (ω : Fin D × Fin D → ℂ)
    (hω : ∑ p, star (ω p) * ω p = 1) :
    ∃ u ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ,
      ∀ p, u p (⟨0, hD⟩, ⟨0, hD⟩) = ω p := by
  let V : Matrix (Fin D × Fin D) Unit ℂ := Matrix.of fun p _ => ω p
  have hV : V.IsIsometry := by
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, V,
      Matrix.of_apply] using hω
  obtain ⟨u, hu, huV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV
    ⟨fun _ => (⟨0, hD⟩, ⟨0, hD⟩), fun a b _ => Subsingleton.elim a b⟩
  exact ⟨u, hu, fun p => huV p ()⟩

/-- Given a forest of isometry trees and any normalized top pair, a unitary
completion gives a MERA whose state is their contraction. -/
theorem exists_of_trees (hD : 0 < D) {M : ℕ} (hM : 0 < M) {ℓ : Fin M → ℕ}
    (hN : ∑ k, ℓ k = N) (T : ∀ k, IsometryTree d (D * D) R h (ℓ k))
    (ω : Fin D × Fin D → ℂ) (hω : ∑ p, star (ω p) * ω p = 1) :
    ∃ 𝓜 : UnequalMERA d D R h N, 𝓜.state =
      blockMatVector (fun k => Matrix.reindex (decodeBlockEquiv d (ℓ k)).symm
        (Equiv.refl _) (T k).matrix) hN (pairFamilyVector fun _ => ω) := by
  obtain ⟨u, hu, huω⟩ := exists_disentangler_pair hD ω hω
  refine ⟨ofTrees hD hM hN T u hu, ?_⟩
  have htop : (ofTrees hD hM hN T u hu).topPair = ω := funext huω
  simp only [state, htop]
  rfl

/-- A forest whose contracted trees are the polar isometries represents the
block-isometry state for every normalized top pair. -/
theorem exists_of_trees_eq_blockIsometryState (hD : 0 < D) (A : MPSTensor d D)
    {M : ℕ} (hM : 0 < M) {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (T : ∀ k, IsometryTree d (D * D) R h (ℓ k))
    (hT : ∀ k, (T k).matrix = cfgPolarIso A (ℓ k))
    (ω : Fin D × Fin D → ℂ) (hω : ∑ p, star (ω p) * ω p = 1) :
    ∃ 𝓜 : UnequalMERA d D R h N, 𝓜.state = blockIsometryState A ω hN := by
  obtain ⟨u, hu, huω⟩ := exists_disentangler_pair hD ω hω
  exact ⟨ofTrees hD hM hN T u hu,
    state_eq_blockIsometryState _ A ω hT (funext huω)⟩

/-- Every normalized state on a positive chain of at most `R` sites is the state
of a bond-one, single-leaf MERA. The leaf range `R` is fixed independently of the state
and the chain length. The two layers are the leaf isometry and the top disentangler. -/
theorem exists_single_leaf (hN : 0 < N) (hR : N ≤ R) (ψ : MPVSpace d N)
    (hψ : ‖ψ‖ = 1) : ∃ 𝓜 : UnequalMERA d 1 R 0 N, 𝓜.state = ψ := by
  letI : Unique (Fin (1 * 1)) := inferInstanceAs (Unique (Fin 1))
  let V : Matrix (Cfg d N) (Fin (1 * 1)) ℂ := Matrix.of fun s _ => ψ s
  have hV : V.IsIsometry := by
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp only [Matrix.conjTranspose_apply, V, Matrix.of_apply]
    rw [sum_star_mul_self_eq_norm_sq, hψ]
    norm_num
  have hsum : ∑ _ : Fin 1, N = N := by simp
  let T : ∀ _ : Fin 1, IsometryTree d (1 * 1) R 0 N :=
    fun _ => IsometryTree.leaf V hV hN hR
  obtain ⟨𝓜, h𝓜⟩ := exists_of_trees (by decide : 0 < 1) (by decide : 0 < 1)
    hsum T (fun _ => 1) (by simp)
  refine ⟨𝓜, h𝓜.trans ?_⟩
  ext s
  rw [blockMatVector_apply]
  simp only [Fintype.sum_unique, Fin.prod_univ_one, pairFamilyVector_apply,
    pairFamilyState, Fin.prod_univ_one, mul_one]
  change ψ (decodeBlockEquiv d N (blockIndexEquiv d hsum s 0)) = ψ s
  rw [blockIndexEquiv_apply, Equiv.apply_symm_apply]
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp [blockSite, blockOffset]

/-- A product-state MERA with bond dimension one exists on every positive chain,
with one physical site per leaf and no coarse layers. -/
theorem nonempty_bond_one (hd : 0 < d) (hN : 0 < N) (hR : 1 ≤ R) :
    Nonempty (UnequalMERA d 1 R 0 N) := by
  classical
  letI : Unique (Fin (1 * 1)) := inferInstanceAs (Unique (Fin 1))
  let z : Fin 1 → Fin d := fun _ => ⟨0, hd⟩
  let V : Matrix (Fin 1 → Fin d) (Fin (1 * 1)) ℂ :=
    Matrix.of fun s _ => if s = z then 1 else 0
  have hV : V.IsIsometry := by
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp [Matrix.conjTranspose_apply, V]
  have hsum : ∑ _ : Fin N, 1 = N := by simp
  let T : ∀ _ : Fin N, IsometryTree d (1 * 1) R 0 1 :=
    fun _ => .leaf V hV (by decide) hR
  obtain ⟨𝓜, _⟩ := exists_of_trees (by decide : 0 < 1) hN hsum T
    (fun _ => 1) (by simp)
  exact ⟨𝓜⟩

end UnequalMERA
end MPSPreparation
