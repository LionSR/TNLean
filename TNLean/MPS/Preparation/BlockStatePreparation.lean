/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinsetEnumeration
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.PairLayer
import TNLean.MPS.Preparation.SequentialFactorization

/-!
# Preparing arbitrary block-isometry states in depth `O(L)`

Cut the ring of `N` sites into `M ≥ 1` blocks of lengths `ℓ 0, …, ℓ (M - 1)`, each at least
`3D` and at most `L`, such that every blocked tensor `B_k = V_k P_k` of a tensor `A` is
injective. For a unit vector `ω` on the pair space, the state `(⊗ₖ V_k) ⊗ₖ |ω⟩_{R_k L_{k+1}}`
(`MPSTensor.blockIsometryState`) is prepared from the all-`|0⟩` product state by a local circuit
of depth at most `C L`, where `C` depends only on `d` and `D`
(`MPSPreparation.exists_isPreparedInDepth_blockIsometryState`).

The circuit is that of arXiv:2307.01696, eqs. (10)–(12) and Fig. 1:

* a layer of unitaries on the pair windows prepares `⊗ₖ |ω⟩_{R_k L_{k+1}} |0⟩_{C_k}`
  (`MPSPreparation.pairLayerOp_mulVec_apply`);
* on every block, in parallel, the unitary `U_k` with `U_k |l, 0, r⟩ = V_k |l, r⟩`, written as a
  staircase of the isometries of the sequential factorization together with SWAP gates, of depth
  `O(ℓ k)` (`MPSPreparation.exists_blockUnitary`).

For blocks of equal length `q` and the pair of the fixed point,
`TNLean.MPS.Preparation.DepthUpperBound` identifies this construction with the uniform
approximating state `|φ'_N⟩` on `N = M q` sites.
The Supplemental Material, proof of Theorem 1, lets the last block be larger; the lengths here
are arbitrary. This is the construction behind eq. (1) of the source; the choice of the block
lengths and the error bound are not made here.

For site-dependent tensors the blocked tensor of block `k` need only be injective on a set
`S_k` of bond pairs that carries the pairs
(`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn`): its
isometric factor is then a partial isometry, and the block unitary implements it on the inputs
`S_k`. This covers the chains of the source paragraph "Inhomogeneous short-range correlated MPS",
with "bond dimension at most `D`" varying along the ring, padded with zeros. The state of the
two layers is computed for any matrices on the blocks
(`MPSPreparation.blockMatVector_pairFamilyVector_eq_mulVec`), which
`TNLean.MPS.Preparation.PartialIsometryPreparation` uses for blocked tensors that are not
injective.

**Scope restriction (injective blocks of length at least `3D`):** the site-dependent depth bounds
`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn` and
`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState` assume that every blocked tensor
is injective, on a set of bond pairs carrying the pairs or on all pairs, and that every block has
length at least `3D`; the source paragraph "Inhomogeneous short-range correlated MPS" states
neither. Documented in `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696, eqs. (1) and (10)–(12), Fig. 1, the paragraphs "The sequential-RG circuit"
  and "Inhomogeneous short-range correlated MPS", and Supplemental Material, proof of Theorem 1.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder
open QuantumCircuit

namespace MPSPreparation

variable {d D M N r₁ : ℕ} {ℓ : Fin M → ℕ}

/-! ### The configurations carrying the pairs -/

/-- The configuration of the ring whose block `k` carries `|l_k, 0 ⋯ 0, r_k⟩`. -/
noncomputable def siteCfg (hd : 0 < d) (hN : ∑ k, ℓ k = N) (dig : Fin D → Cfg d r₁)
    (c : Fin M → Fin D × Fin D) : Cfg d N :=
  (blockCfgEquiv d hN).symm fun k => blockInputCfg hd (ℓ k) dig (c k).1 (c k).2

theorem siteCfg_blockSite (hd : 0 < d) (hN : ∑ k, ℓ k = N) (dig : Fin D → Cfg d r₁)
    (c : Fin M → Fin D × Fin D) (k : Fin M) (j : Fin (ℓ k)) :
    siteCfg hd hN dig c (blockSite hN k j) = blockInputCfg hd (ℓ k) dig (c k).1 (c k).2 j :=
  blockCfgEquiv_symm_blockSite hN _ k j

theorem siteCfg_injective (hd : 0 < d) (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig) :
    Function.Injective (siteCfg hd hN dig) := fun c c' h => funext fun k => by
  have h' : blockInputCfg hd (ℓ k) dig (c k).1 (c k).2 =
      blockInputCfg hd (ℓ k) dig (c' k).1 (c' k).2 := funext fun j => by
    rw [← siteCfg_blockSite, ← siteCfg_blockSite, h]
  obtain ⟨h1, h2⟩ := blockInputCfg_injective hd (hr k) hdig h'
  exact Prod.ext h1 h2

theorem siteCfg_comp_pairSite (hd : 0 < d) (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (dig : Fin D → Cfg d r₁) (c : Fin M → Fin D × Fin D) (k : Fin M) :
    siteCfg hd hN dig c ∘ pairSite hN hr k = twoCfg dig (c k).2 (c (finRotate M k)).1 := by
  funext i
  have hk := hr k
  have hk' := hr (finRotate M k)
  simp only [Function.comp_apply, pairSite, twoCfg]
  split_ifs with h
  · rw [siteCfg_blockSite, blockInputCfg, dite_eq_right (by simp; omega),
      dite_eq_left (by simp)]
    congr 1; ext; simp
  · rw [siteCfg_blockSite, blockInputCfg, dite_eq_left (by simp; omega)]

theorem blockSite_mem_pairSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (j : Fin M)
    (p : Fin (ℓ j)) :
    (∃ k i, pairSite hN hr k i = blockSite hN j p) ↔ p.val < r₁ ∨ ℓ j - r₁ ≤ p.val := by
  constructor
  · rintro ⟨k, i, h⟩
    rcases (pairSite_eq_blockSite_iff hN hr k j i p).mp h with ⟨_, rfl, hp⟩ | ⟨hi, _, hp⟩
    · omega
    · have := i.isLt; omega
  · rintro (hp | hp)
    · refine ⟨(finRotate M).symm j, ⟨r₁ + p.val, by omega⟩, ?_⟩
      rw [pairSite_eq_blockSite_iff]
      exact Or.inr ⟨by simp, (finRotate M).apply_symm_apply j, by simp⟩
    · have := hr j
      refine ⟨j, ⟨p.val - (ℓ j - r₁), by omega⟩, ?_⟩
      rw [pairSite_eq_blockSite_iff]
      exact Or.inl ⟨by simp; omega, rfl, by simp; omega⟩

theorem siteCfg_of_not_mem_pairSite (hd : 0 < d) (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (dig : Fin D → Cfg d r₁) (c : Fin M → Fin D × Fin D)
    {i : Fin N} (hi : ∀ k j, pairSite hN hr k j ≠ i) : siteCfg hd hN dig c i = ⟨0, hd⟩ := by
  obtain ⟨j, p, rfl⟩ := exists_blockSite hN i
  have hp : ¬(p.val < r₁ ∨ ℓ j - r₁ ≤ p.val) := fun h => by
    obtain ⟨k, i', h'⟩ := (blockSite_mem_pairSite hN hr j p).mpr h
    exact hi k i' h'
  rw [siteCfg_blockSite, blockInputCfg, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- A configuration with `|0⟩` off the pair windows and the pair `(r_k, l_{k+1})` on the window
`k` is the configuration whose block `k` carries `|l_k, 0 ⋯ 0, r_k⟩`. -/
theorem eq_siteCfg (hd : 0 < d) (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (dig : Fin D → Cfg d r₁) {y : Cfg d N}
    (h0 : ∀ i, (∀ k j, pairSite hN hr k j ≠ i) → y i = ⟨0, hd⟩)
    (P : Fin M → Fin D × Fin D)
    (hP : ∀ k, y ∘ pairSite hN hr k = twoCfg dig (P k).1 (P k).2) :
    y = siteCfg hd hN dig fun j => ((P ((finRotate M).symm j)).2, (P j).1) := by
  funext i
  obtain ⟨j, p, rfl⟩ := exists_blockSite hN i
  rw [siteCfg_blockSite, blockInputCfg]
  have hj := hr j
  by_cases hp1 : p.val < r₁
  · rw [dite_eq_left hp1]
    have hs : pairSite hN hr ((finRotate M).symm j) ⟨r₁ + p.val, by omega⟩ = blockSite hN j p := by
      rw [pairSite_eq_blockSite_iff]
      exact Or.inr ⟨by simp, (finRotate M).apply_symm_apply j, by simp⟩
    have := congrFun (hP ((finRotate M).symm j)) ⟨r₁ + p.val, by omega⟩
    rw [Function.comp_apply, hs, twoCfg, dite_eq_right (by simp)] at this
    rw [this]; congr 1; ext; simp
  by_cases hp2 : ℓ j - r₁ ≤ p.val
  · rw [dite_eq_right hp1, dite_eq_left hp2]
    have hs : pairSite hN hr j ⟨p.val - (ℓ j - r₁), by omega⟩ = blockSite hN j p := by
      rw [pairSite_eq_blockSite_iff]
      exact Or.inl ⟨by simp; omega, rfl, by simp; omega⟩
    have := congrFun (hP j) ⟨p.val - (ℓ j - r₁), by omega⟩
    rw [Function.comp_apply, hs, twoCfg, dite_eq_left (by simp; omega)] at this
    exact this
  · rw [dite_eq_right hp1, dite_eq_right hp2]
    refine h0 _ fun k i' h => ?_
    exact absurd ((blockSite_mem_pairSite hN hr j p).mp ⟨k, i', h⟩) (by omega)

/-! ### The two layers -/

section Layers

theorem pairwise_commute_blockSite (hN : ∑ k, ℓ k = N)
    (U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ) :
    ((Finset.univ : Finset (Fin M)) : Set (Fin M)).Pairwise
      (Function.onFun Commute fun k => embedOp (blockSite hN k) (U k)) :=
  fun k _ k' _ h => commute_embedOp_of_disjoint (blockSite_injective hN k)
    (blockSite_injective hN k') (disjoint_range_blockSite hN h) (U k) (U k')

theorem pairwise_commute_pairSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) :
    ((Finset.univ : Finset (Fin M)) : Set (Fin M)).Pairwise
      (Function.onFun Commute fun k => embedOp (pairSite hN hr k) (W k)) :=
  fun k _ k' _ h => commute_embedOp_of_disjoint (pairSite_injective hN hr k)
    (pairSite_injective hN hr k') (disjoint_range_pairSite hN hr h) (W k) (W k')

/-- The unitary `U_k` applied on block `k`, for every block: `⊗ₖ U_k`. -/
noncomputable def blockLayerOp (hN : ∑ k, ℓ k = N)
    (U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  Finset.univ.noncommProd (fun k : Fin M => embedOp (blockSite hN k) (U k))
    (pairwise_commute_blockSite hN U)

/-- The unitary `W_k` applied on the pair window `k`, for every window. -/
noncomputable def pairLayerOp (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  Finset.univ.noncommProd (fun k : Fin M => embedOp (pairSite hN hr k) (W k))
    (pairwise_commute_pairSite hN hr W)

theorem blockLayerOp_apply (hN : ∑ k, ℓ k = N) (U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ)
    (x y : Cfg d N) :
    blockLayerOp hN U x y = ∏ k, U k (x ∘ blockSite hN k) (y ∘ blockSite hN k) := by
  rw [blockLayerOp, noncommProd_embedOp_apply _ (fun k => blockSite_injective hN k) _ _
    (fun k _ k' _ h => disjoint_range_blockSite hN h), ite_eq_left]
  intro i hi
  obtain ⟨k, j, rfl⟩ := exists_blockSite hN i
  exact absurd rfl (hi k (Finset.mem_univ k) j)

theorem pairLayerOp_apply (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) (x y : Cfg d N) :
    pairLayerOp hN hr W x y =
      if ∀ i, (∀ k j, pairSite hN hr k j ≠ i) → x i = y i then
        ∏ k, W k (x ∘ pairSite hN hr k) (y ∘ pairSite hN hr k) else 0 := by
  rw [pairLayerOp, noncommProd_embedOp_apply (m := fun _ => r₁ + r₁) _
    (fun k => pairSite_injective hN hr k) _ _
    (fun k _ k' _ h => disjoint_range_pairSite hN hr h)]
  simp only [Finset.mem_univ, true_implies]

/-- The all-`|0⟩` product state is the basis vector of the configuration `0 ⋯ 0`. -/
theorem productVector_single_zero_apply (hd : 0 < d) (z : Cfg d N) :
    productVector (fun _ => Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ)) z =
      if z = fun _ => ⟨0, hd⟩ then 1 else 0 := by
  classical
  simp only [productVector, Pi.single_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_implies, Finset.prod_const_one, funext_iff]

/-- A matrix applied to the all-`|0⟩` product state gives its column at `0 ⋯ 0`. -/
theorem mulVec_productVector_single_zero (hd : 0 < d) (X : Matrix (Cfg d N) (Cfg d N) ℂ)
    (y : Cfg d N) :
    (X *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1) y = X y fun _ => ⟨0, hd⟩ := by
  classical
  simp only [mulVec, dotProduct, productVector_single_zero_apply hd, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The layer of pairs.** Applied to the all-`|0⟩` state, the layer of the unitaries `W_k` has
amplitude `∏ₖ W_k(y|_{window k}, 0)` at a configuration `y` which is `0` off the pair windows,
and `0` at any other configuration.

arXiv:2307.01696, eqs. (10) and (12): `⊗ₖ |ω⟩_{R_k L_{k+1}} |0⟩_{C_k}` is a product over the
pair windows; the paragraph "Inhomogeneous short-range correlated MPS" allows a different pair
`ω^k` on each window. -/
theorem pairLayerOp_mulVec_apply (hd : 0 < d) (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) (y : Cfg d N) :
    (pairLayerOp hN hr W *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1) y =
      if ∀ i, (∀ k j, pairSite hN hr k j ≠ i) → y i = ⟨0, hd⟩ then
        ∏ k, W k (y ∘ pairSite hN hr k) (fun _ => ⟨0, hd⟩) else 0 := by
  classical
  rw [mulVec_productVector_single_zero, pairLayerOp_apply]
  rfl

theorem isCircuitOn_blockLayerOp [NeZero N] (hN : ∑ k, ℓ k = N) {K : ℕ}
    {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ} (hU : ∀ k, IsPairProduct d (ℓ k) K (U k)) :
    IsCircuitOn Set.univ K (blockLayerOp hN U) := by
  refine (IsCircuitOn.finset_noncommProd Finset.univ (fun k => Set.range (blockSite hN k))
    (fun k _ k' _ h => disjoint_range_blockSite hN h) _ (fun k _ =>
      (hU k).isCircuitOn (blockSite_injective hN k) fun i j h => blockSite_succ hN k i j h)
      _).mono_set (Set.subset_univ _)

theorem isCircuitOn_pairLayerOp [NeZero N] (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    {K : ℕ} {W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ k, IsPairProduct d (r₁ + r₁) K (W k)) :
    IsCircuitOn Set.univ K (pairLayerOp hN hr W) := by
  refine (IsCircuitOn.finset_noncommProd Finset.univ
    (fun k => Set.range (pairSite hN hr k))
    (fun k _ k' _ h => disjoint_range_pairSite hN hr h) _ (fun k _ =>
      (hW k).isCircuitOn (pairSite_injective hN hr k) fun i j h => pairSite_succ hN hr k i j h)
      _).mono_set (Set.subset_univ _)

/-- **The state is the output of the two layers**, for any matrices on the blocks. If each `U_k`
implements a matrix `X_k : ℂ^{D²} → ℂ^{d^{ℓ k}}` on the placed inputs `|l, 0 ⋯ 0, r⟩` and `W_k`
prepares the pair `|ω^k⟩` on the window `k`, then `(⊗ₖ X_k) ⊗ₖ |ω^k⟩ = (⊗ₖ U_k) (⊗ₖ W_k) |0 ⋯ 0⟩`.

arXiv:2307.01696, eqs. (10), (11), and (12), and the paragraph "Inhomogeneous short-range
correlated MPS". -/
theorem blockMatVector_pairFamilyVector_eq_mulVec (hd : 0 < d) (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    (X : ∀ k, Matrix (Fin (blockPhysDim d (ℓ k))) (Fin (D * D)) ℂ)
    (ω : Fin M → Fin D × Fin D → ℂ) {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ}
    (hU : ∀ c : Fin M → Fin D × Fin D, pairFamilyState ω c ≠ 0 → ∀ k τ,
      U k τ (blockInputCfg hd (ℓ k) dig (c k).1 (c k).2) =
        X k ((decodeBlockEquiv d (ℓ k)).symm τ) (finProdFinEquiv (c k)))
    {W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ k u, W k u (fun _ => ⟨0, hd⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0 u)
    (s : Cfg d N) :
    blockMatVector X hN (pairFamilyVector ω) s =
      ((blockLayerOp hN U * pairLayerOp hN hr W) *ᵥ
        productVector fun _ => Pi.single ⟨0, hd⟩ 1) s := by
  classical
  have hs : Function.Injective (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) :=
    fun p p' h => Prod.ext (twoCfg_injective hdig h).1 (twoCfg_injective hdig h).2
  set g : Cfg d N → ℂ := fun y => blockLayerOp hN U s y *
    (pairLayerOp hN hr W *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1) y with hg
  rw [← mulVec_mulVec]
  change _ = ∑ y, g y
  -- only the configurations carrying the pairs contribute
  have hzero : ∀ y ∉ Finset.univ.image (siteCfg hd hN dig), g y = 0 := by
    intro y hy
    simp only [hg, pairLayerOp_mulVec_apply]
    split_ifs with h0
    · by_contra hne
      have hall : ∀ k, ∃ p : Fin D × Fin D,
          y ∘ pairSite hN hr k = twoCfg dig p.1 p.2 := by
        intro k
        by_contra hk
        simp only [not_exists] at hk
        apply hne
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) ?_)
        rw [hW, Function.extend_apply' _ _ _ fun h => by
          obtain ⟨p, hp⟩ := h; exact hk p hp.symm, Pi.zero_apply]
      choose P hP using hall
      exact hy (Finset.mem_image.mpr ⟨_, Finset.mem_univ _,
        (eq_siteCfg hd hN hr dig h0 P hP).symm⟩)
    · rw [mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) fun y _ hy => hzero y hy,
    Finset.sum_image fun c _ c' _ h => siteCfg_injective hd hN hr hdig h]
  -- the value at a configuration carrying the pairs
  have hval : ∀ c : Fin M → Fin D × Fin D, g (siteCfg hd hN dig c) =
      (∏ k, X k (blockIndexEquiv d hN s k) (finProdFinEquiv (c k))) * pairFamilyState ω c := by
    intro c
    have hext : ∀ k a b, Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0
        (twoCfg dig a b) = ω k (a, b) := fun k a b => hs.extend_apply _ _ (a, b)
    simp only [hg, pairLayerOp_mulVec_apply,
      ite_eq_left fun i hi => siteCfg_of_not_mem_pairSite hd hN hr dig c hi,
      siteCfg_comp_pairSite hd hN hr dig c, hW, hext, blockLayerOp_apply]
    change _ * pairFamilyState ω c = _
    by_cases hc : pairFamilyState ω c = 0
    · rw [hc, mul_zero, mul_zero]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have : siteCfg hd hN dig c ∘ blockSite hN k = blockInputCfg hd (ℓ k) dig (c k).1 (c k).2 :=
      funext fun j => siteCfg_blockSite hd hN dig c k j
    rw [this, hU c hc, blockIndexEquiv_apply]
  simp_rw [hval, blockMatVector_apply, pairFamilyVector_apply]
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun τ => by
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.apply_symm_apply]
    rfl

/-- **The state is the output of the two layers.** If each `U_k` implements the isometry `V_k`
of the blocked tensor of block `k` on the placed inputs `|l, 0 ⋯ 0, r⟩` and `W_k` prepares the
pair `|ω^k⟩` on the window `k`, then `(⊗ₖ V_k) ⊗ₖ |ω^k⟩ = (⊗ₖ U_k) (⊗ₖ W_k) |0 ⋯ 0⟩`. The
tensors of the chain `A` may depend on the site. This is
`MPSPreparation.blockMatVector_pairFamilyVector_eq_mulVec` for the isometric factors.

arXiv:2307.01696, eqs. (10), (11), and (12), and the paragraph "Inhomogeneous short-range
correlated MPS". -/
theorem chainBlockIsometryState_eq_mulVec (hd : 0 < d) (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ)
    {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ}
    (hU : ∀ c : Fin M → Fin D × Fin D, pairFamilyState ω c ≠ 0 → ∀ k τ,
      U k τ (blockInputCfg hd (ℓ k) dig (c k).1 (c k).2) =
        polarIsoMatrix (chainBlockTensor A hN k) ((decodeBlockEquiv d (ℓ k)).symm τ)
          (finProdFinEquiv (c k)))
    {W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ k u, W k u (fun _ => ⟨0, hd⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0 u)
    (s : Cfg d N) :
    chainBlockIsometryState A ω hN s =
      ((blockLayerOp hN U * pairLayerOp hN hr W) *ᵥ
        productVector fun _ => Pi.single ⟨0, hd⟩ 1) s := by
  rw [chainBlockIsometryState, blockIsoVector_eq_blockMatVector]
  exact blockMatVector_pairFamilyVector_eq_mulVec hd hN hr hdig _ ω hU hW s

/-- **The state is the output of the two layers**, for one tensor and one pair: if each `U_k`
implements the isometry `V_k` of the blocked tensor of block `k` on the placed inputs
`|l, 0 ⋯ 0, r⟩` and `W` prepares the pair `|ω⟩` on a window, then
`(⊗ₖ V_k) ⊗ₖ |ω⟩ = (⊗ₖ U_k) W^{⊗M} |0 ⋯ 0⟩`. This is
`MPSPreparation.chainBlockIsometryState_eq_mulVec` for a constant chain and equal pairs.

arXiv:2307.01696, eqs. (10), (11), and (12). -/
theorem blockIsometryState_eq_mulVec (hd : 0 < d) (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ) {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ}
    (hU : ∀ k l r τ, U k τ (blockInputCfg hd (ℓ k) dig l r) =
      polarIsoMatrix (blockTensor A (ℓ k)) ((decodeBlockEquiv d (ℓ k)).symm τ)
        (finProdFinEquiv (l, r)))
    {W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ u, W u (fun _ => ⟨0, hd⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u)
    (s : Cfg d N) :
    blockIsometryState A ω hN s =
      ((blockLayerOp hN U * pairLayerOp hN hr fun _ => W) *ᵥ
        productVector fun _ => Pi.single ⟨0, hd⟩ 1) s := by
  rw [blockIsometryState_eq_chainBlockIsometryState]
  exact chainBlockIsometryState_eq_mulVec hd hN hr hdig _ _
    (fun c _ k τ => by rw [chainBlockTensor_const]; exact hU k _ _ τ) (fun _ => hW) s

end Layers

/-! ### The depth of the preparation -/

/-- An enumeration of the bond pairs listing the elements of `S` first. -/
theorem exists_pairEquiv_val_lt_card_iff_mem (S : Finset (Fin D × Fin D)) :
    ∃ π : Fin (D * D) ≃ Fin D × Fin D, ∀ x, x.val < S.card ↔ π x ∈ S := by
  obtain ⟨π, hπ⟩ := Finset.exists_equiv_val_lt_card_iff_mem S
  have h : D * D = Fintype.card (Fin D × Fin D) := by simp
  exact ⟨(finCongr h).trans π, fun x => hπ (finCongr h x)⟩

/-- For physical dimension `d ≤ 1` every vector on a ring of `N ≥ 1` sites is prepared in depth
`0`: there is at most one configuration, and a product vector carries any amplitude on it. -/
theorem isPreparedInDepth_zero_of_le_one [NeZero N] (hd : d ≤ 1) (ψ : Cfg d N → ℂ) :
    IsPreparedInDepth 0 ψ := by
  classical
  have h0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hsub : Subsingleton (Fin d) := ⟨fun a b => Fin.ext (by omega)⟩
  refine ⟨1, ⟨[], rfl, rfl⟩, fun i a => if i.val = 0 then ψ (fun _ => a) else 1,
    funext fun s => ?_⟩
  rw [Matrix.one_mulVec, productVector, Finset.prod_eq_single ⟨0, h0⟩
    (fun i _ hi => by rw [ite_eq_right fun h => hi (Fin.ext h)]) (by simp)]
  simp only [ite_true]
  exact congrArg ψ (funext fun _ => Subsingleton.elim _ _)

/-- **Preparation in depth `O(L)` for blocked tensors injective on sets of bond pairs.** There is
`C`, depending only on `d` and `D`, such that the following holds. Cut a ring of `N ≥ 1` sites
into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`, let `A` be a chain of site-dependent tensors of
bond dimension `D` whose blocked tensor of block `k` is injective on a set `S_k` of bond pairs,
and let `ω^k` be unit vectors on the pair space whose product `Ω` vanishes on every bond
configuration `c` with some `c_k ∉ S_k`. Then `(⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is prepared in
depth at most `C L` from a product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1, with the isometric factors
`V_k` partial isometries with `V_k†V_k` the projector onto `S_k`: the unitary on block `k`
implements `V_k` on the inputs in `S_k`, the only ones `Ω` populates. For a chain of bond
dimensions at most `D` padded with zeros, `S_k` is the rectangle of the bonds at the ends of
block `k`. -/
theorem exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (S : Fin M → Finset (Fin D × Fin D))
      (ω : Fin M → Fin D × Fin D → ℂ), (∀ k, ∑ p, star (ω k p) * ω k p = 1) →
      (∀ c, pairFamilyState ω c ≠ 0 → ∀ k, c k ∈ S k) → ∀ L : ℕ,
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (chainBlockTensor A hN k) (S k : Set (Fin D × Fin D))) →
          IsPreparedInDepth (C * L) fun s => chainBlockIsometryState A ω hN s := by
  classical
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · refine ⟨0, fun {M} _ ℓ N _ hN A _ ω _ _ L _ _ _ => ?_⟩
    rw [zero_mul]
    exact isPreparedInDepth_zero_of_le_one (by omega) _
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- no unit pair on the zero space
    refine ⟨0, fun {M} _ ℓ N _ hN A _ ω hω _ L _ _ _ =>
      absurd (hω ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩) ?_⟩
    simp
  have hd : 0 < d := by omega
  have hDd : D ≤ d ^ D := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd2 D)
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d D) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDd)
  have hdig : Function.Injective dig := dig.injective
  choose Cπ hCπ using fun π : Fin (D * D) ≃ Fin D × Fin D =>
    exists_blockUnitary_of_equiv hd (r₁ := D) (by omega) hdig hD π
  obtain ⟨Kw, hKw⟩ := exists_isPairProduct (n := D + D) hd (by omega)
  set Cb := Finset.univ.sup Cπ with hCb
  refine ⟨Cb + Kw, fun {M} _ ℓ N _ hN A S ω hω hωS L hℓ hL hinj => ?_⟩
  choose W hWu hW using fun k => exists_pairUnitary hd hdig (ω k) (hω k)
  have hr : ∀ k, D + D ≤ ℓ k := fun k => by have := hℓ k; omega
  have hUk : ∀ k, ∃ U : Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ,
      IsPairProduct d (ℓ k) (Cb * ℓ k) U ∧ ∀ l r τ, (l, r) ∈ S k →
        U τ (blockInputCfg hd (ℓ k) dig l r) =
          polarIsoMatrix (chainBlockTensor A hN k) ((decodeBlockEquiv d (ℓ k)).symm τ)
            (finProdFinEquiv (l, r)) := fun k => by
    obtain ⟨π, hπ⟩ := exists_pairEquiv_val_lt_card_iff_mem (S k)
    obtain ⟨b, Q, hb0, hbq, -, hrow, -, hiso, hVQ⟩ :=
      exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn (fun j => A (blockSite hN k j))
        (by have := hℓ k; omega) (hinj k) π hπ
    obtain ⟨U, hUpp, hUQ⟩ := hCπ π (ℓ k) (hℓ k) b Q hb0 hrow hiso
    refine ⟨U, hUpp.mono (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ π))),
      fun l r τ hlr => ?_⟩
    have hx : (π.symm (l, r)).val < (S k).card :=
      (hπ (π.symm (l, r))).mpr (by rw [Equiv.apply_symm_apply]; exact hlr)
    have h1 := hUQ (π.symm (l, r)) (by rw [hbq]; exact hx) τ
    have h2 := hVQ τ (π.symm (l, r)) hx
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [h1, ← h2]
    rfl
  choose U hUpp hU using hUk
  have hL1 : 1 ≤ L := by
    have := hℓ ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
    have := hL ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
    omega
  refine ⟨blockLayerOp hN U * pairLayerOp hN hr W, ?_,
    fun _ => Pi.single ⟨0, hd⟩ 1, funext fun s => ?_⟩
  · have hc := (isCircuitOn_pairLayerOp hN hr fun k => hKw (W k) (hWu k)).mul
      (isCircuitOn_blockLayerOp hN fun k => (hUpp k).mono
        (Nat.mul_le_mul_left Cb (hL k)))
    refine (hc.mono ?_).isLocalCircuitOfDepth
    have : Kw ≤ Kw * L := Nat.le_mul_of_pos_right _ hL1
    nlinarith
  · exact chainBlockIsometryState_eq_mulVec hd hN hr hdig A ω
      (fun c hc k τ => hU k _ _ τ (hωS c hc k)) hW s

/-- **Preparation in depth `O(L)` for blocks of lengths at most `L`, site-dependent tensors.**
There is `C`, depending only on `d` and `D`, such that for every cutting of a ring of `N ≥ 1`
sites into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L`, every chain `A` of site-dependent tensors of
bond dimension `D` on the ring for which every blocked tensor is injective, and all unit vectors
`ω^k` on the pair space, the state `(⊗ₖ V_k) ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` is prepared in depth at most
`C L` from a product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1: the pairs are prepared in
constant depth (eq. (12)), and each block unitary of eq. (11) is a sequential circuit of depth
`O(ℓ k)` applied to all blocks in parallel; the paragraph "Inhomogeneous short-range correlated
MPS" applies the same scheme, "preparing `|Ω⟩` and implementing the isometry", to tensors and
pairs that depend on the site. This is
`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn` with every
`S_k` the set of all bond pairs. -/
theorem exists_isPreparedInDepth_chainBlockIsometryState (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ,
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → (∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) →
          IsPreparedInDepth (C * L) fun s => chainBlockIsometryState A ω hN s := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_chainBlockIsometryState_of_isInjectiveOn d D
  exact ⟨C, fun ℓ N _ hN A ω hω L hℓ hL hinj => hC ℓ hN A (fun _ => Finset.univ) ω hω
    (fun _ _ _ => Finset.mem_univ _) L hℓ hL fun k => by
      simpa using isInjectiveOn_univ_iff.mpr (hinj k)⟩

/-- **Preparation in depth `O(L)` for blocks of lengths at most `L`.** There is `C`, depending
only on `d` and `D`, such that for every tensor `A`, every unit vector `ω` on the pair space,
every cutting of a ring of `N ≥ 1` sites into `M ≥ 1` blocks of lengths `3D ≤ ℓ k ≤ L` for
which every blocked tensor is injective, the state `(⊗ₖ V_k) ⊗ₖ |ω⟩` is prepared in depth at
most `C L` from a product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1; this is
`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState` for a constant chain and equal
pairs. -/
theorem exists_isPreparedInDepth_blockIsometryState (d D : ℕ) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (ω : Fin D × Fin D → ℂ), ∑ p, star (ω p) * ω p = 1 →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → (∀ k, Kraus.IsInjective (blockTensor A (ℓ k))) →
          IsPreparedInDepth (C * L) fun s => blockIsometryState A ω hN s := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_chainBlockIsometryState d D
  refine ⟨C, fun A ω hω M _ ℓ N _ hN L hℓ hL hinj => ?_⟩
  rw [blockIsometryState_eq_chainBlockIsometryState]
  exact hC ℓ hN _ _ (fun _ => hω) L hℓ hL fun k => by rw [chainBlockTensor_const]; exact hinj k

/-! ### Blocks of equal length -/

theorem blockSite_const (q : ℕ) (hN : ∑ _ : Fin M, q = M * q) (k : Fin M) (j : Fin q) :
    blockSite (ℓ := fun _ => q) hN k j = finProdFinEquiv (k, j) :=
  Fin.ext (by simp [blockOffset_const q k.isLt.le]; ring)

/-- For blocks of equal length, reading a configuration in blocks is the regrouping
`blockedConfigEquiv` of the uniform blocking. -/
theorem blockedConfigEquiv_symm_eq_blockIndexEquiv (q : ℕ) (hN : ∑ _ : Fin M, q = M * q)
    (s : Cfg d (M * q)) : (blockedConfigEquiv d M q).symm s = blockIndexEquiv d hN s := by
  funext k
  rw [blockIndexEquiv_apply, Equiv.eq_symm_apply]
  funext j
  conv_rhs => rw [← (blockedConfigEquiv d M q).apply_symm_apply s]
  rw [Function.comp_apply, blockSite_const]
  simp [blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry]

end MPSPreparation
