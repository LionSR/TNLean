/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.BlockIsometryState
import TNLean.MPS.Preparation.PairLayer
import TNLean.MPS.Preparation.SequentialFactorization

/-!
# The approximating state is prepared in depth `O(q)`

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

For blocks of equal length `q` and the pair of the fixed point this is the approximating state
`|φ'_N⟩` on `N = M q` sites (`MPSPreparation.exists_isPreparedInDepth_approximatingMPVState`).
The Supplemental Material, proof of Theorem 1, lets the last block be larger; the lengths here
are arbitrary. This is the construction behind eq. (1) of the source; the choice of the block
lengths and the error bound are not made here.

**Scope restriction (common bond dimension):** the site-dependent declarations
`MPSPreparation.chainBlockIsometryState_eq_mulVec` and
`MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState` give every tensor of the chain
and every pair the same square bond dimension `D`, while the source paragraph "Inhomogeneous
short-range correlated MPS" allows bond dimension at most `D`, varying along the ring. The depth
bound `MPSPreparation.exists_isPreparedInDepth_chainBlockIsometryState` assumes moreover that the
blocked tensors are injective and that the blocks have length at least `3D`. Documented in
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder

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

/-- **The state is the output of the two layers.** If each `U_k` implements the isometry `V_k`
of the blocked tensor of block `k` on the placed inputs `|l, 0 ⋯ 0, r⟩` and `W_k` prepares the
pair `|ω^k⟩` on the window `k`, then `(⊗ₖ V_k) ⊗ₖ |ω^k⟩ = (⊗ₖ U_k) (⊗ₖ W_k) |0 ⋯ 0⟩`. The
tensors of the chain `A` may depend on the site.

arXiv:2307.01696, eqs. (10), (11), and (12), and the paragraph "Inhomogeneous short-range
correlated MPS". -/
theorem chainBlockIsometryState_eq_mulVec (hd : 0 < d) (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ)
    {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ}
    (hU : ∀ k l r τ, U k τ (blockInputCfg hd (ℓ k) dig l r) =
      polarIsoMatrix (chainBlockTensor A hN k) ((decodeBlockEquiv d (ℓ k)).symm τ)
        (finProdFinEquiv (l, r)))
    {W : Fin M → Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ k u, W k u (fun _ => ⟨0, hd⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0 u)
    (s : Cfg d N) :
    chainBlockIsometryState A ω hN s =
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
      (∏ k, polarIsoMatrix (chainBlockTensor A hN k) (blockIndexEquiv d hN s k)
        (finProdFinEquiv (c k))) * pairFamilyState ω c := fun c => by
    have hext : ∀ k a b, Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω k) 0
        (twoCfg dig a b) = ω k (a, b) := fun k a b => hs.extend_apply _ _ (a, b)
    simp only [hg, pairLayerOp_mulVec_apply,
      ite_eq_left fun i hi => siteCfg_of_not_mem_pairSite hd hN hr dig c hi,
      siteCfg_comp_pairSite hd hN hr dig c, hW, hext, blockLayerOp_apply]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have : siteCfg hd hN dig c ∘ blockSite hN k = blockInputCfg hd (ℓ k) dig (c k).1 (c k).2 :=
      funext fun j => siteCfg_blockSite hd hN dig c k j
    rw [this, hU, blockIndexEquiv_apply]
  simp_rw [hval, chainBlockIsometryState_apply]
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ => finProdFinEquiv.symm) _ _ fun τ => by
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, Equiv.apply_symm_apply]
    rfl

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
    (fun k => by rw [chainBlockTensor_const]; exact hU k) (fun _ => hW) s

end Layers

/-! ### The depth of the preparation -/

/-- An injective tensor of physical dimension `d^q` has `D² ≤ d^q`. -/
theorem mul_self_le_pow_of_isInjective {q : ℕ} (B : MPSTensor (blockPhysDim d q) D)
    (h : Kraus.IsInjective B) : D * D ≤ d ^ q := by
  have h1 := finrank_range_le_card (R := ℂ) B
  rw [Set.finrank, h, finrank_top, Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_self, mul_one] at h1
  simpa [blockPhysDim_eq_pow] using h1

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
pairs that depend on the site. Injectivity of a blocked tensor forces `D ≤ d^D`
(`MPSPreparation.mul_self_le_pow_of_isInjective`), which lets each bond index be encoded in `D`
sites. -/
theorem exists_isPreparedInDepth_chainBlockIsometryState (d D : ℕ) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (A : MPSChainTensor d D N) (ω : Fin M → Fin D × Fin D → ℂ),
      (∀ k, ∑ p, star (ω k p) * ω k p = 1) → ∀ L : ℕ,
        (∀ k, 3 * D ≤ ℓ k) → (∀ k, ℓ k ≤ L) → (∀ k, Kraus.IsInjective (chainBlockTensor A hN k)) →
          IsPreparedInDepth (C * L) fun s => chainBlockIsometryState A ω hN s := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- no bond: the state vanishes
    refine ⟨0, fun {M} _ ℓ N _ hN A ω _ L _ _ _ =>
      ⟨1, ⟨[], by simp, rfl⟩, fun _ _ => 0, funext fun s => ?_⟩⟩
    have hN' : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    have hM' : IsEmpty (Fin M → Fin (0 * 0)) := by
      rw [isEmpty_fun]; exact ⟨⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩, by simp⟩
    simp [productVector, mulVec, dotProduct, zero_pow (NeZero.ne N)]
  by_cases hDd : D ≤ d ^ D
  swap
  · refine ⟨0, fun {M} _ ℓ N _ hN A _ _ _ hq _ hinj => absurd
      (mul_self_le_pow_of_isInjective _ (hinj ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩)) ?_⟩
    have hq1 : 1 ≤ ℓ ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ := by
      have := hq ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩; omega
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d
      · rw [zero_pow (by omega)]; exact Nat.not_le.mpr (Nat.mul_pos hD hD)
      · rw [one_pow] at hDd ⊢
        nlinarith
    · exact absurd (Nat.lt_pow_self hd).le hDd
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [zero_pow (by omega)] at hDd; omega
    · exact h
  obtain ⟨dig⟩ : Nonempty (Fin D ↪ Cfg d D) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDd)
  have hdig : Function.Injective dig := dig.injective
  obtain ⟨Cb, hCb⟩ := exists_blockUnitary hd (r₁ := D) (by omega) hdig hD
  obtain ⟨Kw, hKw⟩ := exists_isPairProduct (n := D + D) hd (by omega)
  refine ⟨Cb + Kw, fun {M} _ ℓ N _ hN A ω hω L hℓ hL hinj => ?_⟩
  choose W hWu hW using fun k => exists_pairUnitary hd hdig (ω k) (hω k)
  have hr : ∀ k, D + D ≤ ℓ k := fun k => by have := hℓ k; omega
  have hUk : ∀ k, ∃ U : Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ,
      IsPairProduct d (ℓ k) (Cb * ℓ k) U ∧ ∀ l r τ, U τ (blockInputCfg hd (ℓ k) dig l r) =
        polarIsoMatrix (chainBlockTensor A hN k) ((decodeBlockEquiv d (ℓ k)).symm τ)
          (finProdFinEquiv (l, r)) := fun k => by
    obtain ⟨b, Q, hb0, hbq, -, hrow, -, hiso, hVQ⟩ :=
      exists_isometric_chain_polarIsoMatrix (fun j => A (blockSite hN k j))
        (by have := hℓ k; omega) (hinj k)
    obtain ⟨U, hUpp, hUQ⟩ := hCb (ℓ k) (hℓ k) b Q hb0 hbq hrow hiso
    exact ⟨U, hUpp, fun l r τ => by rw [hUQ]; exact (hVQ τ _).symm⟩
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
  · exact chainBlockIsometryState_eq_mulVec hd hN hr hdig A ω hU hW s

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

/-- For blocks of equal length `q` and the pair of the fixed point, the state
`(⊗ₖ V_k) ⊗ₖ |ω⟩` is the approximating state `|φ'_N⟩` of eq. (10) of arXiv:2307.01696. -/
theorem approximatingMPVState_eq_blockIsometryState (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) {σ : Matrix (Fin D) (Fin D) ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (M : ℕ) [NeZero M]
    (hN : ∑ _ : Fin M, q = M * q) :
    approximatingMPVState A σ q M = blockIsometryState A (fixedPointPair σ) hN := by
  rw [(inner_approximatingMPVState_mpvState A hB hσ htr M).1]
  ext s
  rw [approximatingMPVStateRaw_apply, blockIsometryState_apply, mpv_approximatingTensor,
    blockedConfigEquiv_symm_eq_blockIndexEquiv q hN]

/-- **The approximating state is prepared in depth `O(q)`.** There is `C`, depending only on
`d` and `D`, such that for every tensor `A`, every `σ ≥ 0` with `Tr σ = 1`, every block length
`q ≥ 3D` for which the `q`-site blocked tensor is injective and every number of blocks `M ≥ 1`,
the approximating state `|φ'_N⟩` on `N = M q` sites is prepared in depth at most `C q` from a
product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1; this is
`MPSPreparation.exists_isPreparedInDepth_blockIsometryState` for blocks of equal length. -/
theorem exists_isPreparedInDepth_approximatingMPVState (d D : ℕ) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      σ.trace = 1 → ∀ q, 3 * D ≤ q → Kraus.IsInjective (blockTensor A q) →
        ∀ (M : ℕ) [NeZero (M * q)],
          IsPreparedInDepth (C * q) fun s => approximatingMPVState A σ q M s := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_blockIsometryState d D
  refine ⟨C, fun A σ hσ htr q hq hinj M _ => ?_⟩
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hN : ∑ _ : Fin M, q = M * q := by simp
  rw [approximatingMPVState_eq_blockIsometryState A hinj hσ htr M hN]
  exact hC A (fixedPointPair σ) (by rw [fixedPointPair_norm_sq hσ, htr]) (fun _ => q) hN q
    (fun _ => hq) (fun _ => le_rfl) (fun _ => hinj)

end MPSPreparation
