/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.PairLayer
import TNLean.MPS.Preparation.SequentialFactorization

/-!
# The approximating state is prepared in depth `O(q)`

For a tensor `A` whose `q`-site blocked tensor `B = V P` is injective, the approximating state
`|φ'_N⟩ = |φ_M(V P_∞)⟩` on `N = M q` sites (`MPSTensor.approximatingMPVState`) is prepared from
the all-`|0⟩` product state by a local circuit of depth at most `C q`, where `C` depends only
on `d` and `D` (`MPSPreparation.exists_isPreparedInDepth_approximatingMPVState`).

The circuit is that of arXiv:2307.01696, eqs. (10)–(12) and Fig. 1:

* a layer of unitaries on the pair windows prepares `⊗ₖ |ω⟩_{R_k L_{k+1}} |0⟩_{C_k}`
  (`MPSPreparation.embeddedPairState_blockedConfigEquiv_symm`);
* on every block of `q` sites, in parallel, the unitary `U` with `U |l, 0, r⟩ = V |l, r⟩`,
  written as a staircase of the isometries of the sequential factorization together with SWAP
  gates, of depth `O(q)` (`MPSPreparation.exists_blockUnitary`).

This is the construction behind eq. (1) of the source. It is not eq. (1) itself: the choice
`q = ⌈c log(N/ε)⌉` and the error bound of Lemma 1'(i) are not combined here, and the
approximating state is defined for `N` a multiple of `q`.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder

namespace MPSPreparation

variable {d D M q r₁ : ℕ}

/-! ### Blocks of the chain and blocked configurations -/

theorem blockedConfigEquiv_apply_blockSite (t : Fin M → Fin (blockPhysDim d q)) (k : Fin M)
    (j : Fin q) :
    blockedConfigEquiv d M q t (blockSite M q k j) = decodeBlockEquiv d q (t k) j := by
  simp [blockedConfigEquiv, blockSite, Equiv.arrowCongr, Equiv.curry]

theorem decodeBlockEquiv_blockedConfigEquiv_symm (y : Cfg d (M * q)) (k : Fin M) :
    decodeBlockEquiv d q ((blockedConfigEquiv d M q).symm y k) = y ∘ blockSite M q k := by
  funext j
  conv_rhs => rw [← (blockedConfigEquiv d M q).apply_symm_apply y]
  rw [Function.comp_apply, blockedConfigEquiv_apply_blockSite]

/-! ### The configurations carrying the pairs -/

/-- The placement `(l, r) ↦ |l, 0 ⋯ 0, r⟩` of the two bond indices in a block. -/
noncomputable def blockPlacement (hd : 0 < d) (q : ℕ) (dig : Fin D → Cfg d r₁) :
    Fin D × Fin D → Fin (blockPhysDim d q) :=
  fun p => (decodeBlockEquiv d q).symm (blockInputCfg hd q dig p.1 p.2)

/-- The configuration of the chain whose block `k` carries `|l_k, 0 ⋯ 0, r_k⟩`. -/
noncomputable def siteCfg (hd : 0 < d) (M q : ℕ) (dig : Fin D → Cfg d r₁)
    (c : Fin M → Fin D × Fin D) : Cfg d (M * q) :=
  blockedConfigEquiv d M q fun k => blockPlacement hd q dig (c k)

theorem siteCfg_blockSite (hd : 0 < d) (dig : Fin D → Cfg d r₁) (c : Fin M → Fin D × Fin D)
    (k : Fin M) (j : Fin q) :
    siteCfg hd M q dig c (blockSite M q k j) = blockInputCfg hd q dig (c k).1 (c k).2 j := by
  rw [siteCfg, blockedConfigEquiv_apply_blockSite, blockPlacement, Equiv.apply_symm_apply]

theorem siteCfg_comp_pairSite (hd : 0 < d) (hq : 3 * r₁ ≤ q) (dig : Fin D → Cfg d r₁)
    (c : Fin M → Fin D × Fin D) (k : Fin M) :
    siteCfg hd M q dig c ∘ pairSite M q r₁ (by omega) k =
      twoCfg dig (c k).2 (c (finRotate M k)).1 := by
  funext i
  simp only [Function.comp_apply, pairSite, twoCfg]
  split_ifs with h
  · rw [siteCfg_blockSite, blockInputCfg, dite_eq_right (by simp; omega), dite_eq_left (by simp)]
    congr 1; ext; simp
  · rw [siteCfg_blockSite, blockInputCfg, dite_eq_left (by simp; omega)]

theorem blockSite_mem_pairSite (hq : 3 * r₁ ≤ q) (j : Fin M) (p : Fin q) :
    (∃ k i, pairSite M q r₁ (by omega) k i = blockSite M q j p) ↔
      p.val < r₁ ∨ q - r₁ ≤ p.val := by
  constructor
  · rintro ⟨k, i, h⟩
    rcases (pairSite_eq_blockSite_iff (by omega) k j i p).mp h with ⟨_, _, hp⟩ | ⟨hi, _, hp⟩
    · omega
    · have := i.isLt; omega
  · rintro (hp | hp)
    · refine ⟨(finRotate M).symm j, ⟨r₁ + p.val, by omega⟩, ?_⟩
      rw [pairSite_eq_blockSite_iff (by omega)]
      exact Or.inr ⟨by simp, (finRotate M).apply_symm_apply j, by simp⟩
    · refine ⟨j, ⟨p.val - (q - r₁), by omega⟩, ?_⟩
      rw [pairSite_eq_blockSite_iff (by omega)]
      exact Or.inl ⟨by simp; omega, rfl, by simp; omega⟩

theorem siteCfg_of_not_mem_pairSite (hd : 0 < d) (hq : 3 * r₁ ≤ q) (dig : Fin D → Cfg d r₁)
    (c : Fin M → Fin D × Fin D) {i : Fin (M * q)}
    (hi : ∀ k j, pairSite M q r₁ (by omega) k j ≠ i) : siteCfg hd M q dig c i = ⟨0, hd⟩ := by
  obtain ⟨j, p, rfl⟩ := exists_blockSite (M := M) (q := q) i
  have hp : ¬(p.val < r₁ ∨ q - r₁ ≤ p.val) := fun h => by
    obtain ⟨k, i', h'⟩ := (blockSite_mem_pairSite hq j p).mpr h
    exact hi k i' h'
  rw [siteCfg_blockSite, blockInputCfg, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- A configuration with `|0⟩` off the pair windows and the pair `(r_k, l_{k+1})` on the window
`k` is the configuration whose block `k` carries `|l_k, 0 ⋯ 0, r_k⟩`. -/
theorem eq_siteCfg (hd : 0 < d) (hq : 3 * r₁ ≤ q) (dig : Fin D → Cfg d r₁)
    {y : Cfg d (M * q)} (h0 : ∀ i, (∀ k j, pairSite M q r₁ (by omega) k j ≠ i) → y i = ⟨0, hd⟩)
    (P : Fin M → Fin D × Fin D)
    (hP : ∀ k, y ∘ pairSite M q r₁ (by omega) k = twoCfg dig (P k).1 (P k).2) :
    y = siteCfg hd M q dig fun j => ((P ((finRotate M).symm j)).2, (P j).1) := by
  funext i
  obtain ⟨j, p, rfl⟩ := exists_blockSite (M := M) (q := q) i
  rw [siteCfg_blockSite, blockInputCfg]
  by_cases hp1 : p.val < r₁
  · rw [dite_eq_left hp1]
    have hs : pairSite M q r₁ (by omega) ((finRotate M).symm j) ⟨r₁ + p.val, by omega⟩ =
        blockSite M q j p := by
      rw [pairSite_eq_blockSite_iff (by omega)]
      exact Or.inr ⟨by simp, (finRotate M).apply_symm_apply j, by simp⟩
    have := congrFun (hP ((finRotate M).symm j)) ⟨r₁ + p.val, by omega⟩
    rw [Function.comp_apply, hs, twoCfg, dite_eq_right (by simp)] at this
    rw [this]; congr 1; ext; simp
  by_cases hp2 : q - r₁ ≤ p.val
  · rw [dite_eq_right hp1, dite_eq_left hp2]
    have hs : pairSite M q r₁ (by omega) j ⟨p.val - (q - r₁), by omega⟩ = blockSite M q j p := by
      rw [pairSite_eq_blockSite_iff (by omega)]
      exact Or.inl ⟨by simp; omega, rfl, by simp; omega⟩
    have := congrFun (hP j) ⟨p.val - (q - r₁), by omega⟩
    rw [Function.comp_apply, hs, twoCfg, dite_eq_left (by simp; omega)] at this
    exact this
  · rw [dite_eq_right hp1, dite_eq_right hp2]
    refine h0 _ fun k i' h => ?_
    exact absurd ((blockSite_mem_pairSite hq j p).mp ⟨k, i', h⟩) (by omega)

theorem blockPlacement_injective (hd : 0 < d) (hq : 3 * r₁ ≤ q) {dig : Fin D → Cfg d r₁}
    (hdig : Function.Injective dig) : Function.Injective (blockPlacement hd q dig) := by
  intro p p' h
  have h' := blockInputCfg_injective hd (by omega) hdig ((decodeBlockEquiv d q).symm.injective h)
  exact Prod.ext h'.1 h'.2

/-- **The layer of pairs.** Reading a configuration `y` of the chain in blocks, the product of
the pairs placed by `(l, r) ↦ |l, 0 ⋯ 0, r⟩` has amplitude `∏ₖ ω(y|_{window k})` when `y` is
`0` off the pair windows, and `0` otherwise.

arXiv:2307.01696, eqs. (10) and (12): `⊗ₖ |ω⟩_{R_k L_{k+1}} |0⟩_{C_k}` is a product over the
pair windows. -/
theorem embeddedPairState_blockedConfigEquiv_symm (hd : 0 < d) (hq : 3 * r₁ ≤ q)
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig) (σ : Matrix (Fin D) (Fin D) ℂ)
    (y : Cfg d (M * q)) :
    embeddedPairState (blockPlacement hd q dig) σ ((blockedConfigEquiv d M q).symm y) =
      if ∀ i, (∀ k j, pairSite M q r₁ (by omega) k j ≠ i) → y i = ⟨0, hd⟩ then
        ∏ k, Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2)
          (fixedPointPair σ) 0 (y ∘ pairSite M q r₁ (by omega) k) else 0 := by
  classical
  have hs : Function.Injective (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) :=
    fun p p' h => Prod.ext (twoCfg_injective hdig h).1 (twoCfg_injective hdig h).2
  have hι := blockPlacement_injective hd hq hdig
  by_cases hy : ∃ c, y = siteCfg hd M q dig c
  · obtain ⟨c, rfl⟩ := hy
    rw [ite_eq_left fun i hi => siteCfg_of_not_mem_pairSite hd hq dig c hi]
    have hext : ∀ a b, Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2)
        (fixedPointPair σ) 0 (twoCfg dig a b) = fixedPointPair σ (a, b) :=
      fun a b => hs.extend_apply _ _ (a, b)
    simp_rw [siteCfg_comp_pairSite hd hq dig c, hext]
    rw [siteCfg, Equiv.symm_apply_apply, embeddedPairState, Finset.sum_eq_single c]
    · rw [ite_eq_left rfl]; rfl
    · intro c' _ hc'
      rw [ite_eq_right]
      intro h
      exact hc' (funext fun k => hι (congrFun h k))
    · simp
  · have hL : embeddedPairState (blockPlacement hd q dig) σ
        ((blockedConfigEquiv d M q).symm y) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ite_eq_right fun h => hy ⟨c, ?_⟩
      rw [siteCfg, h, Equiv.apply_symm_apply]
    rw [hL]
    split_ifs with h0
    · symm
      by_contra hne
      have hall : ∀ k, ∃ p : Fin D × Fin D,
          y ∘ pairSite M q r₁ (by omega) k = twoCfg dig p.1 p.2 := by
        intro k
        by_contra hk
        simp only [not_exists] at hk
        apply hne
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        rw [Function.extend_apply' _ _ _ fun h => by
          obtain ⟨p, hp⟩ := h; exact hk p hp.symm, Pi.zero_apply]
      choose P hP using hall
      exact hy ⟨_, eq_siteCfg hd hq dig h0 P hP⟩
    · rfl

/-! ### The two layers -/

section Layers

variable [NeZero (M * q)]

omit [NeZero (M * q)] in
theorem pairwise_commute_blockSite (U : Matrix (Cfg d q) (Cfg d q) ℂ) :
    ((Finset.univ : Finset (Fin M)) : Set (Fin M)).Pairwise
      (Function.onFun Commute fun k => embedOp (blockSite M q k) U) :=
  fun k _ k' _ h => commute_embedOp_of_disjoint (blockSite_injective k) (blockSite_injective k')
    (disjoint_range_blockSite h) U U

omit [NeZero (M * q)] in
theorem pairwise_commute_pairSite (hq : r₁ + r₁ ≤ q)
    (W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) :
    ((Finset.univ : Finset (Fin M)) : Set (Fin M)).Pairwise
      (Function.onFun Commute fun k => embedOp (pairSite M q r₁ (by omega) k) W) :=
  fun k _ k' _ h => commute_embedOp_of_disjoint (pairSite_injective hq k)
    (pairSite_injective hq k') (disjoint_range_pairSite hq h) W W

/-- The unitary `U` applied on every block, `U^{⊗M}`. -/
noncomputable def blockLayerOp (U : Matrix (Cfg d q) (Cfg d q) ℂ) :
    Matrix (Cfg d (M * q)) (Cfg d (M * q)) ℂ :=
  Finset.univ.noncommProd (fun k : Fin M => embedOp (blockSite M q k) U)
    (pairwise_commute_blockSite U)

/-- The unitary `W` applied on every pair window. -/
noncomputable def pairLayerOp (hq : r₁ + r₁ ≤ q)
    (W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ) :
    Matrix (Cfg d (M * q)) (Cfg d (M * q)) ℂ :=
  Finset.univ.noncommProd (fun k : Fin M => embedOp (pairSite M q r₁ (by omega) k) W)
    (pairwise_commute_pairSite hq W)

omit [NeZero (M * q)] in
theorem blockLayerOp_apply (U : Matrix (Cfg d q) (Cfg d q) ℂ) (x y : Cfg d (M * q)) :
    blockLayerOp (M := M) U x y = ∏ k, U (x ∘ blockSite M q k) (y ∘ blockSite M q k) := by
  rw [blockLayerOp, noncommProd_embedOp_apply _ (fun k => blockSite_injective k) _ _
    (fun k _ k' _ h => disjoint_range_blockSite h), ite_eq_left]
  intro i hi
  obtain ⟨k, j, rfl⟩ := exists_blockSite (M := M) (q := q) i
  exact absurd rfl (hi k (Finset.mem_univ k) j)

omit [NeZero (M * q)] in
theorem pairLayerOp_apply (hq : r₁ + r₁ ≤ q) (W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ)
    (x y : Cfg d (M * q)) :
    pairLayerOp (M := M) hq W x y =
      if ∀ i, (∀ k j, pairSite M q r₁ (by omega) k j ≠ i) → x i = y i then
        ∏ k, W (x ∘ pairSite M q r₁ (by omega) k) (y ∘ pairSite M q r₁ (by omega) k) else 0 := by
  rw [pairLayerOp, noncommProd_embedOp_apply _ (fun k => pairSite_injective hq k) _ _
    (fun k _ k' _ h => disjoint_range_pairSite hq h)]
  simp only [Finset.mem_univ, true_implies]

theorem isCircuitOn_blockLayerOp {K : ℕ} {U : Matrix (Cfg d q) (Cfg d q) ℂ}
    (hU : IsPairProduct d q K U) : IsCircuitOn Set.univ K (blockLayerOp (M := M) U) := by
  refine (IsCircuitOn.finset_noncommProd Finset.univ (fun k => Set.range (blockSite M q k))
    (fun k _ k' _ h => disjoint_range_blockSite h) _ (fun k _ =>
      hU.isCircuitOn (blockSite_injective k) fun i j h => blockSite_succ k i j h) _).mono_set
    (Set.subset_univ _)

theorem isCircuitOn_pairLayerOp (hq : r₁ + r₁ ≤ q) (hr : 1 ≤ r₁) {K : ℕ}
    {W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ} (hW : IsPairProduct d (r₁ + r₁) K W) :
    IsCircuitOn Set.univ K (pairLayerOp (M := M) hq W) := by
  refine (IsCircuitOn.finset_noncommProd Finset.univ
    (fun k => Set.range (pairSite M q r₁ (by omega) k))
    (fun k _ k' _ h => disjoint_range_pairSite hq h) _ (fun k _ =>
      hW.isCircuitOn (pairSite_injective hq k) fun i j h => pairSite_succ hq hr k i j h) _).mono_set
    (Set.subset_univ _)

omit [NeZero (M * q)] in
/-- **The approximating state is the output of the two layers.** If `U` implements the isometry
`V` of the `q`-site blocked tensor on the placed inputs `|l, 0 ⋯ 0, r⟩` and `W` prepares the
pair `|ω⟩` on a window, then the periodic state of `B' = V P_∞` on `M` blocks is
`U^{⊗M} W^{⊗M} |0 ⋯ 0⟩`.

arXiv:2307.01696, eqs. (10), (11), and (12). -/
theorem approximatingMPVStateRaw_eq_mulVec (hd : 0 < d) (hq : 3 * r₁ ≤ q)
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig) (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) [NeZero M] {U : Matrix (Cfg d q) (Cfg d q) ℂ}
    (hU : ∀ l r τ, U τ (blockInputCfg hd q dig l r) =
      polarIsoMatrix (blockTensor A q) ((decodeBlockEquiv d q).symm τ) (finProdFinEquiv (l, r)))
    {W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ u, W u (fun _ => ⟨0, hd⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (fixedPointPair σ) 0 u)
    (s : Cfg d (M * q)) :
    approximatingMPVStateRaw A σ q M s =
      ((blockLayerOp (M := M) U * pairLayerOp (by omega) W) *ᵥ
        productVector fun _ => Pi.single ⟨0, hd⟩ 1) s := by
  classical
  set U' : Matrix (Fin (blockPhysDim d q)) (Fin (blockPhysDim d q)) ℂ :=
    fun a b => U (decodeBlockEquiv d q a) (decodeBlockEquiv d q b) with hU'
  have hU'p : ∀ i p, U' i (blockPlacement hd q dig p) =
      polarIsoMatrix (blockTensor A q) i (finProdFinEquiv p) := fun i p => by
    simp only [hU', blockPlacement, Equiv.apply_symm_apply, hU, Equiv.symm_apply_apply]
  rw [approximatingMPVStateRaw_apply, mpv_approximatingTensor_eq_sum_embeddedPairState _ σ
    (blockPlacement hd q dig) U' hU'p, ← (blockedConfigEquiv d M q).symm.sum_comp,
    ← mulVec_mulVec]
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  · rw [blockLayerOp_apply]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hU', decodeBlockEquiv_blockedConfigEquiv_symm]
  · have hψ : ∀ z : Cfg d (M * q),
        productVector (fun _ => Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ)) z =
          if z = fun _ => ⟨0, hd⟩ then 1 else 0 := fun z => by
      simp only [productVector, Pi.single_apply]
      rw [Finset.prod_ite_zero]
      simp only [Finset.mem_univ, true_implies, Finset.prod_const_one, funext_iff]
    simp only [hψ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [embeddedPairState_blockedConfigEquiv_symm hd hq hdig σ y, pairLayerOp_apply]
    simp only [Function.comp_def, hW]

end Layers

/-! ### The depth of the preparation -/

theorem mul_self_le_pow_of_isInjective (A : MPSTensor d D) {q : ℕ}
    (h : Kraus.IsInjective (blockTensor A q)) : D * D ≤ d ^ q := by
  have h1 := finrank_range_le_card (R := ℂ) (blockTensor A q)
  rw [Set.finrank, h, finrank_top, Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_self, mul_one] at h1
  simpa [blockPhysDim_eq_pow] using h1

/-- **The approximating state is prepared in depth `O(q)`.** There is `C`, depending only on
`d` and `D`, such that for every tensor `A`, every `σ ≥ 0` with `Tr σ = 1`, every block length
`q ≥ 3D` for which the `q`-site blocked tensor is injective and every number of blocks `M ≥ 1`,
the approximating state `|φ'_N⟩` on `N = M q` sites is prepared in depth at most `C q` from a
product state.

arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1: the pairs are prepared in
constant depth (eq. (12)), and each block unitary of eq. (11) is a sequential circuit of depth
`O(q)` applied to all blocks in parallel. Each bond index is encoded in `D` sites, which gives
`D ≤ d^D` whenever the blocked tensor is injective. -/
theorem exists_isPreparedInDepth_approximatingMPVState (d D : ℕ) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef →
      σ.trace = 1 → ∀ q, 3 * D ≤ q → Kraus.IsInjective (blockTensor A q) →
        ∀ (M : ℕ) [NeZero (M * q)],
          IsPreparedInDepth (C * q) fun s => approximatingMPVState A σ q M s := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- no bond: the state vanishes
    refine ⟨0, fun A σ _ _ q _ _ M _ => ⟨1, ⟨[], by simp, rfl⟩, fun _ _ => 0, funext fun s => ?_⟩⟩
    have hN : Nonempty (Fin (M * q)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    have h0 : (0 : ℂ) ^ (M * q) = 0 := zero_pow (NeZero.ne _)
    simp [approximatingMPVState, productVector, mulVec, dotProduct, Matrix.trace, h0]
  by_cases hDd : D ≤ d ^ D
  swap
  · refine ⟨0, fun A _ _ _ q hq hinj M _ => absurd (mul_self_le_pow_of_isInjective A hinj) ?_⟩
    have hq1 : 1 ≤ q := by omega
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
  refine ⟨Cb + Kw, fun A σ hσ htr q hq hinj M _ => ?_⟩
  obtain ⟨W, hWu, hW⟩ := exists_pairUnitary hd hdig (fixedPointPair σ)
    (by rw [fixedPointPair_norm_sq hσ, htr])
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hq0 : 0 < q := by omega
  obtain ⟨b, Q, hb0, hbq, -, hrow, -, hiso, hVQ⟩ :=
    exists_isometric_chain_polarIsoMatrix A hq0 hinj
  obtain ⟨U, hUpp, hUQ⟩ := hCb q hq b Q hb0 hbq hrow hiso
  have hU : ∀ l r τ, U τ (blockInputCfg hd q dig l r) =
      polarIsoMatrix (blockTensor A q) ((decodeBlockEquiv d q).symm τ)
        (finProdFinEquiv (l, r)) := fun l r τ => by
    rw [hUQ, hVQ]
  have hraw := (inner_approximatingMPVState_mpvState A hinj hσ htr M).1
  refine ⟨blockLayerOp (M := M) U * pairLayerOp (r₁ := D) (by omega) W, ?_,
    fun _ => Pi.single ⟨0, hd⟩ 1, funext fun s => ?_⟩
  · have hc := (isCircuitOn_pairLayerOp (M := M) (q := q) (by omega) (by omega)
      (hKw W hWu)).mul (isCircuitOn_blockLayerOp (M := M) hUpp)
    refine (hc.mono ?_).isLocalCircuitOfDepth
    have : Kw ≤ Kw * q := Nat.le_mul_of_pos_right _ hq0
    nlinarith
  · rw [hraw]
    exact approximatingMPVStateRaw_eq_mulVec hd (by omega) hdig A σ hU hW s

end MPSPreparation
