/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockSites
import TNLean.MPS.Preparation.BlockUnitary
import TNLean.Circuit.Composition
import TNLean.Circuit.EmbeddedProduct
import TNLean.MPS.Preparation.FixedPointPairState

/-!
# Pair windows and the layer of entangled pairs

The ring of `N` sites is cut into `M` blocks of consecutive sites of lengths `ℓ 0, …, ℓ (M - 1)`
(`MPSPreparation.blockSite`, in `TNLean.MPS.Preparation.BlockSites`). In the preparation of
arXiv:2307.01696 (eqs. (10)–(12) and Fig. 1) the right leg `R_k` of block `k` (its last `r₁`
sites) and the left leg `L_{k+1}` of the next block (its first `r₁` sites) carry the entangled
pair `|ω⟩`; these `2 r₁` sites form the pair window `MPSPreparation.pairSite k`, which wraps
around the ring for the last block.

This file places these windows as consecutive, pairwise disjoint sites of the ring
(`MPSPreparation.pairSite_injective`, `MPSPreparation.disjoint_range_pairSite`,
`MPSPreparation.pairSite_succ`) and gives a unitary on one window that sends `|0⋯0⟩` to the
pair (`MPSPreparation.exists_pairUnitary`). The layer of these unitaries and the identification
of its action on the all-`|0⟩` state with the product of the pairs, with all other sites in
`|0⟩`, are `MPSPreparation.pairLayerOp` and `MPSPreparation.pairLayerOp_mulVec_apply` in
`TNLean.MPS.Preparation.DepthUpperBound`; the unitaries form a circuit of constant depth.
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d D M N : ℕ} {ℓ : Fin M → ℕ} {r₁ : ℕ}

/-! ### Pair windows -/

/-- The `2 r₁` sites of the pair window between the blocks `k` and `k + 1` (cyclically): the
last `r₁` sites of block `k` followed by the first `r₁` sites of block `k + 1`. -/
def pairSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (k : Fin M) :
    Fin (r₁ + r₁) → Fin N := fun i =>
  if h : i.val < r₁ then blockSite hN k ⟨ℓ k - r₁ + i.val, by have := hr k; omega⟩
  else blockSite hN (finRotate M k) ⟨i.val - r₁, by have := hr (finRotate M k); omega⟩

theorem pairSite_eq_blockSite_iff (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (k j : Fin M)
    (i : Fin (r₁ + r₁)) (p : Fin (ℓ j)) : pairSite hN hr k i = blockSite hN j p ↔
      (i.val < r₁ ∧ k = j ∧ p.val = ℓ k - r₁ + i.val) ∨
        (r₁ ≤ i.val ∧ finRotate M k = j ∧ p.val = i.val - r₁) := by
  unfold pairSite
  split_ifs with h
  · rw [blockSite_eq_iff]
    constructor
    · rintro ⟨hkj, hp⟩; exact Or.inl ⟨h, hkj, hp.symm⟩
    · rintro (⟨_, hkj, hp⟩ | ⟨h', _, _⟩)
      · exact ⟨hkj, hp.symm⟩
      · omega
  · rw [blockSite_eq_iff]
    constructor
    · rintro ⟨hkj, hp⟩; exact Or.inr ⟨by omega, hkj, hp.symm⟩
    · rintro (⟨h', _, _⟩ | ⟨_, hkj, hp⟩)
      · omega
      · exact ⟨hkj, hp.symm⟩

theorem pairSite_injective (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (k : Fin M) :
    Function.Injective (pairSite hN hr k) := by
  intro i i' h
  simp only [pairSite] at h
  split_ifs at h with h1 h2 h2 <;> obtain ⟨hk, h⟩ := (blockSite_eq_iff hN).mp h <;>
    dsimp only at h
  · exact Fin.ext (by omega)
  · have := i'.isLt; have := hr k; omega
  · have := i.isLt; have := hr k; omega
  · exact Fin.ext (by omega)

theorem disjoint_range_pairSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {k k' : Fin M}
    (h : k ≠ k') :
    Disjoint (Set.range (pairSite hN hr k)) (Set.range (pairSite hN hr k')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨i', hi'⟩
  obtain ⟨j, p, hjp⟩ := exists_blockSite hN (pairSite hN hr k i)
  have h1 := (pairSite_eq_blockSite_iff hN hr k j i p).mp hjp.symm
  have h2 := (pairSite_eq_blockSite_iff hN hr k' j i' p).mp (hi'.trans hjp.symm)
  rcases h1 with ⟨_, rfl, hp⟩ | ⟨_, hk, hp⟩ <;> rcases h2 with ⟨_, hk', hp'⟩ | ⟨_, hk', hp'⟩
  · exact h hk'.symm
  · have := hr k; omega
  · have := hr j; subst hk'; omega
  · exact h ((finRotate M).injective (hk.trans hk'.symm))

theorem pairSite_succ [NeZero N] (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (k : Fin M)
    (i i' : Fin (r₁ + r₁)) (h : i'.val = i.val + 1) :
    pairSite hN hr k i' = pairSite hN hr k i + 1 := by
  simp only [pairSite]
  have hk := hr k
  by_cases h1 : i'.val < r₁
  · rw [dite_eq_left h1, dite_eq_left (by omega)]
    exact blockSite_succ hN k _ _ (by simp; omega)
  by_cases h2 : i.val < r₁
  · rw [dite_eq_right h1, dite_eq_left h2]
    exact blockSite_finRotate hN k _ (by simp; omega) _ (by simp; omega)
  · rw [dite_eq_right h1, dite_eq_right h2]
    exact blockSite_succ hN _ _ _ (by simp; omega)

/-! ### The entangled pairs from the all-zero state -/

/-- A unitary on the `2 r₁` sites of a pair window sending `|0⋯0⟩` to
`∑_{(r,l)} ω(r, l) |dig r, dig l⟩`, for `ω` of unit norm.

arXiv:2307.01696, after eq. (12): the pair "can thus be prepared from a product state with a
constant-depth circuit". -/
theorem exists_pairUnitary (hd : 0 < d) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    (ω : Fin D × Fin D → ℂ) (hω : ∑ p, star (ω p) * ω p = 1) :
    ∃ W ∈ unitary (Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ), ∀ u,
      W u (fun _ => ⟨0, hd⟩) =
        Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u := by
  classical
  have hs : Function.Injective (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) :=
    fun p p' h => Prod.ext (twoCfg_injective hdig h).1 (twoCfg_injective hdig h).2
  let V : Matrix (Cfg d (r₁ + r₁)) Unit ℂ := Matrix.of fun u _ =>
    Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u
  have hV : V.IsIsometry := by
    ext ⟨⟩ ⟨⟩
    rw [mul_apply, one_apply_eq]
    simp only [conjTranspose_apply, V, of_apply]
    rw [sum_extend_zero hs ω (fun u a => star a * Function.extend
      (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u) (by simp)]
    simp only [hs.extend_apply]
    exact hω
  let emb : Unit ↪ Cfg d (r₁ + r₁) := ⟨fun _ => fun _ => ⟨0, hd⟩, fun _ _ _ => rfl⟩
  obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  exact ⟨W, hW, fun u => (hWV u ()).trans (of_apply _ _ _)⟩

end MPSPreparation
