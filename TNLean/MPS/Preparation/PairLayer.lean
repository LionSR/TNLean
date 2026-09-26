/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockUnitary
import TNLean.MPS.Preparation.CircuitComposition
import TNLean.MPS.Preparation.EmbeddedProduct
import TNLean.MPS.Preparation.FixedPointPairs

/-!
# Blocks, pair windows, and the layer of entangled pairs

The ring of `N = M q` sites is cut into `M` blocks of `q` consecutive sites
(`MPSPreparation.blockSite`). In the preparation of arXiv:2307.01696 (eqs. (10)–(12) and
Fig. 1) the right leg `R_k` of block `k` (its last `r₁` sites) and the left leg `L_{k+1}` of
the next block (its first `r₁` sites) carry the entangled pair `|ω⟩`; these `2 r₁` sites form
the pair window `MPSPreparation.pairSite k`, which wraps around the ring for the last block.

This file proves that the product of the pairs, with all other sites in `|0⟩`, is prepared from
the all-`|0⟩` state by one unitary on each window (`MPSPreparation.pairLayer_mulVec`), and that
these windows are placed as consecutive, pairwise disjoint sites of the ring, so the unitaries
form a circuit of constant depth.
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d D M q : ℕ}

/-! ### Blocks -/

/-- The site `j` of the block `k`, that is `k q + j`. -/
def blockSite (M q : ℕ) (k : Fin M) : Fin q → Fin (M * q) := fun j => finProdFinEquiv (k, j)

@[simp] theorem blockSite_val (k : Fin M) (j : Fin q) : (blockSite M q k j).val = j.val + q * k.val :=
  rfl

theorem blockSite_injective (k : Fin M) : Function.Injective (blockSite M q k) := fun j j' h =>
  (Prod.ext_iff.mp (finProdFinEquiv.injective h)).2

theorem blockSite_eq_iff {k k' : Fin M} {j j' : Fin q} :
    blockSite M q k j = blockSite M q k' j' ↔ k = k' ∧ j = j' := by
  rw [blockSite, blockSite, finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem exists_blockSite (i : Fin (M * q)) : ∃ k j, blockSite M q k j = i :=
  ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, by simp [blockSite]⟩

theorem disjoint_range_blockSite {k k' : Fin M} (h : k ≠ k') :
    Disjoint (Set.range (blockSite M q k)) (Set.range (blockSite M q k')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨j', hj'⟩
  exact h (blockSite_eq_iff.mp hj').1.symm

theorem val_add_one_of_lt {N : ℕ} [NeZero N] {a : Fin N} (h : a.val + 1 < N) :
    (a + 1).val = a.val + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem blockSite_succ [NeZero (M * q)] (k : Fin M) (j j' : Fin q) (h : j'.val = j.val + 1) :
    blockSite M q k j' = blockSite M q k j + 1 := by
  have hk := k.isLt
  have hlt : (blockSite M q k j).val + 1 < M * q := by
    simp only [blockSite_val]
    have : q * k.val + q ≤ M * q := by nlinarith
    omega
  ext
  rw [val_add_one_of_lt hlt, blockSite_val, blockSite_val, h]
  ring

/-! ### Pair windows -/

theorem finRotate_val (k : Fin M) :
    (finRotate M k).val = if k.val + 1 = M then 0 else k.val + 1 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by have := k.isLt; omega⟩
  rw [coe_finRotate]
  by_cases h : k = Fin.last M'
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.ext (by simp; omega)))]

/-- The `2 r₁` sites of the pair window between the blocks `k` and `k + 1` (cyclically): the
last `r₁` sites of block `k` followed by the first `r₁` sites of block `k + 1`. -/
def pairSite (M q r₁ : ℕ) (hq : r₁ ≤ q) (k : Fin M) : Fin (r₁ + r₁) → Fin (M * q) := fun i =>
  if h : i.val < r₁ then blockSite M q k ⟨q - r₁ + i.val, by omega⟩
  else blockSite M q (finRotate M k) ⟨i.val - r₁, by omega⟩

variable {r₁ : ℕ}

theorem pairSite_injective (hq : r₁ + r₁ ≤ q) (k : Fin M) :
    Function.Injective (pairSite M q r₁ (by omega) k) := by
  intro i i' h
  simp only [pairSite] at h
  split_ifs at h with h1 h2 h2 <;> rw [blockSite_eq_iff] at h
  · exact Fin.ext (by have := congrArg Fin.val h.2; simp at this; omega)
  · have := congrArg Fin.val h.2; simp at this; omega
  · have := congrArg Fin.val h.2; simp at this; omega
  · exact Fin.ext (by have := congrArg Fin.val h.2; simp at this; omega)

theorem pairSite_eq_blockSite_iff (hq : r₁ + r₁ ≤ q) (k j : Fin M) (i : Fin (r₁ + r₁))
    (p : Fin q) : pairSite M q r₁ (by omega) k i = blockSite M q j p ↔
      (i.val < r₁ ∧ k = j ∧ p.val = q - r₁ + i.val) ∨
        (r₁ ≤ i.val ∧ finRotate M k = j ∧ p.val = i.val - r₁) := by
  simp only [pairSite]
  split_ifs with h
  · rw [blockSite_eq_iff, Fin.ext_iff]; simp only [Fin.val_mk]; omega
  · rw [blockSite_eq_iff, Fin.ext_iff]; simp only [Fin.val_mk]; omega

theorem disjoint_range_pairSite (hq : r₁ + r₁ ≤ q) {k k' : Fin M} (h : k ≠ k') :
    Disjoint (Set.range (pairSite M q r₁ (by omega) k))
      (Set.range (pairSite M q r₁ (by omega) k')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨i', hi'⟩
  obtain ⟨j, p, hjp⟩ := exists_blockSite (M := M) (q := q) (pairSite M q r₁ (by omega) k i)
  have h1 := (pairSite_eq_blockSite_iff hq k j i p).mp hjp
  have h2 := (pairSite_eq_blockSite_iff hq k' j i' p).mp (hi'.trans hjp.symm)
  rcases h1 with ⟨_, rfl, hp⟩ | ⟨_, hk, hp⟩ <;> rcases h2 with ⟨_, hk', hp'⟩ | ⟨_, hk', hp'⟩
  · exact h hk'.symm
  · omega
  · omega
  · exact h ((finRotate M).injective (hk.trans hk'.symm))

theorem pairSite_succ [NeZero (M * q)] (hq : r₁ + r₁ ≤ q) (hr : 1 ≤ r₁) (k : Fin M)
    (i i' : Fin (r₁ + r₁)) (h : i'.val = i.val + 1) :
    pairSite M q r₁ (by omega) k i' = pairSite M q r₁ (by omega) k i + 1 := by
  simp only [pairSite]
  by_cases h1 : i'.val < r₁
  · rw [dite_eq_left h1, dite_eq_left (by omega)]
    exact blockSite_succ k _ _ (by simp; omega)
  by_cases h2 : i.val < r₁
  · rw [dite_eq_right h1, dite_eq_left h2]
    -- crossing from block `k` to block `k + 1`
    have hk := k.isLt
    ext
    have hrot := finRotate_val k
    by_cases hkM : k.val + 1 < M
    · rw [ite_eq_right (by omega)] at hrot
      have hlt : (blockSite M q k ⟨q - r₁ + i.val, by omega⟩).val + 1 < M * q := by
        simp only [blockSite_val]
        have : q * k.val + q + q ≤ M * q := by nlinarith
        omega
      rw [val_add_one_of_lt hlt, blockSite_val, blockSite_val, hrot]
      simp only
      rw [Nat.mul_add]
      omega
    · rw [ite_eq_left (by omega)] at hrot
      rw [blockSite_val, hrot, Fin.val_add, Fin.val_one', blockSite_val]
      simp only
      have hM : M * q = q * k.val + q := by
        have : M = k.val + 1 := by omega
        rw [this]; ring
      rw [Nat.add_mod_mod, hM]
      have : q - r₁ + i.val + q * k.val + 1 = q * k.val + q := by omega
      rw [this, Nat.mod_self]
      omega
  · rw [dite_eq_right h1, dite_eq_right h2]
    exact blockSite_succ _ _ _ (by simp; omega)

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
  let V : Matrix (Cfg d (r₁ + r₁)) Unit ℂ := fun u _ =>
    Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u
  have hV : V.IsIsometry := by
    ext ⟨⟩ ⟨⟩
    rw [mul_apply, one_apply_eq]
    simp only [conjTranspose_apply, V]
    rw [sum_extend_zero hs ω (fun u a => star a * Function.extend
      (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u) (by simp)]
    simp only [hs.extend_apply]
    exact hω
  let emb : Unit ↪ Cfg d (r₁ + r₁) := ⟨fun _ => fun _ => ⟨0, hd⟩, fun _ _ _ => rfl⟩
  obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  exact ⟨W, hW, fun u => hWV u ()⟩

end MPSPreparation
