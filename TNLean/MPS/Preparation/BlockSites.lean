/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import TNLean.MPS.Overlap.Basic

/-!
# Blocks of prescribed lengths on a ring

A ring of `N` sites is cut into `M` consecutive blocks of lengths `ℓ 0, …, ℓ (M - 1)` with
`∑ₖ ℓ k = N`. Block `k` occupies the sites `o_k, …, o_k + ℓ k - 1`, where
`o_k = ∑_{i < k} ℓ i` (`MPSPreparation.blockOffset`). The site `j` of block `k` is
`MPSPreparation.blockSite hN k j`.

The preparation of arXiv:2307.01696 blocks the chain in this way. Eq. (10) takes `N/q` blocks of
`q` sites; the Supplemental Material, proof of Theorem 1, takes blocks "all of the same size,
`q_N`, except for the last one, which may be larger". Both are instances of the present
description.

## Main declarations

* `MPSPreparation.blockOffset`, `MPSPreparation.blockSite` — the first site of a block and the
  sites of a block.
* `MPSPreparation.blockSite_eq_iff`, `MPSPreparation.exists_blockSite` — every site lies in
  exactly one block.
* `MPSPreparation.blockSite_succ`, `MPSPreparation.blockSite_finRotate` — consecutive sites of
  the ring, inside a block and across the boundary between a block and the next one (cyclically).
* `MPSPreparation.blockCfgEquiv` — a configuration of the ring is the family of its restrictions
  to the blocks.
* `MPSPreparation.prod_ofFn_blockSite` — an ordered product along the ring is the ordered
  product of the ordered products along the blocks.
-/

open scoped BigOperators

namespace MPSPreparation

open MPSTensor

variable {M N : ℕ}

/-! ### Offsets -/

/-- The number of sites in the blocks before position `n`: `∑_{k < n} ℓ k`. -/
def blockOffset (ℓ : Fin M → ℕ) (n : ℕ) : ℕ :=
  ∑ k : Fin M, if k.val < n then ℓ k else 0

@[simp] theorem blockOffset_zero (ℓ : Fin M → ℕ) : blockOffset ℓ 0 = 0 := by
  simp [blockOffset]

theorem blockOffset_succ (ℓ : Fin M → ℕ) (k : Fin M) :
    blockOffset ℓ (k.val + 1) = blockOffset ℓ k.val + ℓ k := by
  have h : ∀ i : Fin M, (if i.val < k.val + 1 then ℓ i else 0) =
      (if i.val < k.val then ℓ i else 0) + (if i = k then ℓ i else 0) := fun i => by
    by_cases h1 : i.val < k.val
    · rw [ite_eq_left (by omega), ite_eq_left h1,
        ite_eq_right (fun h => by rw [h] at h1; omega), add_zero]
    · by_cases h2 : i = k
      · subst h2; simp
      · rw [ite_eq_right (by have := Fin.val_ne_of_ne h2; omega), ite_eq_right h1, ite_eq_right h2]
  simp only [blockOffset, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem blockOffset_mono (ℓ : Fin M → ℕ) {n n' : ℕ} (h : n ≤ n') :
    blockOffset ℓ n ≤ blockOffset ℓ n' :=
  Finset.sum_le_sum fun i _ => by
    split_ifs with h1 h2 <;> omega

theorem blockOffset_of_le (ℓ : Fin M → ℕ) {n : ℕ} (h : M ≤ n) :
    blockOffset ℓ n = ∑ k, ℓ k :=
  Finset.sum_congr rfl fun k _ => ite_eq_left (by have := k.isLt; omega)

theorem blockOffset_castSucc (ℓ : Fin (M + 1) → ℕ) {n : ℕ} (h : n ≤ M) :
    blockOffset (fun k : Fin M => ℓ k.castSucc) n = blockOffset ℓ n := by
  rw [blockOffset, blockOffset, Fin.sum_univ_castSucc, ite_eq_right (by simp; omega), add_zero]
  rfl

/-- For blocks of equal length `q`, the block `k` starts at `k q`. -/
theorem blockOffset_const (q : ℕ) {n : ℕ} (h : n ≤ M) :
    blockOffset (fun _ : Fin M => q) n = n * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 = (⟨n, by omega⟩ : Fin M).val + 1 from rfl, blockOffset_succ,
      ih (by omega)]
    ring

/-! ### Sites of a block -/

variable {ℓ : Fin M → ℕ}

theorem blockOffset_add_lt (hN : ∑ k, ℓ k = N) (k : Fin M) (j : Fin (ℓ k)) :
    blockOffset ℓ k.val + j.val < N := by
  have h1 := blockOffset_succ ℓ k
  have h2 := blockOffset_mono ℓ (show k.val + 1 ≤ M from k.isLt)
  rw [blockOffset_of_le ℓ le_rfl, hN] at h2
  have := j.isLt
  omega

/-- The site `j` of the block `k`, that is `∑_{i < k} ℓ i + j`. -/
def blockSite (hN : ∑ k, ℓ k = N) (k : Fin M) (j : Fin (ℓ k)) : Fin N :=
  ⟨blockOffset ℓ k.val + j.val, blockOffset_add_lt hN k j⟩

@[simp] theorem blockSite_val (hN : ∑ k, ℓ k = N) (k : Fin M) (j : Fin (ℓ k)) :
    (blockSite hN k j).val = blockOffset ℓ k.val + j.val :=
  rfl

/-- A one-block partition enumerates the sites in their original order. -/
theorem blockSite_singleton (hN : ∑ _ : Fin 1, N = N) (i : Fin N) :
    blockSite hN 0 i = i := by
  apply Fin.ext
  simp [blockSite, blockOffset]

theorem blockSite_injective (hN : ∑ k, ℓ k = N) (k : Fin M) :
    Function.Injective (blockSite hN k) := fun j j' h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem blockSite_eq_iff (hN : ∑ k, ℓ k = N) {k k' : Fin M} {j : Fin (ℓ k)} {j' : Fin (ℓ k')} :
    blockSite hN k j = blockSite hN k' j' ↔ k = k' ∧ j.val = j'.val := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [blockSite_val] at h'
    have hk : k = k' := by
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · have := blockOffset_succ ℓ k
        have := blockOffset_mono ℓ (show k.val + 1 ≤ k'.val from hlt)
        have := j.isLt
        omega
      · have := blockOffset_succ ℓ k'
        have := blockOffset_mono ℓ (show k'.val + 1 ≤ k.val from hlt)
        have := j'.isLt
        omega
    subst hk
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, h⟩
    exact Fin.ext (by simp [h])

theorem exists_blockSite (hN : ∑ k, ℓ k = N) (i : Fin N) : ∃ k j, blockSite hN k j = i := by
  classical
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · rw [Fin.sum_univ_zero] at hN; subst hN; exact i.elim0
    · exact h
  have hex : ∃ n, i.val < blockOffset ℓ (n + 1) :=
    ⟨M, by rw [blockOffset_of_le ℓ (by omega), hN]; exact i.isLt⟩
  set n := Nat.find hex with hndef
  have hn : i.val < blockOffset ℓ (n + 1) := Nat.find_spec hex
  have hnM : n < M := by
    by_contra h
    have := Nat.find_min hex (show M - 1 < n by omega)
    rw [show M - 1 + 1 = M by omega, blockOffset_of_le ℓ le_rfl, hN] at this
    exact this i.isLt
  have hlo : blockOffset ℓ n ≤ i.val := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, blockOffset_zero]; exact Nat.zero_le _
    · have := Nat.find_min hex (show n - 1 < n by omega)
      rw [show n - 1 + 1 = n by omega] at this
      omega
  have hsucc := blockOffset_succ ℓ ⟨n, hnM⟩
  refine ⟨⟨n, hnM⟩, ⟨i.val - blockOffset ℓ n, by simp only at hsucc; omega⟩, Fin.ext ?_⟩
  simp only [blockSite_val]
  omega

theorem disjoint_range_blockSite (hN : ∑ k, ℓ k = N) {k k' : Fin M} (h : k ≠ k') :
    Disjoint (Set.range (blockSite hN k)) (Set.range (blockSite hN k')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨j', hj'⟩
  exact h ((blockSite_eq_iff hN).mp hj').1.symm

/-- Consecutive sites of a block are consecutive sites of the ring. -/
theorem blockSite_succ [NeZero N] (hN : ∑ k, ℓ k = N) (k : Fin M) (j j' : Fin (ℓ k))
    (h : j'.val = j.val + 1) : blockSite hN k j' = blockSite hN k j + 1 := by
  have hlt : (blockSite hN k j).val + 1 < N := by
    have := blockOffset_add_lt hN k j'
    simp only [blockSite_val]; omega
  ext
  rw [Fin.val_add_one_of_lt' hlt, blockSite_val, blockSite_val, h]
  ring

theorem finRotate_val (k : Fin M) :
    (finRotate M k).val = if k.val + 1 = M then 0 else k.val + 1 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by have := k.isLt; omega⟩
  rw [coe_finRotate]
  by_cases h : k = Fin.last M'
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.ext (by simp; omega)))]

/-- The site after the last site of block `k` starts block `k + 1`, cyclically:
`o_k + ℓ_k ≡ o_{k+1} (mod N)`. -/
theorem blockOffset_add_mod (hN : ∑ k, ℓ k = N) (k : Fin M) :
    (blockOffset ℓ k.val + ℓ k) % N = blockOffset ℓ (finRotate M k).val % N := by
  rw [← blockOffset_succ, finRotate_val]
  split_ifs with hkM
  · rw [hkM, blockOffset_of_le ℓ le_rfl, hN, Nat.mod_self, blockOffset_zero, Nat.zero_mod]
  · rfl

/-- The site after the last site of a block is the first site of the next block, cyclically. -/
theorem blockSite_finRotate [NeZero N] (hN : ∑ k, ℓ k = N) (k : Fin M) (j : Fin (ℓ k))
    (hj : j.val + 1 = ℓ k) (j' : Fin (ℓ (finRotate M k))) (hj' : j'.val = 0) :
    blockSite hN (finRotate M k) j' = blockSite hN k j + 1 := by
  have hsucc := blockOffset_succ ℓ k
  have hrot := finRotate_val k
  ext
  by_cases hkM : k.val + 1 = M
  · rw [ite_eq_left hkM] at hrot
    rw [blockSite_val, hrot, hj', blockOffset_zero, Fin.val_add, Fin.val_one', blockSite_val,
      Nat.add_mod_mod]
    have : blockOffset ℓ k.val + j.val + 1 = N := by
      rw [← hN, ← blockOffset_of_le ℓ (le_of_eq hkM.symm) ]
      omega
    rw [this, Nat.mod_self]
  · rw [ite_eq_right hkM] at hrot
    have hlt : (blockSite hN k j).val + 1 < N := by
      have := blockOffset_add_lt hN (finRotate M k) j'
      rw [hrot] at this
      simp only [blockSite_val]
      rw [show k.val + 1 = k.val + 1 from rfl] at this
      have e : blockOffset ℓ (↑(finRotate M k)) = blockOffset ℓ (k.val + 1) := by rw [hrot]
      omega
    rw [Fin.val_add_one_of_lt' hlt, blockSite_val, blockSite_val, hj', hrot, hsucc]
    omega

/-! ### Configurations read in blocks -/

/-- The sites of the ring are the pairs (block, site of the block). -/
noncomputable def blockSigmaEquiv (hN : ∑ k, ℓ k = N) : (Σ k, Fin (ℓ k)) ≃ Fin N :=
  Equiv.ofBijective (fun p => blockSite hN p.1 p.2)
    ⟨fun ⟨k, j⟩ ⟨k', j'⟩ h => by
      obtain ⟨rfl, hj⟩ := (blockSite_eq_iff hN).mp h
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hj)),
    fun i => by
      obtain ⟨k, j, h⟩ := exists_blockSite hN i
      exact ⟨⟨k, j⟩, h⟩⟩

@[simp] theorem blockSigmaEquiv_apply (hN : ∑ k, ℓ k = N) (p : Σ k, Fin (ℓ k)) :
    blockSigmaEquiv hN p = blockSite hN p.1 p.2 :=
  rfl

/-- A configuration of the ring is the family of its restrictions to the blocks. -/
noncomputable def blockCfgEquiv (d : ℕ) (hN : ∑ k, ℓ k = N) :
    Cfg d N ≃ ∀ k, Cfg d (ℓ k) :=
  (Equiv.arrowCongr (blockSigmaEquiv hN).symm (Equiv.refl (Fin d))).trans
    (Equiv.piCurry fun _ _ => Fin d)

@[simp] theorem blockCfgEquiv_apply {d : ℕ} (hN : ∑ k, ℓ k = N) (s : Cfg d N) (k : Fin M) :
    blockCfgEquiv d hN s k = s ∘ blockSite hN k := by
  funext j
  simp [blockCfgEquiv, Equiv.arrowCongr, Sigma.curry]

@[simp] theorem blockCfgEquiv_symm_blockSite {d : ℕ} (hN : ∑ k, ℓ k = N)
    (t : ∀ k, Cfg d (ℓ k)) (k : Fin M) (j : Fin (ℓ k)) :
    (blockCfgEquiv d hN).symm t (blockSite hN k j) = t k j := by
  have := congrFun (blockCfgEquiv_apply hN ((blockCfgEquiv d hN).symm t) k) j
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-! ### Ordered products along the blocks -/

/-- **Products along the ring, block by block.** An ordered product over the `N` sites is the
ordered product, over the blocks, of the ordered products over their sites. -/
theorem prod_ofFn_blockSite {R : Type*} [Monoid R] :
    ∀ {M : ℕ} (ℓ : Fin M → ℕ) {N : ℕ} (hN : ∑ k, ℓ k = N) (f : Fin N → R),
      (List.ofFn f).prod =
        (List.ofFn fun k => (List.ofFn fun j : Fin (ℓ k) => f (blockSite hN k j)).prod).prod
  | 0, ℓ, N, hN, f => by
    have : N = 0 := by simpa using hN.symm
    subst this
    simp
  | M + 1, ℓ, N, hN, f => by
    set ℓ' : Fin M → ℕ := fun k => ℓ k.castSucc
    have hN' : N = (∑ k, ℓ' k) + ℓ (Fin.last M) := by rw [← hN, Fin.sum_univ_castSucc]
    have ih := prod_ofFn_blockSite ℓ' rfl
      (fun i => f (Fin.cast hN'.symm (Fin.castLE (Nat.le_add_right _ _) i)))
    have hoff : ∀ k : Fin M, blockOffset ℓ' k.val = blockOffset ℓ k.castSucc.val := fun k =>
      blockOffset_castSucc ℓ k.isLt.le
    have hlast : blockOffset ℓ (Fin.last M).val = ∑ k, ℓ' k := by
      rw [Fin.val_last, ← blockOffset_castSucc ℓ le_rfl, blockOffset_of_le _ le_rfl]
    rw [List.ofFn_congr hN', List.ofFn_add, List.prod_append, ih, List.ofFn_succ',
      List.prod_concat]
    congr 1
    · congr 1
      refine List.ofFn_inj.mpr (funext fun k => ?_)
      congr 1
      refine List.ofFn_inj.mpr (funext fun j => congrArg f (Fin.ext ?_))
      simp [hoff k]
    · congr 1
      refine List.ofFn_inj.mpr (funext fun j => congrArg f (Fin.ext ?_))
      simp only [Fin.val_cast, Fin.val_natAdd, blockSite_val]
      rw [hlast]

end MPSPreparation
