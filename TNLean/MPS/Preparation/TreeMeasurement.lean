/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.LongRangeGates

/-!
# Binary trees of gates in depth `O(k)` with measurements

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies `k` layers of isometries to a block
of `2^k` sites; the isometries of the coarse layers act on registers far apart. The paragraph
"Tree-RG circuit with measurements" teleports these registers next to each other, so that every
layer takes constant depth and the `k` layers take depth `O(k)`. This file proves this for
binary trees of two-site gates on the ring of `N` sites.

## The tree

Level `i` of the tree cuts the ring into the blocks `[p 2^{i+1}, (p + 1) 2^{i+1})` contained in
`{0, …, N - 1}` and applies a two-site unitary `u i p` to the two endpoints
`p 2^{i+1}` and `p 2^{i+1} + 2^{i+1} - 1` of every block. The endpoints of a block of level `i`
are the left endpoint of its left half and the right endpoint of its right half, so each gate
joins the sites that carry the two halves after the coarser levels: a register entering a block
sits at one of its endpoints, and the gate of the block writes the other endpoint. The levels are
applied from the coarsest, `i = k - 1`, to the finest, `i = 0`, whose gates act on neighbouring
pairs.

Before level `i` the sites strictly inside the blocks of size `2^{i+1}`, those whose residue
modulo `2^{i+1}` lies in `{1, …, 2^{i+1} - 2}` (`MPSPreparation.blockInterior`), carry `|0⟩`,
and the gates of level `i`, acting on the residues `0` and `2^{i+1} - 1`, keep `|0⟩` at the
sites strictly inside the blocks of size `2^i`. So every level is a layer of long-range gates in
the sense of `TNLean.MPS.Preparation.LongRangeGates`, applied in depth `5` with measurements, and
the tree of `k` levels in depth `5k` (`MPSPreparation.isRoundsImplementationOn_treeRounds`).

## Main definitions

* `MPSPreparation.blockInterior` — the sites strictly inside the blocks of a given size.
* `MPSPreparation.treeGate`, `MPSPreparation.levelGates`, `MPSPreparation.levelOp` — the gates
  of a level of the tree and their product.
* `MPSPreparation.treeOp` — the product of the first `k` levels, the coarsest applied first.
* `MPSPreparation.treeRounds` — the measurement rounds applying them.

## Main results

* `MPSPreparation.sum_depth_treeRounds` — the rounds of `k` levels have depth `5k`.
* `MPSPreparation.isRoundsImplementationOn_treeRounds` — they implement the tree on the vectors
  with `|0⟩` strictly inside the blocks of size `2^k`.
* `MPSPreparation.isPreparedWithMeasurementRoundsInDepth_treeOp` — the tree applied to a nonzero
  product vector with `|0⟩` strictly inside the blocks of size `2^k` is prepared with measurement
  rounds in depth `5k`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-! ### Residues of sites -/

/-- The sites strictly inside the blocks of `B` consecutive sites: the residue modulo `B` lies in
`{1, …, B - 2}`. -/
def blockInterior (N B : ℕ) : Set (Fin N) := {x | 1 ≤ x.val % B ∧ x.val % B + 2 ≤ B}

theorem blockInterior_one : blockInterior N 1 = ∅ := by
  ext x
  simp [blockInterior]

/-- The sites strictly inside the blocks of size `c` lie strictly inside the blocks of size
`2c`. -/
theorem blockInterior_subset_two_mul (c : ℕ) : blockInterior N c ⊆ blockInterior N (2 * c) := by
  rintro x ⟨h1, h2⟩
  have hc : 0 < c := by omega
  set R := x.val % (2 * c)
  have hR : R < 2 * c := Nat.mod_lt _ (by omega)
  have hRc : R % c = x.val % c := Nat.mod_mod_of_dvd _ (Dvd.intro_left 2 rfl)
  have hdiv := Nat.mod_add_div R c
  have hq : R / c < 2 := (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
  constructor
  · interval_cases h : R / c <;> simp at hdiv <;> omega
  · interval_cases h : R / c <;> simp at hdiv <;> omega

/-! ### The gates of the tree -/

private theorem succ_mul_le_of_lt_div {p B : ℕ} (hp : p < N / B) : (p + 1) * B ≤ N :=
  (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero fun h => by simp [h] at hp)).mp hp

private theorem two_pow_le_of_lt_div {p i : ℕ} (hp : p < N / 2 ^ (i + 1)) : 2 ^ (i + 1) ≤ N :=
  le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos p)) (succ_mul_le_of_lt_div hp)

variable [NeZero N]

open Fin.NatCast

private theorem val_natCast_add_natCast {m t : ℕ} (h : m + t < N) :
    (((m : ℕ) : Fin N) + (t : Fin N)).val = m + t := by
  rw [Fin.val_add, Fin.val_cast_of_lt (by omega), Fin.val_cast_of_lt (by omega),
    Nat.mod_eq_of_lt h]

variable (u : ℕ → ℕ → Matrix (Cfg d 2) (Cfg d 2) ℂ)
  (hu : ∀ i p, u i p ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ))

/-- The gate of the block `p` of level `i`: the unitary `u i p` on the endpoints `p 2^{i+1}` and
`p 2^{i+1} + 2^{i+1} - 1` of the block, a long-range gate with `L = 2^i - 1`.

Source: arXiv:2307.01696, eq. (16) (the isometries of the tree) and paragraph "Tree-RG circuit
with measurements". -/
def treeGate (i p : ℕ) (hp : p < N / 2 ^ (i + 1)) : LongRangeGate d N where
  a := ((p * 2 ^ (i + 1) : ℕ) : Fin N)
  L := 2 ^ i - 1
  lt := by
    have h1 := two_pow_le_of_lt_div hp
    have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
    have h3 := Nat.one_le_two_pow (n := i)
    omega
  u := u i p
  u_mem_unitary := hu i p

/-- The gates of level `i`, one for each block `[p 2^{i+1}, (p + 1) 2^{i+1})` contained in
`{0, …, N - 1}`. -/
def levelGates (i : ℕ) : List (LongRangeGate d N) :=
  List.ofFn fun p : Fin (N / 2 ^ (i + 1)) => treeGate u hu i p p.isLt

/-- The sites of the stretch of a gate of the tree, by their values. -/
private theorem val_of_mem_span {i p : ℕ} {hp : p < N / 2 ^ (i + 1)} {x : Fin N}
    (hx : x ∈ (treeGate u hu i p hp).span) :
    ∃ t, t + 1 ≤ 2 ^ (i + 1) ∧ x.val = p * 2 ^ (i + 1) + t ∧
      ((treeGate u hu i p hp).interior x → 1 ≤ t ∧ t + 2 ≤ 2 ^ (i + 1)) := by
  have h1 := succ_mul_le_of_lt_div hp
  have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  have h3 := Nat.one_le_two_pow (n := i)
  obtain ⟨t, ht, rfl⟩ := hx
  change t ≤ 2 * (2 ^ i - 1) + 1 at ht
  have hlt : p * 2 ^ (i + 1) + t < N := by rw [Nat.succ_mul] at h1; omega
  refine ⟨t, by omega, val_natCast_add_natCast hlt, fun ⟨t', h1', h2', he⟩ => ?_⟩
  change t' ≤ 2 * (2 ^ i - 1) at h2'
  have hL := (treeGate u hu i p hp).lt
  change 2 * (2 ^ i - 1) + 1 < N at hL
  have := add_natCast_injective (((p * 2 ^ (i + 1) : ℕ) : Fin N)) (j := t) (k := t')
    (by omega) (by omega) he
  omega

theorem treeGate_a_val {i p : ℕ} (hp : p < N / 2 ^ (i + 1)) :
    (treeGate u hu i p hp).a.val = p * 2 ^ (i + 1) := by
  have h1 := succ_mul_le_of_lt_div hp
  rw [Nat.succ_mul] at h1
  exact Fin.val_cast_of_lt (by have := Nat.one_le_two_pow (n := i + 1); omega)

theorem treeGate_far_val {i p : ℕ} (hp : p < N / 2 ^ (i + 1)) :
    (treeGate u hu i p hp).far.val = p * 2 ^ (i + 1) + (2 ^ (i + 1) - 1) := by
  have h1 := succ_mul_le_of_lt_div hp
  have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  have h3 := Nat.one_le_two_pow (n := i)
  rw [Nat.succ_mul] at h1
  change (((p * 2 ^ (i + 1) : ℕ) : Fin N) + ((2 * (2 ^ i - 1) + 1 : ℕ) : Fin N)).val = _
  rw [val_natCast_add_natCast (by omega)]
  omega

theorem pairwise_levelGates (i : ℕ) :
    (levelGates (d := d) (N := N) u hu i).Pairwise fun g g' => Disjoint g.span g'.span := by
  rw [levelGates, List.pairwise_ofFn]
  intro p p' hpp'
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨t, ht, hxt, -⟩ := val_of_mem_span u hu hx
  obtain ⟨t', ht', hxt', -⟩ := val_of_mem_span u hu hx'
  have hlt : (p : ℕ) + 1 ≤ p' := hpp'
  have : ((p : ℕ) + 1) * 2 ^ (i + 1) ≤ (p' : ℕ) * 2 ^ (i + 1) := Nat.mul_le_mul_right _ hlt
  rw [Nat.succ_mul] at this
  omega

/-- The product of the gates of level `i`. -/
noncomputable def levelOp (i : ℕ) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  ((levelGates u hu i).map LongRangeGate.op).prod

/-- The product of the levels `0, …, k - 1` of the tree, the coarsest applied first.

Source: arXiv:2307.01696, eq. (16). -/
noncomputable def treeOp : ℕ → Matrix (Cfg d N) (Cfg d N) ℂ
  | 0 => 1
  | i + 1 => treeOp i * levelOp u hu i

variable [NeZero d]

/-- The measurement rounds applying the levels `0, …, k - 1` of the tree, the coarsest first:
two rounds for each level (`MPSPreparation.LongRangeGate.rounds`).

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
noncomputable def treeRounds : ℕ → List (MeasurementRound d N)
  | 0 => []
  | i + 1 => LongRangeGate.rounds (pairwise_levelGates u hu i) ++ treeRounds i

/-- The rounds of `k` levels have depth `5k`. -/
theorem sum_depth_treeRounds (k : ℕ) :
    ((treeRounds (N := N) u hu k).map MeasurementRound.depth).sum = 5 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [treeRounds, List.map_append, List.sum_append, LongRangeGate.sum_depth_rounds, ih]
    ring

omit [NeZero N] in
/-- A product vector with `|0⟩` at the sites of `S` has `|0⟩` at the sites of `S`. -/
theorem isZeroOn_productVector {S : Set (Fin N)} {v : Fin N → Fin d → ℂ}
    (hv : ∀ x ∈ S, ∀ j, j ≠ 0 → v x j = 0) : IsZeroOn S (productVector v) := by
  intro y hy x hx
  by_contra h
  exact hy (Finset.prod_eq_zero (Finset.mem_univ x) (hv x hx _ h))

/-- The gates of level `i` keep `|0⟩` at the sites strictly inside the blocks of size `2^i`. -/
theorem isZeroOn_levelOp_mulVec (i : ℕ) {v : Cfg d N → ℂ}
    (hv : IsZeroOn (blockInterior N (2 ^ (i + 1))) v) :
    IsZeroOn (blockInterior N (2 ^ i)) (levelOp u hu i *ᵥ v) := by
  have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  refine (hv.mono (h2 ▸ blockInterior_subset_two_mul _)).mulVec_of_mem_supportedOperators
    disjoint_compl_right (list_prod_mem_supportedOperators _ fun A hA => ?_)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hA
  obtain ⟨⟨p, hp⟩, rfl⟩ := List.mem_ofFn.mp hg
  refine supportedOperators_mono ?_ (LongRangeGate.op_mem_supportedOperators _)
  have h3 := Nat.one_le_two_pow (n := i)
  rintro x (rfl | rfl) ⟨hx1, hx2⟩
  · rw [treeGate_a_val u hu hp] at hx1
    rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (pow_dvd_pow 2 (Nat.le_succ i)) _)] at hx1
    omega
  · obtain ⟨c, hc⟩ : ∃ c, 2 ^ i = c + 1 := ⟨2 ^ i - 1, by omega⟩
    have hfar : p * 2 ^ (i + 1) + (2 ^ (i + 1) - 1) = c + (c + 1) * (2 * p + 1) := by
      rw [h2, hc]
      have : 2 * (c + 1) - 1 = 2 * c + 1 := by omega
      rw [this]
      ring
    rw [treeGate_far_val u hu hp, hfar, hc, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)] at hx2
    omega

omit [NeZero d] in
/-- The interiors of the gates of level `i` lie strictly inside the blocks of size `2^{i+1}`. -/
theorem interior_subset_blockInterior {i : ℕ} {g : LongRangeGate d N}
    (hg : g ∈ levelGates u hu i) : g.interior ⊆ blockInterior N (2 ^ (i + 1)) := by
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hg
  intro x hx
  obtain ⟨t, -, hxt, hint⟩ := val_of_mem_span u hu (LongRangeGate.interior_subset_span _ hx)
  obtain ⟨h1, h2⟩ := hint hx
  have : x.val % 2 ^ (i + 1) = t := by
    rw [hxt, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  exact ⟨this ▸ h1, this ▸ h2⟩

/-- **A binary tree of gates in depth `5k` with measurements.** The rounds of the levels
`0, …, k - 1`, of total depth `5k`, implement the product of the levels, the coarsest applied
first, on the vectors with `|0⟩` at the sites strictly inside the blocks of size `2^k`: whatever
the outcomes, every output is a scalar multiple of the tree applied to the input.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("every isometry in
eq. (16) takes constant time using measurement"). -/
theorem isRoundsImplementationOn_treeRounds (k : ℕ) :
    MeasurementRound.IsRoundsImplementationOn (treeRounds u hu k)
      {v | IsZeroOn (blockInterior N (2 ^ k)) v} (treeOp u hu k) := by
  induction k with
  | zero =>
    exact MeasurementRound.isRoundsImplementationOn_nil _
  | succ k ih =>
    refine ((LongRangeGate.isRoundsImplementationOn_rounds (pairwise_levelGates u hu k)).mono
      fun v hv g hg => IsZeroOn.mono hv (interior_subset_blockInterior u hu hg)).append ih
      fun v hv => isZeroOn_levelOp_mulVec u hu k hv

/-- **Preparation of a tree state in depth `5k` with measurements.** Let `v` be a nonzero product
vector with `|0⟩` at the sites strictly inside the blocks of size `2^k`. The tree of the levels
`0, …, k - 1` applied to it is prepared with measurement rounds in depth `5k`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem isPreparedWithMeasurementRoundsInDepth_treeOp (k : ℕ) {v : Fin N → Fin d → ℂ}
    (hv : productVector v ≠ 0) (hv0 : ∀ x ∈ blockInterior N (2 ^ k), ∀ j, j ≠ 0 → v x j = 0) :
    IsPreparedWithMeasurementRoundsInDepth (5 * k) (treeOp u hu k *ᵥ productVector v) := by
  have := (isRoundsImplementationOn_treeRounds u hu k).isPreparedWithMeasurementRoundsInDepth hv
    (isZeroOn_productVector hv0)
  rwa [sum_depth_treeRounds] at this

end MPSPreparation
