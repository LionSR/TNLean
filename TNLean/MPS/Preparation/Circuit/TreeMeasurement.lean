/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Protocol.Teleportation.LongRangeGates
import TNLean.MPS.Tensor.Overlap

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

Before level `i` the sites strictly inside the complete blocks of size `2^{i+1}`, those whose
residue modulo `2^{i+1}` lies in `{1, …, 2^{i+1} - 2}` (`MPSPreparation.blockInterior`), carry
`|0⟩`, and the gates of level `i`, acting on the residues `0` and `2^{i+1} - 1`, act on no site
strictly inside a complete block of a finer level. So every level is a layer of long-range gates
in the sense of `QICLean.Circuit.Protocol.Teleportation.LongRangeGates`, applied in depth at
most `5` with measurements, and the tree of `k` levels in depth at most `5k` on the vectors with
`|0⟩` strictly inside the complete blocks of all its levels (`MPSPreparation.treeInterior`,
`MPSPreparation.isImplementationOn_treeRounds`). No divisibility of `N` is assumed: only
complete blocks carry gates, and the sites of an incomplete block need no `|0⟩` on its account.

Every register of this tree is one site of dimension `d` and every node carries a two-site
unitary, whereas in arXiv:2307.01696, eq. (16), a register above the lowest level carries
`ℂ^{D²}`. Registers of several sites are the subject of
`QICLean.Circuit.Protocol.Teleportation.RegisterGates` and `TNLean.MPS.Preparation.RegisterTree`,
and the preparation of matrix product states in depth `O(log log(N/ε))` of
`TNLean.MPS.Preparation.LogLogDepthPreparation`.

## Main definitions

* `MPSPreparation.blockInterior` — the sites strictly inside the complete blocks of a given size.
* `MPSPreparation.treeInterior` — the sites strictly inside the complete blocks of the levels
  `0, …, k - 1`.
* `MPSPreparation.treeGate`, `MPSPreparation.levelGates`, `MPSPreparation.levelOp` — the gates
  of a level of the tree and their product.
* `MPSPreparation.treeOp` — the product of the first `k` levels, the coarsest applied first.
* `MPSPreparation.treeRounds` — the measurement circuit applying them.

## Main results

* `MPSPreparation.depth_treeRounds_le` — the circuit of `k` levels has depth at most `5k`.
* `MPSPreparation.isImplementationOn_treeRounds` — it implements the tree on the vectors
  with `|0⟩` at the sites of `MPSPreparation.treeInterior N k`.
* `MPSPreparation.exists_isMeasurementConversion_treeOp` — the tree applied to a nonzero
  product vector with `|0⟩` at these sites is converted from it with measurements in depth `5k`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d N : ℕ}

/-! ### Residues of sites -/

/-- The sites strictly inside the complete blocks of `B` consecutive sites: the residue modulo
`B` lies in `{1, …, B - 2}`, and the block `[q B, (q + 1) B)` containing the site,
`q = ⌊x / B⌋`, is contained in `{0, …, N - 1}`. -/
def blockInterior (N B : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ 1 ≤ x.val % B ∧ x.val % B + 2 ≤ B ∧ (x.val / B + 1) * B ≤ N

/-- The sites strictly inside a complete block of size `2^{i+1}` for some `i < k`: the sites on
which the tree of `k` levels needs `|0⟩`. No site of an incomplete block of size `2^{i+1}`
belongs to it through that block. -/
def treeInterior (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ ∃ i < k, x ∈ blockInterior N (2 ^ (i + 1))

theorem mem_blockInterior {B : ℕ} {x : Fin N} :
    x ∈ blockInterior N B ↔ 1 ≤ x.val % B ∧ x.val % B + 2 ≤ B ∧ (x.val / B + 1) * B ≤ N := by
  simp [blockInterior]

theorem mem_treeInterior {k : ℕ} {x : Fin N} :
    x ∈ treeInterior N k ↔ ∃ i < k, x ∈ blockInterior N (2 ^ (i + 1)) := by
  simp [treeInterior]

theorem treeInterior_mono {k k' : ℕ} (h : k ≤ k') : treeInterior N k ⊆ treeInterior N k' :=
  fun _ hx => by
    obtain ⟨i, hi, hx⟩ := mem_treeInterior.mp hx
    exact mem_treeInterior.mpr ⟨i, by omega, hx⟩

theorem blockInterior_subset_treeInterior (k : ℕ) :
    blockInterior N (2 ^ (k + 1)) ⊆ treeInterior N (k + 1) :=
  fun _ hx => mem_treeInterior.mpr ⟨k, Nat.lt_succ_self k, hx⟩

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
  u_mem_unitaryGroup := hu i p

/-- The gates of level `i`, one for each block `[p 2^{i+1}, (p + 1) 2^{i+1})` contained in
`{0, …, N - 1}`. -/
def levelGates (i : ℕ) : List (LongRangeGate d N) :=
  List.ofFn fun p : Fin (N / 2 ^ (i + 1)) => treeGate u hu i p p.isLt

/-- The sites of the stretch of a gate of the tree, by their values. -/
private theorem val_of_mem_span {i p : ℕ} {hp : p < N / 2 ^ (i + 1)} {x : Fin N}
    (hx : x ∈ (treeGate u hu i p hp).span) :
    ∃ t, t + 1 ≤ 2 ^ (i + 1) ∧ x.val = p * 2 ^ (i + 1) + t ∧
      (x ∈ (treeGate u hu i p hp).interior → 1 ≤ t ∧ t + 2 ≤ 2 ^ (i + 1)) := by
  have h1 := succ_mul_le_of_lt_div hp
  have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  have h3 := Nat.one_le_two_pow (n := i)
  obtain ⟨t, ht, rfl⟩ := (treeGate u hu i p hp).mem_span.mp hx
  change t ≤ 2 * (2 ^ i - 1) + 1 at ht
  have hlt : p * 2 ^ (i + 1) + t < N := by rw [Nat.succ_mul] at h1; omega
  refine ⟨t, by omega, val_natCast_add_natCast hlt, fun hint => ?_⟩
  obtain ⟨t', h1', h2', he⟩ := (treeGate u hu i p hp).mem_interior.mp hint
  change t' ≤ 2 * (2 ^ i - 1) at h2'
  have hL := (treeGate u hu i p hp).lt
  change 2 * (2 ^ i - 1) + 1 < N at hL
  have := add_natCast_injective ((p * 2 ^ (i + 1) : ℕ) : Fin N) (j := t) (k := t')
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
  rw [Finset.disjoint_left]
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

/-- The measurement circuit applying the levels `0, …, k - 1` of the tree, the coarsest first:
two rounds for each level (`QuantumCircuit.LongRangeGate.rounds`).

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
noncomputable def treeRounds : ℕ →
    Circuit (Geometry.ring N) KrausGate (ManyBody.Qudits (Fin N) d) (ManyBody.Qudits (Fin N) d)
  | 0 => Circuit.done _
  | i + 1 => (LongRangeGate.rounds (pairwise_levelGates u hu i)).comp (treeRounds i)

/-- The circuit of `k` levels has depth at most `5k`. -/
theorem depth_treeRounds_le (k : ℕ) : (treeRounds (N := N) u hu k).depth ≤ 5 * k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [treeRounds]
    exact (Circuit.depth_comp _ _).trans
      ((Nat.add_le_add (LongRangeGate.depth_rounds_le _) ih).trans_eq (by ring))

/-- The circuit of the tree is a measurement circuit. -/
theorem forall_treeRounds (k : ℕ) :
    (treeRounds (N := N) u hu k).Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement := by
  induction k with
  | zero => exact trivial
  | succ k ih =>
    rw [treeRounds]
    exact (LongRangeGate.forall_rounds _).comp _ ih

omit [NeZero N] in
/-- A product vector with `|0⟩` at the sites of `S` has `|0⟩` at the sites of `S`. -/
theorem isZeroOn_productVector {S : Finset (Fin N)} {v : Fin N → Fin d → ℂ}
    (hv : ∀ x ∈ S, ∀ j, j ≠ 0 → v x j = 0) :
    IsZeroOn S (fun σ : Cfg d N => ∏ i, v i (σ i)) := by
  intro y hy x hx
  by_contra h
  exact hy (Finset.prod_eq_zero (Finset.mem_univ x) (hv x hx _ h))

/-- The residue modulo `2^{i+1}` of a site `x` with `x + 1` a multiple of `2^{k+1}`, `i ≤ k`, is
`2^{i+1} - 1`. -/
private theorem mod_two_pow_eq_of_succ_dvd {i k x : ℕ} (hik : i ≤ k)
    (hx : 2 ^ (k + 1) ∣ x + 1) :
    x % 2 ^ (i + 1) + 1 = 2 ^ (i + 1) := by
  have hB : 2 ≤ 2 ^ (i + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 : (x + 1) % 2 ^ (i + 1) = 0 :=
    Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 2 (Nat.succ_le_succ hik)).trans hx)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 ^ (i + 1) by omega)] at h0
  have hlt := Nat.mod_lt x (show 0 < 2 ^ (i + 1) by omega)
  rcases Nat.lt_or_ge (x % 2 ^ (i + 1) + 1) (2 ^ (i + 1)) with h | h
  · rw [Nat.mod_eq_of_lt h] at h0
    omega
  · omega

/-- The gates of level `k` keep `|0⟩` at the sites strictly inside the complete blocks of the
finer levels `0, …, k - 1`. -/
theorem isZeroOn_levelOp_mulVec (k : ℕ) {v : Cfg d N → ℂ}
    (hv : IsZeroOn (treeInterior N (k + 1)) v) :
    IsZeroOn (treeInterior N k) (levelOp u hu k *ᵥ v) := by
  refine (hv.mono (treeInterior_mono (Nat.le_succ k))).mulVec_of_mem_supportedOperators
    disjoint_compl_right (list_prod_mem fun A hA => ?_)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hA
  obtain ⟨⟨p, hp⟩, rfl⟩ := List.mem_ofFn.mp hg
  refine ManyBody.supportedOperators_mono ?_ (LongRangeGate.op_mem_supportedOperators _)
  intro x hx
  refine Finset.mem_compl.mpr fun hx' => ?_
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  obtain ⟨i, hi, hx'⟩ := mem_treeInterior.mp hx'
  obtain ⟨hx1, hx2, -⟩ := mem_blockInterior.mp hx'
  rcases hx with rfl | rfl
  · rw [treeGate_a_val u hu hp] at hx1
    rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega)) _)] at hx1
    omega
  · rw [treeGate_far_val u hu hp] at hx2
    have h1 := Nat.one_le_two_pow (n := k + 1)
    have hdvd : 2 ^ (k + 1) ∣ p * 2 ^ (k + 1) + (2 ^ (k + 1) - 1) + 1 :=
      ⟨p + 1, by rw [Nat.mul_succ, Nat.mul_comm (2 ^ (k + 1)) p]; omega⟩
    have := mod_two_pow_eq_of_succ_dvd (i := i) (by omega) hdvd
    omega

omit [NeZero d] in
/-- The interiors of the gates of level `i` lie strictly inside the complete blocks of size
`2^{i+1}`. -/
theorem interior_subset_blockInterior {i : ℕ} {g : LongRangeGate d N}
    (hg : g ∈ levelGates u hu i) : g.interior ⊆ blockInterior N (2 ^ (i + 1)) := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := List.mem_ofFn.mp hg
  intro x hx
  obtain ⟨t, ht, hxt, hint⟩ := val_of_mem_span u hu (LongRangeGate.interior_subset_span _ hx)
  obtain ⟨h1, h2⟩ := hint hx
  have hB : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
  change x.val = p * 2 ^ (i + 1) + t at hxt
  have hmod : x.val % 2 ^ (i + 1) = t := by
    rw [hxt, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hdiv : x.val / 2 ^ (i + 1) = p :=
    Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  exact mem_blockInterior.mpr ⟨hmod ▸ h1, hmod ▸ h2, hdiv ▸ succ_mul_le_of_lt_div hp⟩

/-- **A binary tree of gates in depth `5k` with measurements.** The circuit of the levels
`0, …, k - 1`, of depth at most `5k`, implements the product of the levels, the coarsest applied
first, on the vectors with `|0⟩` at the sites strictly inside the complete blocks of sizes
`2, 4, …, 2^k`: whatever the outcomes, every output is a scalar multiple of the tree applied to
the input.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("every isometry in
eq. (16) takes constant time using measurement"). -/
theorem isImplementationOn_treeRounds (k : ℕ) :
    (treeRounds u hu k).IsImplementationOn KrausGate.ev
      {v | IsZeroOn (treeInterior N k) v} (treeOp u hu k) := by
  induction k with
  | zero =>
    exact Circuit.isImplementationOn_done _
  | succ k ih =>
    rw [treeRounds]
    exact ((LongRangeGate.isImplementationOn_rounds (pairwise_levelGates u hu k)).mono
      fun v hv g hg => IsZeroOn.mono hv ((interior_subset_blockInterior u hu hg).trans
        (blockInterior_subset_treeInterior k))).comp ih
      fun v hv => isZeroOn_levelOp_mulVec u hu k hv

/-- **Preparation of a tree state in depth `5k` with measurements.** Let `v` be a nonzero product
vector with `|0⟩` at the sites strictly inside the complete blocks of sizes `2, 4, …, 2^k`. The
tree of the levels `0, …, k - 1` applied to it is converted from it by a measurement circuit of
depth at most `5k`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem exists_isMeasurementConversion_treeOp (k : ℕ) {v : Fin N → Fin d → ℂ}
    (hv : (fun σ : Cfg d N => ∏ i, v i (σ i)) ≠ 0)
    (hv0 : ∀ x ∈ treeInterior N k, ∀ j, j ≠ 0 → v x j = 0) :
    ∃ w : Fin N → Fin d → ℂ, IsMeasurementConversion (Geometry.ring N) (5 * k)
      (fun σ ↦ ∏ i, w i (σ i)) (treeOp u hu k *ᵥ fun σ ↦ ∏ i, v i (σ i)) :=
  ⟨v, (isImplementationOn_treeRounds u hu k).isMeasurementConversion (forall_treeRounds u hu k)
    (depth_treeRounds_le u hu k) hv (isZeroOn_productVector hv0)⟩

end MPSPreparation
