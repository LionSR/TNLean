/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthUpperBound
import TNLean.Circuit.Teleportation.RegisterGates

/-!
# Binary trees of gates on registers in depth `O(k)` with measurements

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies to every block of the ring a binary
tree of isometries; above the lowest level each isometry maps a register carrying `ℂ^{D²}` to
two such registers. This file places such trees on blocks of `q = s 2^{k+1}` sites with
registers of `s` sites and proves, with the register gates of
`TNLean.Circuit.Teleportation.RegisterGates`, that the trees of all the blocks are applied with
measurements in depth `(k + 1)(4s + K + 2)`, if every node is a product of at most `K` gates
on neighbouring sites.

## The tree of a block

Group the `q` sites of a block into `2^{k+1}` registers of `s` consecutive sites. At depth `j`
(`0 ≤ j ≤ k`, the depth `0` being the root) the registers are cut into the `2^j` sub-blocks
`[p 2^{k+1-j}, (p + 1) 2^{k+1-j})`, and a unitary `X j p` on `2s` sites acts on the first and
the last register of the sub-block `p` (`MPSPreparation.regWindow`). The operator of depth `j`
is the product of these unitaries (`MPSPreparation.regLevelOp`), and the tree is the product
of the depths `k, …, 0`, the root applied first (`MPSPreparation.regTreeOp`). The registers of
a sub-block of depth `j` are the first and the last register of its two halves, so a unitary of
depth `j` writes the registers on which the two unitaries below it act.

## Measurements

On the ring of `N` sites cut into `M` blocks of `q` sites, the unitaries of depth `j` of all
the blocks are register gates on pairwise disjoint stretches (`MPSPreparation.regLevelGates`),
and the unitaries of depth `j' < j` act on no site strictly between the two registers of a
unitary of depth `j`. So the depths are applied one after the other, each in depth
`4s + K + 2` (`QuantumCircuit.RegisterGate.exists_rounds`), on the vectors with `|0⟩` at every
site of every block other than its first and its last `s` sites
(`MPSPreparation.exists_rounds_blockLayerOp_regTreeOp`).

## Main definitions

* `MPSPreparation.regWindow`, `MPSPreparation.regLevelOp`, `MPSPreparation.regTreeOp`.
* `MPSPreparation.regGate`, `MPSPreparation.regLevelGates`.

## Main results

* `MPSPreparation.list_prod_map_op_regLevelGates` — the gates of depth `j` of all the blocks
  form the layer `⊗ₖ (regLevelOp j)` of the blocks.
* `MPSPreparation.exists_rounds_blockLayerOp_regTreeOp`.
* `MPSPreparation.isZeroOn_pairLayerOp_mulVec_productVector` — the pairs leave `|0⟩` at the
  sites of every block other than its first and its last `s` sites.
* `MPSPreparation.mul_self_le_pow_of_isInjective_blockTensor` — an injective blocked tensor over
  `m` sites has `D² ≤ d^m`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

open Fin.NatCast

variable {d s : ℕ}

/-! ### Layers on blocks -/

section BlockLayer

variable {M N : ℕ} {ℓ : Fin M → ℕ}

/-- Moving along a block. -/
theorem blockSite_add_natCast [NeZero N] (hN : ∑ k, ℓ k = N) (b : Fin M) (y : Fin (ℓ b))
    (m : ℕ) (h : y.val + m < ℓ b) :
    blockSite hN b y + (m : Fin N) = blockSite hN b ⟨y.val + m, h⟩ := by
  have hlt := blockOffset_add_lt hN b ⟨y.val + m, h⟩
  apply Fin.ext
  rw [Fin.val_add, blockSite_val, blockSite_val, Fin.val_natCast, Nat.add_mod_mod,
    Nat.mod_eq_of_lt (by simpa [Nat.add_assoc] using hlt)]
  simp [Nat.add_assoc]

/-- The layer of the products `U k * V k` on the blocks is the product of the layers. -/
theorem blockLayerOp_mul (hN : ∑ k, ℓ k = N) (U V : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ) :
    blockLayerOp hN (fun k => U k * V k) = blockLayerOp hN U * blockLayerOp hN V := by
  unfold blockLayerOp
  rw [← Finset.noncommProd_mul_distrib (fun k => embedOp (blockSite hN k) (U k))
    (fun k => embedOp (blockSite hN k) (V k)) _ _ fun k _ k' _ h =>
      commute_embedOp_of_disjoint (blockSite_injective hN k) (blockSite_injective hN k')
        (disjoint_range_blockSite hN h) _ _]
  exact Finset.noncommProd_congr rfl (fun k _ => (embedOp_mul (blockSite_injective hN k) _ _).symm)
    _

theorem blockLayerOp_one (hN : ∑ k, ℓ k = N) :
    blockLayerOp (d := d) hN (fun _ => 1) = 1 := by
  unfold blockLayerOp
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun k _ => embedOp_one _, one_pow]

/-- The layer on the blocks as a product along the list of the blocks. -/
theorem blockLayerOp_eq_list_prod (hN : ∑ k, ℓ k = N)
    (U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ) :
    blockLayerOp hN U = ((List.finRange M).map fun k => embedOp (blockSite hN k) (U k)).prod := by
  unfold blockLayerOp
  rw [← Finset.noncommProd_toFinset (List.finRange M) _ _ (List.nodup_finRange M)]
  exact Finset.noncommProd_congr (List.toFinset_finRange M).symm (fun _ _ => rfl) _

end BlockLayer

/-! ### The pairs and the registers -/

/-- The layer of pairs applied to the all-`|0⟩` state leaves `|0⟩` at every site of every block
other than its first and its last `s` sites. -/
theorem isZeroOn_pairLayerOp_mulVec_productVector {M N : ℕ} [NeZero d] {ℓ : Fin M → ℕ}
    (hN : ∑ b, ℓ b = N) (hr : ∀ b, s + s ≤ ℓ b)
    (W : Fin M → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) :
    IsZeroOn {x | ∃ b y, s ≤ y.val ∧ y.val + s < ℓ b ∧ x = blockSite hN b y}
      (pairLayerOp hN hr W *ᵥ productVector fun _ => Pi.single ⟨0, NeZero.pos d⟩ 1) := by
  intro x hx i hi
  rw [pairLayerOp_mulVec_apply] at hx
  split_ifs at hx with h
  · obtain ⟨b, y, hy1, hy2, rfl⟩ := hi
    have hx0 := h (blockSite hN b y) fun b' j hj => by
      have := (blockSite_mem_pairSite hN hr b y).mp ⟨b', j, hj⟩
      omega
    rw [hx0]
    exact Fin.ext (by simp)
  · exact absurd rfl hx

/-- An injective tensor with physical dimension `d^m` has `D² ≤ d^m`: its matrices span the
`D²`-dimensional matrix algebra. -/
theorem mul_self_le_pow_of_isInjective_blockTensor {D m : ℕ} {A : MPSTensor d D}
    (h : Kraus.IsInjective (blockTensor A m)) : D * D ≤ d ^ m := by
  have h1 := finrank_range_le_card (R := ℂ) (blockTensor A m)
  rw [Set.finrank, h, finrank_top, Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_self, mul_one] at h1
  simpa [blockPhysDim_eq_pow] using h1

/-! ### The tree of a block -/

section Tree

variable (k : ℕ)

/-- The number `2^{k+1-j}` of registers of a sub-block of depth `j`. -/
def regSpan (j : ℕ) : ℕ := 2 ^ (k + 1 - j)

/-- The offset, from the first site of its sub-block, of the site `t` of the two registers of a
unitary of depth `j`. -/
def regOffset (s j : ℕ) (t : Fin (s + s)) : ℕ :=
  if t.val < s then t.val else t.val + s * (regSpan k j - 2)

theorem mul_sub_two_add_two_mul {s B : ℕ} (hB : 2 ≤ B) : s * (B - 2) + 2 * s = s * B := by
  obtain ⟨c, rfl⟩ : ∃ c, B = c + 2 := ⟨B - 2, by omega⟩
  rw [Nat.add_sub_cancel]; ring

variable [NeZero s]

theorem block_pos : 0 < s * 2 ^ (k + 1) :=
  Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne s)) (Nat.two_pow_pos _)

/-- The sites of the first and of the last register of the sub-block `p` of depth `j` of a block
of `s 2^{k+1}` sites: `X j p` acts on them.

Source: arXiv:2307.01696, eq. (16) (the isometries of the tree). -/
def regWindow (j p : ℕ) (t : Fin (s + s)) : Fin (s * 2 ^ (k + 1)) :=
  ⟨(s * (p * regSpan k j) + regOffset k s j t) % (s * 2 ^ (k + 1)),
    Nat.mod_lt _ (block_pos k)⟩

variable {k}

theorem regSpan_eq {j : ℕ} (hj : j ≤ k) : regSpan k j = 2 * 2 ^ (k - j) := by
  rw [regSpan, show k + 1 - j = (k - j) + 1 by omega, pow_succ, mul_comm]

theorem two_le_regSpan {j : ℕ} (hj : j ≤ k) : 2 ≤ regSpan k j := by
  rw [regSpan_eq hj]; have := Nat.one_le_two_pow (n := k - j); omega

theorem succ_mul_regSpan_le {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) :
    (p + 1) * regSpan k j ≤ 2 ^ (k + 1) := by
  calc (p + 1) * regSpan k j ≤ 2 ^ j * regSpan k j := Nat.mul_le_mul_right _ hp
    _ = 2 ^ (k + 1) := by rw [regSpan, ← pow_add]; congr 1; omega

omit [NeZero s] in
theorem regOffset_lt {j : ℕ} (hj : j ≤ k) (t : Fin (s + s)) :
    regOffset k s j t < s * regSpan k j := by
  have := mul_sub_two_add_two_mul (s := s) (two_le_regSpan hj)
  unfold regOffset; split_ifs <;> omega

omit [NeZero s] in
theorem mul_mul_regSpan_add_lt {j p m : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j)
    (hm : m < s * regSpan k j) : s * (p * regSpan k j) + m < s * 2 ^ (k + 1) := by
  have := Nat.mul_le_mul_left s (succ_mul_regSpan_le hj hp)
  rw [Nat.succ_mul, Nat.mul_add] at this
  omega

theorem regWindow_val {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) (t : Fin (s + s)) :
    (regWindow k j p t).val = s * (p * regSpan k j) + regOffset k s j t :=
  Nat.mod_eq_of_lt (mul_mul_regSpan_add_lt hj hp (regOffset_lt hj t))

theorem regWindow_injective {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) :
    Function.Injective (regWindow (s := s) k j p) := by
  intro t t' h
  have h' := congrArg Fin.val h
  rw [regWindow_val hj hp, regWindow_val hj hp] at h'
  have := two_le_regSpan hj
  unfold regOffset at h'
  exact Fin.ext (by split_ifs at h' <;> omega)

omit [NeZero s] in
/-- Sites of distinct sub-blocks of the same length are distinct. -/
theorem mul_mul_add_ne_of_ne {B p p' o o' : ℕ} (hpp : p ≠ p') (ho : o < s * B)
    (ho' : o' < s * B) : s * (p * B) + o ≠ s * (p' * B) + o' := by
  intro h
  rcases Nat.lt_or_gt_of_ne hpp with hlt | hlt
  · have := Nat.mul_le_mul_left s (Nat.mul_le_mul_right B hlt)
    rw [Nat.succ_mul, Nat.mul_add] at this
    omega
  · have := Nat.mul_le_mul_left s (Nat.mul_le_mul_right B hlt)
    rw [Nat.succ_mul, Nat.mul_add] at this
    omega

omit [NeZero s] in
/-- A register of depth `j` is not strictly between the two registers of a sub-block of depth
`j`. -/
theorem regWindow_val_ne_of_interior {j p p' m : ℕ} (hj : j ≤ k) (t : Fin (s + s))
    (hm1 : s ≤ m) (hm2 : m + s < s * regSpan k j) :
    s * (p' * regSpan k j) + regOffset k s j t ≠ s * (p * regSpan k j) + m := by
  by_cases hpp : p' = p
  · subst hpp
    have := mul_sub_two_add_two_mul (s := s) (two_le_regSpan hj)
    unfold regOffset
    split_ifs <;> omega
  · exact mul_mul_add_ne_of_ne hpp (regOffset_lt hj t) (by omega)

/-- The windows of depth `j` are pairwise disjoint and injective. -/
theorem regWindow_injective₂ {j : ℕ} (hj : j ≤ k) :
    Function.Injective fun pt : Fin (2 ^ j) × Fin (s + s) => regWindow (s := s) k j pt.1 pt.2 := by
  rintro ⟨p, t⟩ ⟨p', t'⟩ h
  have h' := congrArg Fin.val h
  simp only [regWindow_val hj p.isLt, regWindow_val hj p'.isLt] at h'
  by_cases hpp : p = p'
  · subst hpp
    exact Prod.ext rfl (regWindow_injective hj p.isLt (Fin.ext (by
      rw [regWindow_val hj p.isLt, regWindow_val hj p.isLt]; omega)))
  · exact absurd h' (mul_mul_add_ne_of_ne (fun h => hpp (Fin.ext h)) (regOffset_lt hj t)
      (regOffset_lt hj t'))

/-- The product of the unitaries of depth `j` of a block.

Source: arXiv:2307.01696, eq. (16) (the layer `(V⁽ʲ⁾)^{⊗ ⋯}` of the tree). -/
noncomputable def regLevelOp (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) (k j : ℕ) :
    Matrix (Cfg d (s * 2 ^ (k + 1))) (Cfg d (s * 2 ^ (k + 1))) ℂ :=
  ((List.finRange (2 ^ j)).map fun p : Fin (2 ^ j) => embedOp (regWindow k j p) (X j p)).prod

/-- The tree of a block: the products of the depths `j - 1, …, 0`, the root applied first.

Source: arXiv:2307.01696, eq. (16). -/
noncomputable def regTreeOp (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) (k : ℕ) :
    ℕ → Matrix (Cfg d (s * 2 ^ (k + 1))) (Cfg d (s * 2 ^ (k + 1))) ℂ
  | 0 => 1
  | j + 1 => regLevelOp X k j * regTreeOp X k j

/-! ### The trees of all the blocks of a ring -/

variable {M N : ℕ} [NeZero N] (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ)
  (hN : ∑ _ : Fin M, s * 2 ^ (k + 1) = N)

omit [NeZero s] in
include hN in
theorem block_le : s * 2 ^ (k + 1) ≤ N := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp at hN; exact absurd hN.symm (NeZero.ne N)
  · rw [← hN, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.le_mul_of_pos_left _ hM

/-- The unitary of depth `j` of the sub-block `p` of the block `b`, as a register gate on the
ring.

Source: arXiv:2307.01696, eq. (16) and paragraph "Tree-RG circuit with measurements". -/
def regGate (j : ℕ) (b : Fin M) (p : ℕ) : RegisterGate d N s where
  a := blockSite hN b ⟨(s * (p * regSpan k j)) % (s * 2 ^ (k + 1)), Nat.mod_lt _ (block_pos k)⟩
  L := s * (2 ^ (k - j) - 1)
  le := by
    have h1 := Nat.one_le_two_pow (n := k - j)
    have h2 : 2 ^ (k - j) ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (Nat.sub_le k j)
    have h3 : s * (2 ^ (k - j) - 1) + s = s * 2 ^ (k - j) := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h4 : s * 2 ^ (k - j) ≤ s * 2 ^ k := Nat.mul_le_mul_left s h2
    have h5 : s * 2 ^ (k + 1) = 2 * (s * 2 ^ k) := by rw [pow_succ]; ring
    have := block_le hN
    omega
  X := X j p

/-- The register gates of depth `j` of all the blocks. -/
def regLevelGates (j : ℕ) : List (RegisterGate d N s) :=
  (List.finRange M).flatMap fun b =>
    (List.finRange (2 ^ j)).map fun p : Fin (2 ^ j) => regGate X hN j b p

variable {X hN}

theorem two_mul_regGate_L {j : ℕ} (hj : j ≤ k) (b : Fin M) (p : ℕ) :
    2 * (regGate X hN j b p).L = s * (regSpan k j - 2) := by
  change 2 * (s * (2 ^ (k - j) - 1)) = _
  rw [regSpan_eq hj]
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (k - j) = c + 1 := ⟨_, (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm⟩
  rw [hc, Nat.add_sub_cancel, show 2 * (c + 1) - 2 = 2 * c by omega]
  ring

/-- The sites `a + m` of a gate of depth `j` are the sites `s p 2^{k+1-j} + m` of its block. -/
theorem regGate_a_add {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) (b : Fin M) {m : ℕ}
    (hm : m < s * regSpan k j) :
    (regGate X hN j b p).a + (m : Fin N) =
      blockSite hN b ⟨s * (p * regSpan k j) + m, mul_mul_regSpan_add_lt hj hp hm⟩ := by
  have hlt := mul_mul_regSpan_add_lt hj hp hm
  have hmod : s * (p * regSpan k j) % (s * 2 ^ (k + 1)) = s * (p * regSpan k j) :=
    Nat.mod_eq_of_lt (by omega)
  change blockSite hN b _ + _ = _
  rw [blockSite_add_natCast hN b _ m (by simp only [hmod]; exact hlt)]
  exact congrArg (blockSite hN b) (Fin.ext (by simp only [hmod]))

/-- The registers of a gate of depth `j` are the window of its sub-block. -/
theorem regGate_sites {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) (b : Fin M) :
    (regGate X hN j b p).sites = blockSite hN b ∘ regWindow k j p := by
  funext t
  have hoff : (regGate X hN j b p).offset t = regOffset k s j t := by
    simp only [RegisterGate.offset, regOffset, two_mul_regGate_L hj]
  rw [RegisterGate.sites, hoff, regGate_a_add hj hp b (regOffset_lt hj t), Function.comp_apply]
  congr 1
  exact Fin.ext (regWindow_val hj hp t).symm

theorem mem_span_regGate {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) {b : Fin M} {x : Fin N}
    (hx : x ∈ (regGate X hN j b p).span) :
    ∃ m, ∃ hm : m < s * regSpan k j,
      x = blockSite hN b ⟨s * (p * regSpan k j) + m, mul_mul_regSpan_add_lt hj hp hm⟩ := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hm' : m < s * regSpan k j := by
    have := two_mul_regGate_L (X := X) (hN := hN) hj b p
    have := mul_sub_two_add_two_mul (s := s) (two_le_regSpan hj)
    omega
  exact ⟨m, hm', regGate_a_add hj hp b hm'⟩

theorem mem_interior_regGate {j p : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j) {b : Fin M} {x : Fin N}
    (hx : x ∈ (regGate X hN j b p).interior) :
    ∃ m, ∃ hm : m < s * regSpan k j, s ≤ m ∧ m + s < s * regSpan k j ∧
      x = blockSite hN b ⟨s * (p * regSpan k j) + m, mul_mul_regSpan_add_lt hj hp hm⟩ := by
  obtain ⟨m, hm1, hm2, rfl⟩ := hx
  have hL := two_mul_regGate_L (X := X) (hN := hN) hj b p
  have := mul_sub_two_add_two_mul (s := s) (two_le_regSpan hj)
  have hm' : m < s * regSpan k j := by omega
  exact ⟨m, hm', hm1, by omega, regGate_a_add hj hp b hm'⟩

omit [NeZero s] [NeZero N] in
/-- Two sites of distinct sub-blocks of depth `j` are distinct. -/
theorem blockSite_ne_of_subBlock_ne {j p p' m m' : ℕ} (hj : j ≤ k) (hp : p < 2 ^ j)
    (hp' : p' < 2 ^ j) {b b' : Fin M} (hm : m < s * regSpan k j) (hm' : m' < s * regSpan k j)
    (hne : b ≠ b' ∨ p ≠ p') :
    blockSite hN b ⟨s * (p * regSpan k j) + m, mul_mul_regSpan_add_lt hj hp hm⟩ ≠
      blockSite hN b' ⟨s * (p' * regSpan k j) + m', mul_mul_regSpan_add_lt hj hp' hm'⟩ := by
  intro h
  obtain ⟨rfl, h'⟩ := (blockSite_eq_iff hN).mp h
  change s * (p * regSpan k j) + m = s * (p' * regSpan k j) + m' at h'
  rcases hne with hne | hne
  · exact hne rfl
  · exact mul_mul_add_ne_of_ne hne hm hm' h'

theorem mem_regLevelGates {j : ℕ} {g : RegisterGate d N s} (hg : g ∈ regLevelGates X hN j) :
    ∃ b : Fin M, ∃ p < 2 ^ j, g = regGate X hN j b p := by
  obtain ⟨b, -, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨b, p, p.isLt, rfl⟩

/-- The stretches of the gates of depth `j` are pairwise disjoint. -/
theorem pairwise_regLevelGates {j : ℕ} (hj : j ≤ k) :
    (regLevelGates X hN j).Pairwise fun g g' => Disjoint g.span g'.span := by
  have key : ∀ (b b' : Fin M) (p p' : Fin (2 ^ j)), (b ≠ b' ∨ p ≠ p') →
      Disjoint (regGate X hN j b p).span (regGate X hN j b' p').span := by
    intro b b' p p' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨m, hm, rfl⟩ := mem_span_regGate hj p.isLt hx
    obtain ⟨m', hm', he⟩ := mem_span_regGate hj p'.isLt hx'
    exact blockSite_ne_of_subBlock_ne hj p.isLt p'.isLt hm hm'
      (hne.imp id fun h h' => h (Fin.ext h')) he
  rw [regLevelGates, List.pairwise_flatMap]
  refine ⟨fun b _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.Pairwise.imp (fun h => key b b _ _ (Or.inr h)) (List.nodup_finRange _)
  · refine List.Pairwise.imp (fun {b b'} (h : b ≠ b') => ?_) (List.nodup_finRange M)
    intro g hg g' hg'
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
    obtain ⟨p', -, rfl⟩ := List.mem_map.mp hg'
    exact key b b' p p' (Or.inl h)

/-- **The gates of depth `j` of all the blocks are the layer of the unitaries of depth `j` on
the blocks.** -/
theorem list_prod_map_op_regLevelGates {j : ℕ} (hj : j ≤ k) :
    ((regLevelGates X hN j).map RegisterGate.op).prod =
      blockLayerOp hN fun _ => regLevelOp X k j := by
  rw [blockLayerOp_eq_list_prod, regLevelGates, List.map_flatMap, List.flatMap_def,
    List.prod_flatten, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  rw [Function.comp_apply, regLevelOp, embedOp_list_prod (blockSite_injective hN b), List.map_map,
    List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp_apply, RegisterGate.op, regGate_sites hj p.isLt b]
  rw [embedOp_embedOp (blockSite_injective hN b)]
  rfl

/-! ### The registers of the coarser depths -/

omit [NeZero s] in
/-- A register of a unitary of depth `j' < j` is not strictly between the two registers of a
unitary of depth `j`: at depth `j` its register index is `0` or `2^{k+1-j} - 1` modulo the
length `2^{k+1-j}` of the sub-blocks of depth `j`. -/
theorem regWindow_val_ne {j j' p p' m : ℕ} (hjj : j' < j) (hj : j ≤ k) (t : Fin (s + s))
    (hm1 : s ≤ m) (hm2 : m + s < s * regSpan k j) :
    s * (p' * regSpan k j') + regOffset k s j' t ≠ s * (p * regSpan k j) + m := by
  intro h
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp at hm2
  set B := regSpan k j with hBdef
  have hB := two_le_regSpan hj
  obtain ⟨c, hc⟩ : ∃ c, regSpan k j' = (c + 1) * B := by
    refine ⟨2 ^ (j - j') - 1, ?_⟩
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, regSpan, hBdef, regSpan, ← pow_add]
    congr 1; omega
  have hdiv := congrArg (· / s) h
  simp only [Nat.mul_add_div hs] at hdiv
  have hms1 : 1 ≤ m / s := (Nat.le_div_iff_mul_le hs).2 (by omega)
  have hms2 : m / s < B - 1 := by
    rw [Nat.div_lt_iff_lt_mul hs]
    have : (B - 1) * s + s = s * B := by
      rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega
    omega
  have hrhs : (p * B + m / s) % B = m / s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show m / s < B by omega)]
  rw [← hdiv, hc] at hrhs
  unfold regOffset at hrhs
  rw [hc] at hrhs
  split_ifs at hrhs with ht
  · rw [Nat.div_eq_of_lt ht, Nat.add_zero, show p' * ((c + 1) * B) = p' * (c + 1) * B by ring,
      Nat.mul_mod_left] at hrhs
    omega
  · have hcB : 2 ≤ (c + 1) * B := le_trans hB (Nat.le_mul_of_pos_left _ (Nat.succ_pos c))
    have hq : (t.val + s * ((c + 1) * B - 2)) / s = (c + 1) * B - 1 := by
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have : ((c + 1) * B - 1) * s = s * ((c + 1) * B - 2) + s := by
          rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega
        omega
      · have : ((c + 1) * B - 1 + 1) * s = s * ((c + 1) * B - 2) + s + s := by
          rw [Nat.mul_comm, ← Nat.mul_succ, ← Nat.mul_succ]; congr 1; omega
        have := t.isLt
        omega
    have hsplit : p' * ((c + 1) * B) + ((c + 1) * B - 1) = (B - 1) + (p' * (c + 1) + c) * B := by
      have : (c + 1) * B - 1 = c * B + (B - 1) := by
        rw [Nat.succ_mul]; omega
      rw [this]; ring
    rw [hq, hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show B - 1 < B by omega)] at hrhs
    omega

variable (X hN) in
/-- The sites strictly between the two registers of the unitaries of depths `j, …, k`. -/
def regInteriorFrom (j : ℕ) : Set (Fin N) :=
  {x | ∃ j', j ≤ j' ∧ j' ≤ k ∧ ∃ g ∈ regLevelGates X hN j', x ∈ g.interior}

theorem regInteriorFrom_succ_subset (j : ℕ) :
    regInteriorFrom (k := k) X hN (j + 1) ⊆ regInteriorFrom X hN j :=
  fun _ ⟨j', hj', hjk, g, hg, hx⟩ => ⟨j', by omega, hjk, g, hg, hx⟩

theorem interior_subset_regInteriorFrom {j : ℕ} (hj : j ≤ k) {g : RegisterGate d N s}
    (hg : g ∈ regLevelGates X hN j) : g.interior ⊆ regInteriorFrom X hN j :=
  fun _ hx => ⟨j, le_rfl, hj, g, hg, hx⟩

/-- The registers of a unitary of depth `j' < j` are not strictly between the two registers of a
unitary of depth `j`. -/
theorem disjoint_range_sites_interior {j j' : ℕ} (hjj : j' < j) (hj : j ≤ k)
    {g' g : RegisterGate d N s} (hg' : g' ∈ regLevelGates X hN j')
    (hg : g ∈ regLevelGates X hN j) : Disjoint (Set.range g'.sites) g.interior := by
  obtain ⟨b', p', hp', rfl⟩ := mem_regLevelGates hg'
  obtain ⟨b, p, hp, rfl⟩ := mem_regLevelGates hg
  rw [regGate_sites (by omega) hp', Set.disjoint_left]
  rintro x ⟨t, rfl⟩ hx
  obtain ⟨m, hm, hm1, hm2, he⟩ := mem_interior_regGate hj hp hx
  have := ((blockSite_eq_iff hN).mp he).2
  rw [regWindow_val (by omega) hp'] at this
  exact regWindow_val_ne hjj hj t hm1 hm2 this

/-- The unitaries of depth `j` keep `|0⟩` strictly between the two registers of the unitaries of
the depths `j + 1, …, k`. -/
theorem isZeroOn_regInteriorFrom_mulVec [NeZero d] {j : ℕ} {v : Cfg d N → ℂ}
    (hv : IsZeroOn (regInteriorFrom X hN (j + 1)) v) :
    IsZeroOn (regInteriorFrom X hN (j + 1))
      (((regLevelGates X hN j).map RegisterGate.op).prod *ᵥ v) := by
  refine hv.mulVec_of_mem_supportedOperators
    (T := {x | ∃ g ∈ regLevelGates X hN j, x ∈ Set.range g.sites}) ?_
    (list_prod_mem_supportedOperators _ fun A hA => ?_)
  · rw [Set.disjoint_left]
    rintro x ⟨j', hj', hjk, g, hg, hx⟩ ⟨g', hg', hx'⟩
    exact Set.disjoint_left.mp (disjoint_range_sites_interior (by omega) hjk hg' hg) hx' hx
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hA
    refine supportedOperators_mono ?_ g.op_mem_supportedOperators
    exact fun x hx => ⟨g, hg, hx⟩

/-! ### The trees of all the blocks with measurements -/

variable (hN) in
/-- The sites of the blocks other than their first and their last `s` sites. -/
def regCentralSites : Set (Fin N) :=
  {x | ∃ b y, s ≤ y.val ∧ y.val + s < s * 2 ^ (k + 1) ∧ x = blockSite hN b y}

theorem regInteriorFrom_zero_subset :
    regInteriorFrom X hN 0 ⊆ regCentralSites (k := k) (s := s) hN := by
  rintro x ⟨j, -, hj, g, hg, hx⟩
  obtain ⟨b, p, hp, rfl⟩ := mem_regLevelGates hg
  obtain ⟨m, hm, hm1, hm2, rfl⟩ := mem_interior_regGate hj hp hx
  refine ⟨b, _, by simp only; omega, ?_, rfl⟩
  have := Nat.mul_le_mul_left s (succ_mul_regSpan_le hj hp)
  rw [Nat.succ_mul, Nat.mul_add] at this
  simp only
  omega

theorem exists_rounds_regTreeOp_aux [NeZero d] {K : ℕ}
    (hK : ∀ j p, IsPairProduct d (s + s) K (X j p)) :
    ∀ j ≤ k + 1, ∃ Rs : List (MeasurementRound d N),
      (Rs.map MeasurementRound.depth).sum = j * (4 * s + K + 2) ∧
      MeasurementRound.IsRoundsImplementationOn Rs
        {v : Cfg d N → ℂ | IsZeroOn (regInteriorFrom X hN 0) v}
        (blockLayerOp hN fun _ => regTreeOp X k j) ∧
      ∀ v : Cfg d N → ℂ, IsZeroOn (regInteriorFrom X hN 0) v →
        IsZeroOn (regInteriorFrom X hN j) ((blockLayerOp hN fun _ => regTreeOp X k j) *ᵥ v)
  | 0, _ => by
    refine ⟨[], by simp, ?_, fun v hv => ?_⟩
    · simpa [regTreeOp, blockLayerOp_one] using
        MeasurementRound.isRoundsImplementationOn_nil (d := d) (N := N)
          {v : Cfg d N → ℂ | IsZeroOn (regInteriorFrom X hN 0) v}
    · simpa [regTreeOp, blockLayerOp_one] using hv
  | j + 1, hj => by
    obtain ⟨Rs, hRs, hRsE, hRsZ⟩ := exists_rounds_regTreeOp_aux hK j (by omega)
    obtain ⟨Rs', hRs', hRs'E⟩ := RegisterGate.exists_rounds (pairwise_regLevelGates
      (X := X) (hN := hN) (show j ≤ k by omega)) (K := K) fun g hg => by
        obtain ⟨b, p, -, rfl⟩ := mem_regLevelGates hg
        exact hK j p
    have hop : (blockLayerOp hN fun _ => regTreeOp X k (j + 1)) =
        ((regLevelGates X hN j).map RegisterGate.op).prod *
          blockLayerOp hN fun _ => regTreeOp X k j := by
      rw [list_prod_map_op_regLevelGates (by omega), ← blockLayerOp_mul]
      rfl
    refine ⟨Rs ++ Rs', ?_, ?_, fun v hv => ?_⟩
    · rw [List.map_append, List.sum_append, hRs, hRs']; ring
    · rw [hop]
      refine hRsE.append (hRs'E.mono (E' := {v | IsZeroOn (regInteriorFrom X hN j) v})
        fun v hv g hg => ?_) fun v hv => hRsZ v hv
      exact (show IsZeroOn (regInteriorFrom X hN j) v from hv).mono
        (interior_subset_regInteriorFrom (by omega) hg)
    · rw [hop, ← mulVec_mulVec]
      exact isZeroOn_regInteriorFrom_mulVec ((hRsZ v hv).mono (regInteriorFrom_succ_subset j))

/-- **The trees of all the blocks in depth `(k + 1)(4s + K + 2)` with measurements.** Let the
ring of `N` sites be cut into `M` blocks of `s 2^{k+1}` sites, and let every unitary `X j p` of
the trees be a product of at most `K` gates on neighbouring sites. Some sequence of measurement
rounds of total depth `(k + 1)(4s + K + 2)` implements the trees of all the blocks, `⊗ₖ T` with
`T = regTreeOp X k (k + 1)`, on the vectors with `|0⟩` at every site of every block other than
its first and its last `s` sites: whatever the outcomes, every output is a scalar multiple of
`(⊗ₖ T) v`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("every isometry in
eq. (16) takes constant time using measurement"). -/
theorem exists_rounds_blockLayerOp_regTreeOp [NeZero d] {K : ℕ}
    (hK : ∀ j p, IsPairProduct d (s + s) K (X j p)) :
    ∃ Rs : List (MeasurementRound d N),
      (Rs.map MeasurementRound.depth).sum = (k + 1) * (4 * s + K + 2) ∧
      MeasurementRound.IsRoundsImplementationOn Rs
        {v : Cfg d N → ℂ | IsZeroOn (regCentralSites (k := k) (s := s) hN) v}
        (blockLayerOp hN fun _ => regTreeOp X k (k + 1)) := by
  obtain ⟨Rs, hRs, hRsE, -⟩ := exists_rounds_regTreeOp_aux (X := X) (hN := hN) hK (k + 1) le_rfl
  exact ⟨Rs, hRs, hRsE.mono fun v hv => (show IsZeroOn _ v from hv).mono
    (regInteriorFrom_zero_subset (X := X))⟩

end Tree

end MPSPreparation
