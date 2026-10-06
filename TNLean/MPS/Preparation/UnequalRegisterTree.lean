/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RegisterTree

/-!
# Trees of register gates on blocks of any length

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies to every block a binary tree of
isometries, and the paragraph "Tree-RG circuit with measurements" applies each level of the tree
in constant depth by teleportation. `TNLean.MPS.Preparation.RegisterTree` places such trees on
blocks of `s 2^{k+1}` sites, cut into registers of `s` sites. The Supplemental Material, proof of
Theorem 1, cuts a chain whose length is not a multiple of the block length into blocks "all of
the same size, `q_N`, except for the last one, which may be larger". This file places trees on
blocks of any length.

## The tree of a block

A block of `n` sites is cut into `2^{h+1}` consecutive *leaves* of even widths `w 0, w 1, …`,
each at least `2s`; the sites of the block after them belong to the last leaf
(`MPSPreparation.IsTreeLayout`). The node `p` of depth `j ≤ h + 1` covers the leaves
`p 2^{h+1-j}, …, (p + 1) 2^{h+1-j} - 1`; its two registers are its first `s` sites and the last
`s` sites of its last leaf, not counting the remainder (`MPSPreparation.nodeWindow`). The
registers of a node are the first register of its first half and the last register of its second
half, so a unitary of depth `j` writes the registers on which the two unitaries below it act, as
in the tree of equal halves. The widths need not be equal: the halves of a node may have
different lengths.

The depths `0, …, h` carry unitaries `X j p` on the two registers of their nodes
(`MPSPreparation.treeLevelOp`); the leaves carry unitaries on all their sites
(`MPSPreparation.treeLeafOp`).

## Measurements

The widths are even, so the two registers of a node are `2L` sites apart for some `L`, and the
unitary of a node is a register gate (`MPSPreparation.treeRegGate`). As for the trees of equal
blocks, the registers of the coarser depths are not strictly between the two registers of a
finer node, so the depths `0, …, h` of the trees of all the blocks of a ring are applied one
after the other, each in depth `4s + K + 2`
(`MPSPreparation.exists_rounds_blockLayerOp_treeLevelsOp`),
and the leaves of all the blocks by one local circuit
(`MPSPreparation.isCircuitOn_blockLayerOp_treeLeafOp`).

## Main definitions

* `MPSPreparation.registerLayersOp` — the product of a sequence of layers of register gates.
* `MPSPreparation.IsTreeLayout`, `MPSPreparation.nodeWindow`, `MPSPreparation.leafWindow`.
* `MPSPreparation.treeLevelOp`, `MPSPreparation.treeLevelsOp`, `MPSPreparation.treeLeafOp`.
* `MPSPreparation.treeRegGate`, `MPSPreparation.treeLevelGates`.

## Main results

* `MPSPreparation.exists_rounds_registerLayersOp` — layers of register gates, applied one after
  the other with measurements.
* `MPSPreparation.exists_rounds_blockLayerOp_treeLevelsOp`.
* `MPSPreparation.isCircuitOn_blockLayerOp_treeLeafOp`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16), the paragraph "Tree-RG circuit with
  measurements", and Supplemental Material, proof of Theorem 1.
-/

open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

open Fin.NatCast

/-! ### Layers of register gates applied one after the other -/

section Layers

variable {d N s : ℕ} [NeZero N]

/-- The product of the layers `gs 0, …, gs (m - 1)` of register gates, the layer `gs 0` applied
first. -/
noncomputable def registerLayersOp (gs : ℕ → List (RegisterGate d N s)) :
    ℕ → Matrix (Cfg d N) (Cfg d N) ℂ
  | 0 => 1
  | j + 1 => ((gs j).map RegisterGate.op).prod * registerLayersOp gs j

/-- **Layers of register gates with measurements.** Let `gs 0, …, gs (m - 1)` be layers of
register gates, the gates of each layer on pairwise disjoint stretches, such that no register of
a gate of a layer is strictly between the two registers of a gate of a later layer. If every
gate is a product of at most `K` gates on neighbouring sites, some sequence of measurement rounds
of total depth `m (4s + K + 2)` implements the product of the layers on the vectors with `|0⟩`
strictly between the two registers of every gate.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("every isometry in
eq. (16) takes constant time using measurement"), one level of the tree after the other. -/
theorem exists_rounds_registerLayersOp [NeZero d] [NeZero s] {K : ℕ}
    (gs : ℕ → List (RegisterGate d N s)) (m : ℕ)
    (hdisj : ∀ j < m, (gs j).Pairwise fun g g' => Disjoint g.span g'.span)
    (hreg : ∀ j' j, j' < j → j < m → ∀ g' ∈ gs j', ∀ g ∈ gs j,
      Disjoint (Set.range g'.sites) g.interior)
    (hK : ∀ j < m, ∀ g ∈ gs j, IsPairProduct d (s + s) K g.X) :
    ∃ Rs : List (MeasurementRound d N),
      (Rs.map MeasurementRound.depth).sum = m * (4 * s + K + 2) ∧
      MeasurementRound.IsRoundsImplementationOn Rs
        {v | ∀ j < m, ∀ g ∈ gs j, IsZeroOn g.interior v} (registerLayersOp gs m) := by
  set E := {v : Cfg d N → ℂ | ∀ j < m, ∀ g ∈ gs j, IsZeroOn g.interior v}
  suffices aux : ∀ j ≤ m, ∃ Rs : List (MeasurementRound d N),
      (Rs.map MeasurementRound.depth).sum = j * (4 * s + K + 2) ∧
      MeasurementRound.IsRoundsImplementationOn Rs E (registerLayersOp gs j) ∧
      ∀ v ∈ E, ∀ j', j ≤ j' → j' < m → ∀ g ∈ gs j',
        IsZeroOn g.interior (registerLayersOp gs j *ᵥ v) by
    obtain ⟨Rs, h1, h2, -⟩ := aux m le_rfl
    exact ⟨Rs, h1, h2⟩
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨[], by simp, ?_, fun v hv j' _ hj' g hg => ?_⟩
    · simpa [registerLayersOp] using
        MeasurementRound.isRoundsImplementationOn_nil (d := d) (N := N) E
    · simpa [registerLayersOp] using hv j' hj' g hg
  | succ j ih =>
    intro hj
    obtain ⟨Rs, hRs, hRsE, hRsZ⟩ := ih (by omega)
    obtain ⟨Rs', hRs', hRs'E⟩ := RegisterGate.exists_rounds (hdisj j (by omega)) (K := K)
      (hK j (by omega))
    refine ⟨Rs ++ Rs', ?_, ?_, fun v hv j' hj' hj'm g hg => ?_⟩
    · rw [List.map_append, List.sum_append, hRs, hRs']; ring
    · exact hRsE.append hRs'E fun v hv g hg => hRsZ v hv j le_rfl (by omega) g hg
    · rw [registerLayersOp, ← mulVec_mulVec]
      refine (hRsZ v hv j' (by omega) hj'm g hg).mulVec_of_mem_supportedOperators
        (T := {x | ∃ g' ∈ gs j, x ∈ Set.range g'.sites}) ?_
        (list_prod_mem_supportedOperators _ fun A hA => ?_)
      · rw [Set.disjoint_left]
        rintro x hx ⟨g', hg', hx'⟩
        exact Set.disjoint_left.mp (hreg j j' (by omega) hj'm g' hg' g hg) hx' hx
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hA
        exact supportedOperators_mono (S' := {x | ∃ g' ∈ gs j, x ∈ Set.range g'.sites})
          (fun x hx => ⟨g', hg', hx⟩) g'.op_mem_supportedOperators

end Layers

/-! ### Leaves and nodes -/

section Layout

/-- The first site `w 0 + ⋯ + w (m - 1)` of the leaf `m`. -/
def leafOffset (w : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, w i

variable {h s n : ℕ} {w : ℕ → ℕ}

theorem leafOffset_succ (m : ℕ) : leafOffset w (m + 1) = leafOffset w m + w m :=
  Finset.sum_range_succ _ _

theorem leafOffset_mono {m m' : ℕ} (h : m ≤ m') : leafOffset w m ≤ leafOffset w m' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem leafOffset_add_le {c m m' : ℕ} (hmm : m < m') (hw : c ≤ w m) :
    leafOffset w m + c ≤ leafOffset w m' :=
  calc leafOffset w m + c ≤ leafOffset w m + w m := by omega
    _ = leafOffset w (m + 1) := (leafOffset_succ m).symm
    _ ≤ leafOffset w m' := leafOffset_mono hmm

theorem even_leafOffset_sub {m m' : ℕ} (hmm : m ≤ m')
    (he : ∀ i, m ≤ i → i < m' → Even (w i)) : Even (leafOffset w m' - leafOffset w m) := by
  induction m', hmm using Nat.le_induction with
  | base => simp
  | succ m' hmm ih =>
    have := leafOffset_mono (w := w) hmm
    rw [leafOffset_succ, show leafOffset w m' + w m' - leafOffset w m =
      (leafOffset w m' - leafOffset w m) + w m' by omega]
    exact (ih fun i h1 h2 => he i h1 (by omega)).add (he m' hmm (by omega))

/-- **The tree layout of a block** of `n` sites: `2^{h+1}` leaves of even widths `w i ≥ 2s`,
whose total is at most `n`; the sites after them belong to the last leaf.

arXiv:2307.01696, eq. (16), with the leaves of unequal lengths that a block "which may be
larger" (Supplemental Material, proof of Theorem 1) requires. -/
structure IsTreeLayout (h s n : ℕ) (w : ℕ → ℕ) : Prop where
  two_mul_le : ∀ i < 2 ^ (h + 1), s + s ≤ w i
  even : ∀ i < 2 ^ (h + 1), Even (w i)
  le : leafOffset w (2 ^ (h + 1)) ≤ n

theorem IsTreeLayout.pos [NeZero s] (hT : IsTreeLayout h s n w) : 0 < n := by
  have := leafOffset_add_le (w := w) (Nat.two_pow_pos (h + 1)) (hT.two_mul_le 0
    (Nat.two_pow_pos _))
  have hs := NeZero.pos s
  have := hT.le
  omega

variable (h) in
/-- The number `2^{h+1-j}` of leaves of a node of depth `j`. -/
def nodeLeaves (j : ℕ) : ℕ := 2 ^ (h + 1 - j)

variable (h w) in
/-- The first site of the node `p` of depth `j`. -/
def nodeStart (j p : ℕ) : ℕ := leafOffset w (p * nodeLeaves h j)

variable (h w) in
/-- The site after the last leaf of the node `p` of depth `j`, not counting the remainder. -/
def nodeStop (j p : ℕ) : ℕ := leafOffset w ((p + 1) * nodeLeaves h j)

theorem nodeLeaves_pos (j : ℕ) : 0 < nodeLeaves h j := Nat.two_pow_pos _

theorem nodeLeaves_eq_two_mul {j : ℕ} (hj : j ≤ h) : nodeLeaves h j = 2 * nodeLeaves h (j + 1) := by
  rw [nodeLeaves, nodeLeaves, show h + 1 - j = (h + 1 - (j + 1)) + 1 by omega, pow_succ]
  ring

theorem succ_mul_nodeLeaves_le {j p : ℕ} (hj : j ≤ h + 1) (hp : p < 2 ^ j) :
    (p + 1) * nodeLeaves h j ≤ 2 ^ (h + 1) := by
  calc (p + 1) * nodeLeaves h j ≤ 2 ^ j * nodeLeaves h j := Nat.mul_le_mul_right _ hp
    _ = 2 ^ (h + 1) := by rw [nodeLeaves, ← pow_add]; congr 1; omega

theorem nodeStart_add_le (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1)
    (hp : p < 2 ^ j) : nodeStart h w j p + (s + s) ≤ nodeStop h w j p := by
  have h1 := succ_mul_nodeLeaves_le hj hp
  have h2 := nodeLeaves_pos (h := h) j
  refine leafOffset_add_le (by nlinarith) (hT.two_mul_le _ (by nlinarith))

theorem nodeStop_le {j p : ℕ} (hj : j ≤ h + 1) (hp : p < 2 ^ j) :
    nodeStop h w j p ≤ leafOffset w (2 ^ (h + 1)) :=
  leafOffset_mono (succ_mul_nodeLeaves_le hj hp)

theorem nodeStop_le_n (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1) (hp : p < 2 ^ j) :
    nodeStop h w j p ≤ n :=
  (nodeStop_le hj hp).trans hT.le

theorem even_nodeStop_sub (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1)
    (hp : p < 2 ^ j) : Even (nodeStop h w j p - nodeStart h w j p) := by
  have h1 := succ_mul_nodeLeaves_le hj hp
  exact even_leafOffset_sub (by nlinarith) fun i _ hi => hT.even i (by omega)

theorem nodeStop_le_nodeStart {j p p' : ℕ} (hpp : p < p') :
    nodeStop h w j p ≤ nodeStart h w j p' :=
  leafOffset_mono (Nat.mul_le_mul_right _ hpp)

theorem nodeStart_two_mul {j : ℕ} (hj : j ≤ h) (p : ℕ) :
    nodeStart h w (j + 1) (2 * p) = nodeStart h w j p := by
  rw [nodeStart, nodeStart, nodeLeaves_eq_two_mul hj]; ring_nf

theorem nodeStop_two_mul_add_one {j : ℕ} (hj : j ≤ h) (p : ℕ) :
    nodeStop h w (j + 1) (2 * p + 1) = nodeStop h w j p := by
  rw [nodeStop, nodeStop, nodeLeaves_eq_two_mul hj]; ring_nf

theorem nodeStop_two_mul (j p : ℕ) :
    nodeStop h w (j + 1) (2 * p) = nodeStart h w (j + 1) (2 * p + 1) := rfl

/-- The offset in the block of the site `t` of the two registers of the node `p` of depth `j`:
the first `s` sites of the node, then the last `s` sites of its last leaf. -/
def nodeOffset (s h : ℕ) (w : ℕ → ℕ) (j p : ℕ) (t : Fin (s + s)) : ℕ :=
  if t.val < s then nodeStart h w j p + t.val else nodeStop h w j p - (s + s) + t.val

theorem nodeOffset_lt (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1) (hp : p < 2 ^ j)
    (t : Fin (s + s)) : nodeOffset s h w j p t < nodeStop h w j p := by
  have := nodeStart_add_le hT hj hp
  have := t.isLt
  unfold nodeOffset; split_ifs <;> omega

theorem nodeStart_le_nodeOffset (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1)
    (hp : p < 2 ^ j) (t : Fin (s + s)) : nodeStart h w j p ≤ nodeOffset s h w j p t := by
  have := nodeStart_add_le hT hj hp
  unfold nodeOffset; split_ifs <;> omega

/-- The registers of a node of depth `j'` are registers of nodes of every finer depth `j`, with
the same index `t`. -/
theorem exists_nodeOffset_eq {j' j p' : ℕ} (hjj : j' ≤ j) (hj : j ≤ h + 1) (hp' : p' < 2 ^ j')
    (t : Fin (s + s)) : ∃ m < 2 ^ j, nodeOffset s h w j' p' t = nodeOffset s h w j m t := by
  have hB : nodeLeaves h j' = 2 ^ (j - j') * nodeLeaves h j := by
    rw [nodeLeaves, nodeLeaves, ← pow_add]; congr 1; omega
  have hpow : 2 ^ j = 2 ^ j' * 2 ^ (j - j') := by rw [← pow_add]; congr 1; omega
  have hc := Nat.two_pow_pos (j - j')
  by_cases ht : t.val < s
  · refine ⟨p' * 2 ^ (j - j'), ?_, ?_⟩
    · rw [hpow]; exact Nat.mul_lt_mul_of_pos_right hp' hc
    · simp only [nodeOffset, ht, ↓reduceIte, nodeStart, hB]
      ring_nf
  · refine ⟨(p' + 1) * 2 ^ (j - j') - 1, ?_, ?_⟩
    · have : (p' + 1) * 2 ^ (j - j') ≤ 2 ^ j := by
        rw [hpow]; exact Nat.mul_le_mul_right _ hp'
      exact lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) this
    · have h1 : (p' + 1) * 2 ^ (j - j') - 1 + 1 = (p' + 1) * 2 ^ (j - j') := by
        have : 1 ≤ (p' + 1) * 2 ^ (j - j') := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      simp only [nodeOffset, ht, ↓reduceIte, nodeStop, h1, hB]
      ring_nf

/-- A register of a node of depth `j` is not strictly between the two registers of a node of
the same depth. -/
theorem nodeOffset_notMem_interior (hT : IsTreeLayout h s n w) {j m p : ℕ} (hj : j ≤ h + 1)
    (hm : m < 2 ^ j) (hp : p < 2 ^ j) (t : Fin (s + s)) :
    nodeOffset s h w j m t < nodeStart h w j p + s ∨
      nodeStop h w j p ≤ nodeOffset s h w j m t + s := by
  have hm' := nodeStart_add_le hT hj hm
  have hp' := nodeStart_add_le hT hj hp
  have := t.isLt
  rcases lt_trichotomy m p with hmp | rfl | hmp
  · have := nodeStop_le_nodeStart (h := h) (w := w) (j := j) hmp
    have := nodeOffset_lt hT hj hm t
    omega
  · unfold nodeOffset; split_ifs <;> omega
  · have := nodeStop_le_nodeStart (h := h) (w := w) (j := j) hmp
    unfold nodeOffset; split_ifs <;> omega

/-! ### Windows in a block -/

variable [NeZero s]

/-- The two registers of the node `p` of depth `j`, as sites of the block.

Source: arXiv:2307.01696, eq. (16) (the isometries of the tree). -/
def nodeWindow (hT : IsTreeLayout h s n w) (j p : ℕ) (t : Fin (s + s)) : Fin n :=
  ⟨nodeOffset s h w j p t % n, Nat.mod_lt _ hT.pos⟩

theorem nodeWindow_val (hT : IsTreeLayout h s n w) {j p : ℕ} (hj : j ≤ h + 1) (hp : p < 2 ^ j)
    (t : Fin (s + s)) : (nodeWindow hT j p t).val = nodeOffset s h w j p t :=
  Nat.mod_eq_of_lt ((nodeOffset_lt hT hj hp t).trans_le (nodeStop_le_n hT hj hp))

theorem nodeWindow_injective₂ (hT : IsTreeLayout h s n w) {j : ℕ} (hj : j ≤ h + 1) :
    Function.Injective fun pt : Fin (2 ^ j) × Fin (s + s) => nodeWindow hT j pt.1 pt.2 := by
  rintro ⟨p, t⟩ ⟨p', t'⟩ he
  simp only at he
  have he' := congrArg Fin.val he
  simp only [nodeWindow_val hT hj p.isLt, nodeWindow_val hT hj p'.isLt] at he'
  have hp := nodeStart_add_le hT hj p.isLt
  have hp' := nodeStart_add_le hT hj p'.isLt
  have h1 := nodeOffset_lt hT hj p.isLt t
  have h2 := nodeOffset_lt hT hj p'.isLt t'
  have h3 := nodeStart_le_nodeOffset hT hj p.isLt t
  have h4 := nodeStart_le_nodeOffset hT hj p'.isLt t'
  have hpp : p = p' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have := nodeStop_le_nodeStart (h := h) (w := w) (j := j) hlt; omega
    · have := nodeStop_le_nodeStart (h := h) (w := w) (j := j) hlt; omega
  subst hpp
  refine Prod.ext rfl (Fin.ext ?_)
  change t.val = t'.val
  have := t.isLt; have := t'.isLt
  unfold nodeOffset at he'
  split_ifs at he' <;> omega

variable (h n w) in
/-- The number of sites of the node `p` of depth `j`: its leaves, and for the last node also the
sites after the leaves. -/
def nodeLen (j p : ℕ) : ℕ := (if p + 1 = 2 ^ j then n else nodeStop h w j p) - nodeStart h w j p

variable (h n w) in
/-- The number of sites of the leaf `p`: its width, and for the last leaf also the sites after
the leaves. -/
def leafLen (p : ℕ) : ℕ := nodeLen h n w (h + 1) p

theorem leafLen_eq (p : ℕ) :
    leafLen h n w p = if p + 1 = 2 ^ (h + 1) then n - leafOffset w p else w p := by
  simp only [leafLen, nodeLen, nodeStart, nodeStop, nodeLeaves, Nat.sub_self, pow_zero, mul_one,
    leafOffset_succ]
  split_ifs <;> omega

omit [NeZero s] in
theorem leafOffset_add_leafLen (hT : IsTreeLayout h s n w) {p : ℕ} (hp : p < 2 ^ (h + 1)) :
    leafOffset w p + leafLen h n w p ≤ n := by
  have := leafOffset_mono (w := w) (show p + 1 ≤ 2 ^ (h + 1) by omega)
  have := hT.le
  rw [leafLen_eq, leafOffset_succ] at *
  split_ifs <;> omega

omit [NeZero s] in
theorem two_mul_le_leafLen (hT : IsTreeLayout h s n w) {p : ℕ} (hp : p < 2 ^ (h + 1)) :
    s + s ≤ leafLen h n w p := by
  have := leafOffset_mono (w := w) (show p + 1 ≤ 2 ^ (h + 1) by omega)
  have := hT.le
  have := hT.two_mul_le p hp
  rw [leafLen_eq, leafOffset_succ] at *
  split_ifs <;> omega

/-- The sites of the leaf `p` of the block. -/
def leafWindow (hT : IsTreeLayout h s n w) (p : ℕ) (i : Fin (leafLen h n w p)) : Fin n :=
  ⟨(leafOffset w p + i.val) % n, Nat.mod_lt _ hT.pos⟩

theorem leafWindow_val (hT : IsTreeLayout h s n w) {p : ℕ} (hp : p < 2 ^ (h + 1))
    (i : Fin (leafLen h n w p)) : (leafWindow hT p i).val = leafOffset w p + i.val :=
  Nat.mod_eq_of_lt (by have := leafOffset_add_leafLen hT hp; have := i.isLt; omega)

theorem leafWindow_injective (hT : IsTreeLayout h s n w) {p : ℕ} (hp : p < 2 ^ (h + 1)) :
    Function.Injective (leafWindow hT p) := fun i i' he => Fin.ext (by
  have := congrArg Fin.val he
  rw [leafWindow_val hT hp, leafWindow_val hT hp] at this
  omega)

/-- The leaves of a block are pairwise disjoint. -/
theorem disjoint_range_leafWindow (hT : IsTreeLayout h s n w) {p p' : ℕ}
    (hp : p < 2 ^ (h + 1)) (hp' : p' < 2 ^ (h + 1)) (hne : p ≠ p') :
    Disjoint (Set.range (leafWindow hT p)) (Set.range (leafWindow hT p')) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨i', he⟩
  have he' := congrArg Fin.val he
  rw [leafWindow_val hT hp, leafWindow_val hT hp'] at he'
  have hi := i.isLt
  have hi' := i'.isLt
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := leafOffset_mono (w := w) (show p + 1 ≤ p' by omega)
    have h2 : leafLen h n w p = w p := by rw [leafLen_eq]; split_ifs <;> omega
    rw [leafOffset_succ] at h1
    omega
  · have h1 := leafOffset_mono (w := w) (show p' + 1 ≤ p by omega)
    have h2 : leafLen h n w p' = w p' := by rw [leafLen_eq]; split_ifs <;> omega
    rw [leafOffset_succ] at h1
    omega

/-- Every site of the block lies in a leaf. -/
theorem exists_leafWindow_eq (hT : IsTreeLayout h s n w) (y : Fin n) :
    ∃ p < 2 ^ (h + 1), ∃ i, leafWindow hT p i = y := by
  -- the last leaf whose first site is at most `y`
  have hex : ∃ p, p < 2 ^ (h + 1) ∧ leafOffset w p ≤ y.val := ⟨0, Nat.two_pow_pos _, by
    simp [leafOffset]⟩
  classical
  let P := Nat.findGreatest (fun p => p < 2 ^ (h + 1) ∧ leafOffset w p ≤ y.val) (2 ^ (h + 1))
  obtain ⟨p, hp, hpy⟩ := hex
  have hP : P < 2 ^ (h + 1) ∧ leafOffset w P ≤ y.val :=
    Nat.findGreatest_spec (P := fun p => p < 2 ^ (h + 1) ∧ leafOffset w p ≤ y.val) hp.le ⟨hp, hpy⟩
  refine ⟨P, hP.1, ⟨y.val - leafOffset w P, ?_⟩, Fin.ext ?_⟩
  · by_cases hlast : P + 1 = 2 ^ (h + 1)
    · rw [leafLen_eq]; simp only [hlast, ↓reduceIte]; omega
    · rw [leafLen_eq]; simp only [hlast, ↓reduceIte]
      have hnext : ¬ (P + 1 < 2 ^ (h + 1) ∧ leafOffset w (P + 1) ≤ y.val) :=
        Nat.findGreatest_is_greatest (Nat.lt_succ_self P) (by omega)
      have : y.val < leafOffset w (P + 1) := by
        by_contra hc; exact hnext ⟨by omega, by omega⟩
      rw [leafOffset_succ] at this
      omega
  · rw [leafWindow_val hT hP.1]
    change leafOffset w P + (y.val - leafOffset w P) = y.val
    omega

/-- Consecutive sites of a leaf are consecutive sites of the block. -/
theorem leafWindow_succ (hT : IsTreeLayout h s n w) {p : ℕ} (hp : p < 2 ^ (h + 1))
    (i i' : Fin (leafLen h n w p)) (hi : i'.val = i.val + 1) :
    (leafWindow hT p i').val = (leafWindow hT p i).val + 1 := by
  rw [leafWindow_val hT hp, leafWindow_val hT hp, hi, Nat.add_assoc]

end Layout

/-! ### The operators of a block -/

section BlockOps

variable {d h s n : ℕ} [NeZero s] {w : ℕ → ℕ} (hT : IsTreeLayout h s n w)

/-- The unitaries of the nodes of depth `j` of the tree of a block.

Source: arXiv:2307.01696, eq. (16) (the layer `(V⁽ʲ⁾)^{⊗ ⋯}` of the tree). -/
noncomputable def treeLevelOp (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) (j : ℕ) :
    Matrix (Cfg d n) (Cfg d n) ℂ :=
  ((List.finRange (2 ^ j)).map fun p : Fin (2 ^ j) => embedOp (nodeWindow hT j p) (X j p)).prod

/-- The depths `j, …, j + m - 1` of the tree of a block, the depth `j` applied first. -/
noncomputable def treeLevelsOp (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) (j : ℕ) :
    ℕ → Matrix (Cfg d n) (Cfg d n) ℂ
  | 0 => 1
  | m + 1 => treeLevelOp hT X (j + m) * treeLevelsOp X j m

/-- The unitaries of the leaves of the tree of a block. -/
noncomputable def treeLeafOp
    (U : ∀ p : Fin (2 ^ (h + 1)), Matrix (Cfg d (leafLen h n w p)) (Cfg d (leafLen h n w p)) ℂ) :
    Matrix (Cfg d n) (Cfg d n) ℂ :=
  ((List.finRange (2 ^ (h + 1))).map fun p : Fin (2 ^ (h + 1)) =>
    embedOp (leafWindow hT p) (U p)).prod

theorem treeLevelsOp_succ' (X : ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ) (j : ℕ) :
    ∀ m, treeLevelsOp hT X j (m + 1) = treeLevelsOp hT X (j + 1) m * treeLevelOp hT X j
  | 0 => by simp [treeLevelsOp]
  | m + 1 => by
    rw [treeLevelsOp, treeLevelsOp_succ' X j m, treeLevelsOp, Matrix.mul_assoc,
      show j + (m + 1) = j + 1 + m by omega]

end BlockOps

/-! ### The trees of all the blocks of a ring -/

section Ring

variable {d h s M N : ℕ} [NeZero s] [NeZero N] {ℓ : Fin M → ℕ} (hN : ∑ b, ℓ b = N)
  {w : Fin M → ℕ → ℕ} (hT : ∀ b, IsTreeLayout h s (ℓ b) (w b))
  (X : Fin M → ℕ → ℕ → Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ)

/-- The unitary of the node `p` of depth `j` of the block `b`, as a register gate on the ring.

Source: arXiv:2307.01696, eq. (16) and paragraph "Tree-RG circuit with measurements". -/
def treeRegGate (j : ℕ) (b : Fin M) (p : ℕ) (hj : j ≤ h) (hp : p < 2 ^ j) : RegisterGate d N s where
  a := blockSite hN b ⟨nodeStart h (w b) j p, by
    have := nodeStart_add_le (hT b) (by omega) hp
    have := nodeStop_le_n (hT b) (by omega) hp
    have := NeZero.pos s
    omega⟩
  L := (nodeStop h (w b) j p - nodeStart h (w b) j p - (s + s)) / 2
  le := by
    have := nodeStart_add_le (hT b) (by omega) hp
    have := nodeStop_le_n (hT b) (by omega) hp
    have : ℓ b ≤ N := hN ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    omega
  X := X b j p

variable {hN hT X}

theorem two_mul_treeRegGate_L {j : ℕ} (b : Fin M) {p : ℕ} (hj : j ≤ h) (hp : p < 2 ^ j) :
    2 * (treeRegGate hN hT X j b p hj hp).L + (s + s) =
      nodeStop h (w b) j p - nodeStart h (w b) j p := by
  have := nodeStart_add_le (hT b) (by omega) hp
  obtain ⟨c, hc⟩ := even_nodeStop_sub (hT b) (by omega : j ≤ h + 1) hp
  change 2 * ((nodeStop h (w b) j p - nodeStart h (w b) j p - (s + s)) / 2) + (s + s) = _
  omega

theorem treeRegGate_a_add {j : ℕ} (b : Fin M) {p : ℕ} (hj : j ≤ h) (hp : p < 2 ^ j) {m : ℕ}
    (hm : m < nodeStop h (w b) j p - nodeStart h (w b) j p) :
    (treeRegGate hN hT X j b p hj hp).a + (m : Fin N) =
      blockSite hN b ⟨nodeStart h (w b) j p + m, by
        have := nodeStop_le_n (hT b) (by omega) hp; omega⟩ :=
  blockSite_add_natCast hN b _ m _

/-- The registers of a gate are the window of its node. -/
theorem treeRegGate_sites {j : ℕ} (b : Fin M) {p : ℕ} (hj : j ≤ h) (hp : p < 2 ^ j) :
    (treeRegGate hN hT X j b p hj hp).sites = blockSite hN b ∘ nodeWindow (hT b) j p := by
  funext t
  have hL := two_mul_treeRegGate_L (hN := hN) (hT := hT) (X := X) b hj hp
  have hlt := nodeOffset_lt (hT b) (by omega : j ≤ h + 1) hp t
  have hle := nodeStart_le_nodeOffset (hT b) (by omega : j ≤ h + 1) hp t
  have hoff : (treeRegGate hN hT X j b p hj hp).offset t =
      nodeOffset s h (w b) j p t - nodeStart h (w b) j p := by
    have := t.isLt
    simp only [RegisterGate.offset, nodeOffset]
    split_ifs <;> omega
  rw [RegisterGate.sites, hoff, treeRegGate_a_add b hj hp (by omega), Function.comp_apply]
  congr 1
  exact Fin.ext (by rw [nodeWindow_val (hT b) (by omega) hp]; simp only; omega)

theorem mem_span_treeRegGate {j : ℕ} {b : Fin M} {p : ℕ} (hj : j ≤ h) (hp : p < 2 ^ j)
    {x : Fin N} (hx : x ∈ (treeRegGate hN hT X j b p hj hp).span) :
    ∃ m, ∃ hm : m < nodeStop h (w b) j p - nodeStart h (w b) j p,
      x = blockSite hN b ⟨nodeStart h (w b) j p + m, by
        have := nodeStop_le_n (hT b) (by omega) hp; omega⟩ := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hL := two_mul_treeRegGate_L (hN := hN) (hT := hT) (X := X) b hj hp
  exact ⟨m, by omega, treeRegGate_a_add b hj hp (by omega)⟩

theorem mem_interior_treeRegGate {j : ℕ} {b : Fin M} {p : ℕ} (hj : j ≤ h) (hp : p < 2 ^ j)
    {x : Fin N} (hx : x ∈ (treeRegGate hN hT X j b p hj hp).interior) :
    ∃ m, ∃ hm : m < nodeStop h (w b) j p - nodeStart h (w b) j p, s ≤ m ∧
      nodeStart h (w b) j p + m + s < nodeStop h (w b) j p ∧
      x = blockSite hN b ⟨nodeStart h (w b) j p + m, by
        have := nodeStop_le_n (hT b) (by omega) hp; omega⟩ := by
  obtain ⟨m, hm1, hm2, rfl⟩ := hx
  have hL := two_mul_treeRegGate_L (hN := hN) (hT := hT) (X := X) b hj hp
  have := nodeStart_add_le (hT b) (by omega : j ≤ h + 1) hp
  exact ⟨m, by omega, hm1, by omega, treeRegGate_a_add b hj hp (by omega)⟩

variable (hN hT X) in
/-- The register gates of depth `j` of the trees of all the blocks (none beyond the depth `h`). -/
def treeLevelGates (j : ℕ) : List (RegisterGate d N s) :=
  if hj : j ≤ h then
    (List.finRange M).flatMap fun b =>
      (List.finRange (2 ^ j)).map fun p : Fin (2 ^ j) => treeRegGate hN hT X j b p hj p.isLt
  else []

theorem mem_treeLevelGates {j : ℕ} {g : RegisterGate d N s} (hg : g ∈ treeLevelGates hN hT X j) :
    ∃ hj : j ≤ h, ∃ b : Fin M, ∃ p : Fin (2 ^ j), g = treeRegGate hN hT X j b p hj p.isLt := by
  unfold treeLevelGates at hg
  split_ifs at hg with hj
  · obtain ⟨b, -, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
    exact ⟨hj, b, p, rfl⟩
  · simp at hg

/-- The gates of depth `j` lie on pairwise disjoint stretches. -/
theorem pairwise_treeLevelGates (j : ℕ) :
    (treeLevelGates hN hT X j).Pairwise fun g g' => Disjoint g.span g'.span := by
  unfold treeLevelGates
  split_ifs with hj
  · have key : ∀ (b b' : Fin M) (p p' : Fin (2 ^ j)), (b ≠ b' ∨ p ≠ p') →
        Disjoint (treeRegGate hN hT X j b p hj p.isLt).span
          (treeRegGate hN hT X j b' p' hj p'.isLt).span := by
      intro b b' p p' hne
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨m, hm, rfl⟩ := mem_span_treeRegGate hj p.isLt hx
      obtain ⟨m', hm', he⟩ := mem_span_treeRegGate hj p'.isLt hx'
      obtain ⟨rfl, he'⟩ := (blockSite_eq_iff hN).mp he
      simp only at he'
      rcases hne with hne | hne
      · exact hne rfl
      · rcases Nat.lt_or_gt_of_ne (fun h' => hne (Fin.ext h')) with hlt | hlt
        · have := nodeStop_le_nodeStart (h := h) (w := w b) (j := j) hlt; omega
        · have := nodeStop_le_nodeStart (h := h) (w := w b) (j := j) hlt; omega
    rw [List.pairwise_flatMap]
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun h' => key b b _ _ (Or.inr h')) (List.nodup_finRange _)
    · refine List.Pairwise.imp (fun {b b'} (h' : b ≠ b') => ?_) (List.nodup_finRange M)
      intro g hg g' hg'
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
      obtain ⟨p', -, rfl⟩ := List.mem_map.mp hg'
      exact key b b' p p' (Or.inl h')
  · exact List.Pairwise.nil

/-- A register of a gate of depth `j'` is not strictly between the two registers of a gate of a
depth `j > j'`. -/
theorem disjoint_range_sites_interior_treeLevelGates {j' j : ℕ} (hjj : j' < j)
    {g' g : RegisterGate d N s} (hg' : g' ∈ treeLevelGates hN hT X j')
    (hg : g ∈ treeLevelGates hN hT X j) : Disjoint (Set.range g'.sites) g.interior := by
  obtain ⟨hj', b', p', rfl⟩ := mem_treeLevelGates hg'
  obtain ⟨hj, b, p, rfl⟩ := mem_treeLevelGates hg
  rw [treeRegGate_sites b' hj' p'.isLt, Set.disjoint_left]
  rintro x ⟨t, rfl⟩ hx
  obtain ⟨m, hm, hm1, hm2, he⟩ := mem_interior_treeRegGate hj p.isLt hx
  obtain ⟨rfl, he'⟩ := (blockSite_eq_iff hN).mp he
  simp only at he'
  rw [nodeWindow_val (hT b') (by omega) p'.isLt] at he'
  obtain ⟨m', hm', hm'e⟩ := exists_nodeOffset_eq (h := h) (w := w b') (le_of_lt hjj)
    (by omega : j ≤ h + 1) p'.isLt t
  rw [hm'e] at he'
  rcases nodeOffset_notMem_interior (hT b') (by omega : j ≤ h + 1) hm' p.isLt t with h' | h' <;>
    omega

/-- **The gates of depth `j` of all the blocks are the layer of the unitaries of depth `j` on
the blocks.** -/
theorem list_prod_map_op_treeLevelGates {j : ℕ} (hj : j ≤ h) :
    ((treeLevelGates hN hT X j).map RegisterGate.op).prod =
      blockLayerOp hN fun b => treeLevelOp (hT b) (X b) j := by
  simp only [treeLevelGates, hj, ↓reduceDIte]
  rw [blockLayerOp_eq_list_prod, List.map_flatMap, List.flatMap_def,
    List.prod_flatten, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  rw [Function.comp_apply, treeLevelOp, embedOp_list_prod (blockSite_injective hN b), List.map_map,
    List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp_apply, RegisterGate.op, treeRegGate_sites b hj p.isLt]
  rw [embedOp_embedOp (blockSite_injective hN b)]
  rfl

theorem registerLayersOp_treeLevelGates :
    ∀ m, m ≤ h + 1 → registerLayersOp (treeLevelGates hN hT X) m =
      blockLayerOp hN fun b => treeLevelsOp (hT b) (X b) 0 m
  | 0, _ => by simp [registerLayersOp, treeLevelsOp, blockLayerOp_one]
  | m + 1, hm => by
    rw [registerLayersOp, registerLayersOp_treeLevelGates m (by omega),
      list_prod_map_op_treeLevelGates (by omega), ← blockLayerOp_mul]
    simp only [treeLevelsOp, zero_add]

/-- The sites `s, …, o - s - 1` of every block, `o` the number of sites of its leaves. -/
def treeCentralSites (h s : ℕ) (hN : ∑ b, ℓ b = N) (w : Fin M → ℕ → ℕ) : Set (Fin N) :=
  {x | ∃ b y, s ≤ y.val ∧ y.val + s < leafOffset (w b) (2 ^ (h + 1)) ∧ x = blockSite hN b y}

/-- **The depths `0, …, h` of the trees of all the blocks in depth `(h + 1)(4s + K + 2)` with
measurements.** If every unitary `X b j p` of the nodes is a product of at most `K` gates on
neighbouring sites, some sequence of measurement rounds of total depth `(h + 1)(4s + K + 2)`
implements the depths `0, …, h` of the trees of all the blocks on the vectors with `|0⟩` at the
sites `s, …, o - s - 1` of every block, `o` the number of sites of its leaves: whatever the
outcomes, every output is a scalar multiple of the product of the unitaries applied to the
input.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("every isometry in
eq. (16) takes constant time using measurement"), for blocks of any lengths. -/
theorem exists_rounds_blockLayerOp_treeLevelsOp [NeZero d] {K : ℕ}
    (hK : ∀ b j p, IsPairProduct d (s + s) K (X b j p)) :
    ∃ Rs : List (MeasurementRound d N),
      (Rs.map MeasurementRound.depth).sum = (h + 1) * (4 * s + K + 2) ∧
      MeasurementRound.IsRoundsImplementationOn Rs
        {v | IsZeroOn (treeCentralSites h s hN w) v}
        (blockLayerOp hN fun b => treeLevelsOp (hT b) (X b) 0 (h + 1)) := by
  obtain ⟨Rs, hRs, hRsE⟩ := exists_rounds_registerLayersOp (treeLevelGates hN hT X) (h + 1)
    (fun j _ => pairwise_treeLevelGates j)
    (fun j' j hjj _ g' hg' g hg => disjoint_range_sites_interior_treeLevelGates hjj hg' hg)
    (K := K) fun j _ g hg => by
      obtain ⟨-, b, p, rfl⟩ := mem_treeLevelGates hg
      exact hK b j p
  rw [registerLayersOp_treeLevelGates (h + 1) le_rfl] at hRsE
  refine ⟨Rs, hRs, hRsE.mono fun v hv j _ g hg => ?_⟩
  refine (show IsZeroOn _ v from hv).mono fun x hx => ?_
  obtain ⟨hj, b, p, rfl⟩ := mem_treeLevelGates hg
  obtain ⟨m, hm, hm1, hm2, rfl⟩ := mem_interior_treeRegGate hj p.isLt hx
  have := nodeStop_le (h := h) (w := w b) (by omega : j ≤ h + 1) p.isLt
  exact ⟨b, _, by simp only; omega, by simp only; omega, rfl⟩

/-- **The leaves of all the blocks by one local circuit.** If every unitary of the leaves is a
product of at most `K` gates on neighbouring sites, the leaves of all the blocks form a local
circuit of depth `K`. -/
theorem isCircuitOn_blockLayerOp_treeLeafOp {K : ℕ}
    (U : ∀ b (p : Fin (2 ^ (h + 1))),
      Matrix (Cfg d (leafLen h (ℓ b) (w b) p)) (Cfg d (leafLen h (ℓ b) (w b) p)) ℂ)
    (hU : ∀ b (p : Fin (2 ^ (h + 1))), IsPairProduct d (leafLen h (ℓ b) (w b) p) K (U b p)) :
    IsCircuitOn Set.univ K (blockLayerOp hN fun b => treeLeafOp (hT b) (U b)) := by
  refine (IsCircuitOn.finset_noncommProd Finset.univ (fun b => Set.range (blockSite hN b))
    (fun b _ b' _ h' => disjoint_range_blockSite hN h') _ (fun b _ => ?_) _).mono_set
      (Set.subset_univ _)
  change IsCircuitOn _ K (embedOp (blockSite hN b) (treeLeafOp (hT b) (U b)))
  rw [treeLeafOp, embedOp_list_prod (blockSite_injective hN b), List.map_map]
  have hcomp : (embedOp (blockSite hN b) ∘ fun p : Fin (2 ^ (h + 1)) =>
      embedOp (leafWindow (hT b) p) (U b p)) =
      fun p : Fin (2 ^ (h + 1)) => embedOp (blockSite hN b ∘ leafWindow (hT b) p) (U b p) :=
    funext fun p => embedOp_embedOp (blockSite_injective hN b) _ _
  rw [hcomp]
  refine (isCircuitOn_list_prod_embedOp (fun p : Fin (2 ^ (h + 1)) =>
    blockSite hN b ∘ leafWindow (hT b) p) (U b)
    (fun p => (blockSite_injective hN b).comp (leafWindow_injective (hT b) p.isLt))
    (fun p i i' hi => blockSite_succ hN b _ _ (leafWindow_succ (hT b) p.isLt i i' hi)) (hU b) _
    ?_).mono_set ?_
  · refine List.Pairwise.imp (fun {p p'} (hne : p ≠ p') => ?_) (List.nodup_finRange _)
    rw [Set.range_comp, Set.range_comp]
    exact (disjoint_range_leafWindow (hT b) p.isLt p'.isLt
      (fun h' => hne (Fin.ext h'))).image (blockSite_injective hN b).injOn
      (Set.subset_univ _) (Set.subset_univ _)
  · rintro x ⟨p, -, i, rfl⟩
    exact ⟨_, rfl⟩

end Ring

end MPSPreparation
