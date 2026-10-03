/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Range

/-!
# Balanced binary partitions of finite physical intervals

For every positive interval length, midpoint splitting constructs an actual
binary tree with one leaf per physical site. Its internal nodes record the
cut between their consecutive child intervals. In their physical order,
the leaf sites and internal cuts are precisely the corresponding finite
ranges, so every site and every internal cut occurs once. The tree height
is the binary ceiling logarithm of the interval length.

The construction reuses Mathlib's `BinaryTree`; no tree or partition is
supplied as an assumption. This is the finite recursive geometry used in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- Both midpoint child lengths are positive and strictly smaller than a
nontrivial parent length. Source: balanced interval recursion in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem midpoint_child_lengths (n : ℕ) (hn : 2 ≤ n) :
    0 < n / 2 ∧ n / 2 < n ∧ 0 < n - n / 2 ∧ n - n / 2 < n := by
  omega

/-- Midpoint children differ in length by at most one. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem midpoint_child_balance (n : ℕ) :
    n / 2 ≤ n - n / 2 ∧ n - n / 2 ≤ n / 2 + 1 := by
  omega

/-- The larger midpoint child decreases the binary ceiling logarithm by
one. Source: the balanced height estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem clog_two_midpoint (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
  rw [Nat.clog_of_two_le (by decide : 1 < 2) hn]
  congr 2
  omega

/-- The balanced tree of the interval starting at `start` and having length
`n`. Each node records its actual midpoint cut. The value at length zero
is immaterial to the positive-interval statements. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def balancedIntervalTree (start n : ℕ) : BinaryTree ℕ :=
  if n ≤ 1 then .nil else
    .node (start + n / 2) (balancedIntervalTree start (n / 2))
      (balancedIntervalTree (start + n / 2) (n - n / 2))
termination_by n
decreasing_by all_goals omega

/-- A single physical site is a leaf of the constructed tree. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
@[simp] theorem balancedIntervalTree_one (start : ℕ) :
    balancedIntervalTree start 1 = .nil := by
  rw [balancedIntervalTree, ite_eq_left (by omega)]

/-- A nontrivial physical interval splits into its actual midpoint children.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_split (start n : ℕ) (hn : 2 ≤ n) :
    balancedIntervalTree start n =
      .node (start + n / 2) (balancedIntervalTree start (n / 2))
        (balancedIntervalTree (start + n / 2) (n - n / 2)) := by
  rw [balancedIntervalTree, ite_eq_right (by omega)]

/-- Both children lie at a strictly smaller binary logarithmic height.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem midpoint_child_clog_lt (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) < Nat.clog 2 n ∧
      Nat.clog 2 (n - n / 2) < Nat.clog 2 n := by
  have hleft := Nat.clog_mono_right 2 (midpoint_child_balance n).1
  rw [clog_two_midpoint n hn]
  omega

/-- The actual constructed tree has exactly the binary ceiling-logarithmic
height, including intervals whose length is not a power of two. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_height (start n : ℕ) :
    (balancedIntervalTree start n).height = Nat.clog 2 n := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    by_cases hn : n ≤ 1
    · rw [balancedIntervalTree, ite_eq_left hn, BinaryTree.height,
        Nat.clog_of_right_le_one hn]
    · have hlarge : 2 ≤ n := by omega
      obtain ⟨_, hleft, _, hright⟩ := midpoint_child_lengths n hlarge
      rw [balancedIntervalTree, ite_eq_right hn, BinaryTree.height,
        ih (n / 2) hleft, ih (n - n / 2) hright]
      rw [max_eq_right (Nat.clog_mono_right 2 (midpoint_child_balance n).1),
        ← clog_two_midpoint n hlarge]

/-- A binary partition into consecutive nonempty child intervals, with
single-site leaves and each node labelled by the common child boundary.
Source: the physical geometry of Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
inductive IsIntervalPartition : ℕ → ℕ → BinaryTree ℕ → Prop
  | leaf (start : ℕ) : IsIntervalPartition start 1 .nil
  | node {start l r : ℕ} {left right : BinaryTree ℕ}
      (hl : 0 < l) (hr : 0 < r)
      (hleft : IsIntervalPartition start l left)
      (hright : IsIntervalPartition (start + l) r right) :
      IsIntervalPartition start (l + r) (.node (start + l) left right)

/-- Traverse the single-site leaves in physical order, carrying the left
endpoint down the tree. Source: the leaf geometry in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def intervalLeafSites (start : ℕ) : BinaryTree ℕ → List ℕ
  | .nil => [start]
  | .node cut left right => intervalLeafSites start left ++ intervalLeafSites cut right

/-- Traverse all internal cuts in physical order. Source: the once-only
joining cuts in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def intervalTreeCuts : BinaryTree ℕ → List ℕ
  | .nil => []
  | .node cut left right => intervalTreeCuts left ++ cut :: intervalTreeCuts right

/-- A consecutive interval partition has exactly its physical sites as
leaves, in their physical order. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsIntervalPartition.leafSites {start n : ℕ} {t : BinaryTree ℕ}
    (h : IsIntervalPartition start n t) :
    intervalLeafSites start t = List.range' start n := by
  induction h with
  | leaf start => simp [intervalLeafSites, List.range']
  | node hl hr hleft hright ihleft ihright =>
    rw [intervalLeafSites, ihleft, ihright, List.range'_append_1]

/-- A consecutive interval partition uses exactly the internal physical
cuts, in their physical order. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsIntervalPartition.cuts {start n : ℕ} {t : BinaryTree ℕ}
    (h : IsIntervalPartition start n t) :
    intervalTreeCuts t = List.range' (start + 1) (n - 1) := by
  induction h with
  | leaf start => simp [intervalTreeCuts]
  | @node start l r left right hl hr hleft hright ihleft ihright =>
    rw [intervalTreeCuts, ihleft, ihright]
    have htail : (start + l) :: List.range' (start + l + 1) (r - 1) =
        List.range' (start + l) r := by
      conv_rhs => rw [show r = r - 1 + 1 by omega]
      rw [List.range'_succ]
    rw [htail, show start + l = start + 1 + (l - 1) by omega, List.range'_append_1]
    congr 1
    omega

/-- Midpoint recursion constructs a genuine consecutive interval partition
for every positive length. No partition or tree witness is assumed.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_isIntervalPartition (start n : ℕ) (hn : 0 < n) :
    IsIntervalPartition start n (balancedIntervalTree start n) := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    by_cases hsmall : n ≤ 1
    · have hn1 : n = 1 := by omega
      subst n
      rw [balancedIntervalTree, ite_eq_left (by omega)]
      exact IsIntervalPartition.leaf start
    · have hlarge : 2 ≤ n := by omega
      obtain ⟨hl, hleft, hr, hright⟩ := midpoint_child_lengths n hlarge
      rw [balancedIntervalTree, ite_eq_right hsmall]
      have hsplit : n / 2 + (n - n / 2) = n := by omega
      simpa only [hsplit] using IsIntervalPartition.node hl hr
        (ih (n / 2) hleft start hl) (ih (n - n / 2) hright (start + n / 2) hr)

/-- The constructed tree leaves are precisely its single physical sites.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_leafSites (start n : ℕ) (hn : 0 < n) :
    intervalLeafSites start (balancedIntervalTree start n) = List.range' start n :=
  (balancedIntervalTree_isIntervalPartition start n hn).leafSites

/-- The constructed tree records precisely all internal physical cuts.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_cuts (start n : ℕ) (hn : 0 < n) :
    intervalTreeCuts (balancedIntervalTree start n) =
      List.range' (start + 1) (n - 1) :=
  (balancedIntervalTree_isIntervalPartition start n hn).cuts

/-- Every physical site occurs once in the constructed leaf list.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_leafSites_nodup (start n : ℕ) (hn : 0 < n) :
    (intervalLeafSites start (balancedIntervalTree start n)).Nodup := by
  rw [balancedIntervalTree_leafSites start n hn]
  exact List.nodup_range'

/-- No internal cut is used at more than one node of the constructed tree.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_cuts_nodup (start n : ℕ) (hn : 0 < n) :
    (intervalTreeCuts (balancedIntervalTree start n)).Nodup := by
  rw [balancedIntervalTree_cuts start n hn]
  exact List.nodup_range'

/-- A cut occurs at a node exactly when it is an internal physical boundary.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem mem_balancedIntervalTree_cuts (start n : ℕ) (hn : 0 < n) (cut : ℕ) :
    cut ∈ intervalTreeCuts (balancedIntervalTree start n) ↔
      start < cut ∧ cut < start + n := by
  rw [balancedIntervalTree_cuts start n hn, List.mem_range'_1]
  omega

/-- Every internal physical boundary labels exactly one constructed node.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem count_balancedIntervalTree_cut (start n : ℕ) (hn : 0 < n) (cut : ℕ) :
    (intervalTreeCuts (balancedIntervalTree start n)).count cut =
      if start < cut ∧ cut < start + n then 1 else 0 := by
  rw [balancedIntervalTree_cuts start n hn, List.count_range_1']
  have hiff : (start + 1 ≤ cut ∧ cut < start + 1 + (n - 1)) ↔
      (start < cut ∧ cut < start + n) := by omega
  simp only [hiff]

private theorem intervalLeafSites_length (start : ℕ) (t : BinaryTree ℕ) :
    (intervalLeafSites start t).length = t.numLeaves := by
  induction t generalizing start with
  | nil => rfl
  | node cut left right ihleft ihright =>
    simp only [intervalLeafSites, List.length_append, ihleft, ihright, BinaryTree.numLeaves]

/-- The actual tree has one leaf per physical site. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_numLeaves (start n : ℕ) (hn : 0 < n) :
    (balancedIntervalTree start n).numLeaves = n := by
  rw [← intervalLeafSites_length start, balancedIntervalTree_leafSites start n hn,
    List.length_range']

/-- There are exactly `n - 1` merges in the actual tree. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedIntervalTree_numNodes (start n : ℕ) (hn : 0 < n) :
    (balancedIntervalTree start n).numNodes = n - 1 := by
  have h := (balancedIntervalTree start n).numLeaves_eq_numNodes_succ
  rw [balancedIntervalTree_numLeaves start n hn] at h
  omega

/-- Every positive physical interval has an explicitly constructed binary
partition with exactly its sites and internal cuts, at height at most the
binary ceiling logarithm. No tree or geometry witness is assumed. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_balancedIntervalPartition (start n : ℕ) (hn : 0 < n) :
    ∃ t : BinaryTree ℕ, IsIntervalPartition start n t ∧
      intervalLeafSites start t = List.range' start n ∧
      intervalTreeCuts t = List.range' (start + 1) (n - 1) ∧
      t.height ≤ Nat.clog 2 n :=
  ⟨balancedIntervalTree start n, balancedIntervalTree_isIntervalPartition start n hn,
    balancedIntervalTree_leafSites start n hn, balancedIntervalTree_cuts start n hn,
    (balancedIntervalTree_height start n).le⟩

end MPUCircuit
