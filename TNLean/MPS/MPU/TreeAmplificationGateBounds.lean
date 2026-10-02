/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BalancedIntervalTree
import TNLean.MPS.MPU.AmplifiedRecursionBounds

/-!
# Gate-count recursion on the actual balanced interval tree

The numerical count at a node is the exact amplification count, with both
child counts included in the pre-amplification circuit. If the joining and
two reflection costs have uniform bounds and the number of rounds is at
most `D`, the count on any binary tree is bounded geometrically by its
actual height. The explicitly constructed balanced interval tree then gives
a polynomial bound in its arbitrary positive physical length.

These results count the stated recursive operations. They do not assume
or assert the existence of any circuit. Source: the resource calculation
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

variable {α : Type*}

/-- A numerical tree recursion with leaf cost `K`, child multiplier `b`,
and additive node overhead `C`. Source: the resource calculation in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def treeGateCount (K b C : ℕ) : BinaryTree α → ℕ
  | .nil => K
  | .node _ left right => b * (treeGateCount K b C left + treeGateCount K b C right) + C

/-- Keeping one overhead term in the induction invariant absorbs the node
addition on an arbitrary actual tree. Source: the resource calculation in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem treeGateCount_add_overhead_le_height (K b C : ℕ) (hb : 1 ≤ b)
    (t : BinaryTree α) :
    treeGateCount K b C t + C ≤ (K + C) * (2 * b) ^ t.height := by
  induction t with
  | nil => simp [treeGateCount]
  | node cut left right ihleft ihright =>
    have hC : C ≤ b * C := by simpa using Nat.mul_le_mul_right C hb
    have hleft : treeGateCount K b C left + C ≤
        (K + C) * (2 * b) ^ max left.height right.height :=
      ihleft.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega : 0 < 2 * b) (Nat.le_max_left _ _)))
    have hright : treeGateCount K b C right + C ≤
        (K + C) * (2 * b) ^ max left.height right.height :=
      ihright.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega : 0 < 2 * b) (Nat.le_max_right _ _)))
    rw [treeGateCount, BinaryTree.height]
    calc
      _ ≤ b * (treeGateCount K b C left + treeGateCount K b C right) +
          (b * C + b * C) := by omega
      _ = b * ((treeGateCount K b C left + C) +
          (treeGateCount K b C right + C)) := by ring
      _ ≤ b * (((K + C) * (2 * b) ^ max left.height right.height) +
          ((K + C) * (2 * b) ^ max left.height right.height)) :=
        Nat.mul_le_mul_left b (Nat.add_le_add hleft hright)
      _ = (K + C) * (2 * b) ^ (max left.height right.height + 1) := by
        rw [pow_succ]
        ring

/-- Uniform joining and reflection costs give the explicit additive node
term after at most `D` amplification rounds. Source: the exact node count
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def amplificationTreeOverhead (D M B L : ℕ) : ℕ :=
  (2 * D + 1) * M + D * (1 + B + L)

/-- The actual numerical amplification count on a tree, allowing the number
of rounds to depend on its cut label. Source: the exact circuit gate formula
in Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def amplificationTreeGateCount (K M B L : ℕ) (rounds : α → ℕ) : BinaryTree α → ℕ
  | .nil => K
  | .node cut left right =>
    let pre := amplificationTreeGateCount K M B L rounds left +
      amplificationTreeGateCount K M B L rounds right + M
    rounds cut * (1 + (2 * pre + B + L)) + pre

/-- Using the same upper bound on rounds at every cut gives exactly the
linear two-child recursion with its stated overhead. Source: the resource
calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationTreeGateCount_const_eq_treeGateCount (K M B L D : ℕ)
    (t : BinaryTree α) :
    amplificationTreeGateCount K M B L (fun _ ↦ D) t =
      treeGateCount K (2 * D + 1) (amplificationTreeOverhead D M B L) t := by
  induction t with
  | nil => rfl
  | node cut left right ihleft ihright =>
    simp only [amplificationTreeGateCount, treeGateCount, ihleft, ihright]
    rw [amplificationTreeOverhead]
    ring

/-- The exact two-child node formula has child multiplier `2D+1` and the
stated uniform overhead. Source: the resource calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplification_node_gateCount_le {ℓ D : ℕ} (hℓ : ℓ ≤ D)
    (left right M B L : ℕ) :
    ℓ * (1 + (2 * (left + right + M) + B + L)) + (left + right + M) ≤
      (2 * D + 1) * (left + right) + amplificationTreeOverhead D M B L := by
  calc
    _ ≤ D * (1 + (2 * (left + right + M) + B + L)) + (left + right + M) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hℓ) _
    _ = _ := by rw [amplificationTreeOverhead]; ring

/-- The recursively defined exact node counts are bounded by the generic
tree recursion; no recurrence witness is supplied. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationTreeGateCount_le_treeGateCount (K M B L D : ℕ)
    (rounds : α → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) (t : BinaryTree α) :
    amplificationTreeGateCount K M B L rounds t ≤
      treeGateCount K (2 * D + 1) (amplificationTreeOverhead D M B L) t := by
  induction t with
  | nil => rfl
  | node cut left right ihleft ihright =>
    rw [amplificationTreeGateCount, treeGateCount]
    exact (amplification_node_gateCount_le (hrounds cut) _ _ M B L).trans
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.add_le_add ihleft ihright)) _)

/-- On any actual binary tree, the amplification count plus its reserve
has geometric bound with branching factor `4D+2`. Source: the resource
calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationTreeGateCount_add_overhead_le_height (K M B L D : ℕ)
    (rounds : α → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) (t : BinaryTree α) :
    amplificationTreeGateCount K M B L rounds t + amplificationTreeOverhead D M B L ≤
      (K + amplificationTreeOverhead D M B L) * (4 * D + 2) ^ t.height := by
  have hgeneric := treeGateCount_add_overhead_le_height K (2 * D + 1)
    (amplificationTreeOverhead D M B L) (by omega) t
  have hbound := Nat.add_le_add_right
    (amplificationTreeGateCount_le_treeGateCount K M B L D rounds hrounds t)
    (amplificationTreeOverhead D M B L)
  exact hbound.trans (by simpa only [show 2 * (2 * D + 1) = 4 * D + 2 by omega]
    using hgeneric)

/-- The count itself satisfies the same geometric height bound on any
actual tree. Source: the resource calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationTreeGateCount_le_height (K M B L D : ℕ)
    (rounds : α → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) (t : BinaryTree α) :
    amplificationTreeGateCount K M B L rounds t ≤
      (K + amplificationTreeOverhead D M B L) * (4 * D + 2) ^ t.height :=
  (Nat.le_add_right _ _).trans
    (amplificationTreeGateCount_add_overhead_le_height K M B L D rounds hrounds t)

/-- The actual balanced interval tree gives a polynomial numerical count
at every positive physical length, without assuming a height or partition.
Source: the resource calculation in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationTreeGateCount_balanced_le_polynomial
    (K M B L D start N : ℕ) (hN : 0 < N)
    (rounds : ℕ → ℕ) (hrounds : ∀ cut, rounds cut ≤ D) :
    amplificationTreeGateCount K M B L rounds (balancedIntervalTree start N) ≤
      (K + amplificationTreeOverhead D M B L) * (2 * N) ^ Nat.clog 2 (4 * D + 2) := by
  let C := amplificationTreeOverhead D M B L
  let R := 4 * D + 2
  have hheight := amplificationTreeGateCount_add_overhead_le_height
    K M B L D rounds hrounds (balancedIntervalTree start N)
  rw [balancedIntervalTree_height] at hheight
  have hpoly := gateCount_le_polynomial_of_balanced_height
    (fun h ↦ (K + C) * R ^ h) (K + C) 0 R N (by omega) hN (by simp)
    (by intro h; simp [pow_succ, Nat.mul_left_comm, Nat.mul_comm])
  exact (Nat.le_add_right _ _).trans (hheight.trans (by simpa only [Nat.add_zero] using hpoly))

end MPUCircuit
