/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteHierarchy

/-!
# Finite physical regions of the retained hierarchy

The physical sites in a parent block are the disjoint union of its two child
regions. The recursive finite sets agree with the existing supersite quotient
blocks, including empty blocks beyond the physical chain. These coordinates
are used for the retained-basis expansion of Hastings,
arXiv:cond-mat/0508554v3, Section III, lines 630–685.
-/

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Physical sites in a finite block of the binary hierarchy.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 609–685. -/
def hierarchyBlock (blk : ι → ℕ) : ℕ → ℕ → Finset ι
  | 0, k => Finset.univ.filter (fun i ↦ blk i = k)
  | m + 1, k => hierarchyBlock blk m (2 * k) ∪ hierarchyBlock blk m (2 * k + 1)

/-- The recursive finite region is exactly the existing supersite block.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 609–685. -/
theorem mem_hierarchyBlock (blk : ι → ℕ) (m k : ℕ) (i : ι) :
    i ∈ hierarchyBlock blk m k ↔ i ∈ levelBlock blk m k := by
  induction m generalizing k with
  | zero => simp [hierarchyBlock, levelBlock]
  | succ m ih =>
      simp only [hierarchyBlock, Finset.mem_union, ih, levelBlock,
        Set.mem_ofPred_eq, pow_succ, ← Nat.div_div_eq_div_mul]
      omega

/-- The finite and set-valued blocks have the same physical sites.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 609–685. -/
theorem coe_hierarchyBlock (blk : ι → ℕ) (m k : ℕ) :
    (hierarchyBlock blk m k : Set ι) = levelBlock blk m k :=
  Set.ext (mem_hierarchyBlock blk m k)

/-- The two child regions are disjoint, including padded empty blocks.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 609–685. -/
theorem disjoint_hierarchyBlock_children (blk : ι → ℕ) (m k : ℕ) :
    Disjoint (hierarchyBlock blk m (2 * k)) (hierarchyBlock blk m (2 * k + 1)) :=
  Finset.disjoint_left.mpr fun _ hleft hright ↦
    Set.disjoint_left.mp (disjoint_levelBlock_two_mul blk m k)
      ((mem_hierarchyBlock blk m (2 * k) _).mp hleft)
      ((mem_hierarchyBlock blk m (2 * k + 1) _).mp hright)

/-- A block containing every supersite is the whole physical region.
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 609–685. -/
theorem hierarchyBlock_eq_univ (blk : ι → ℕ) (h : ℕ)
    (hblk : ∀ i, blk i < 2 ^ h) : hierarchyBlock blk h 0 = Finset.univ :=
  Finset.eq_univ_iff_forall.mpr fun i ↦
    (mem_hierarchyBlock blk h 0 i).mpr (Nat.div_eq_of_lt (hblk i))

end TNLean.MPS.AreaLaw.LocalSolution
