/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.Transfer
import Mathlib.Data.List.TakeDrop

/-!
# Nonwrapping intervals of a tensor chain

An interval retains the actual ordered tensors of the selected chain. Its transfer map is
the corresponding contiguous subproduct, with no periodic wrapping or homogeneous power.
This is the interval convention used in the inhomogeneous preparation setting of
arXiv:2307.01696.

## References

* arXiv:2307.01696, eq. (18) and paragraph "Inhomogeneous short-range correlated MPS".
-/

namespace MPSChainTensor

/-- The actual tensors on a nonwrapping interval `[a,a+n)`. -/
def interval {d D N : ℕ} (A : MPSChainTensor d D N) (a n : ℕ) (h : a + n ≤ N) :
    MPSChainTensor d D n := fun i => A ⟨a + i, by omega⟩

/-- Restricting an interval again adds its starting offsets. -/
theorem interval_interval {d D N a n b m : ℕ} (A : MPSChainTensor d D N)
    (h : a + n ≤ N) (h' : b + m ≤ n) :
    interval (interval A a n h) b m h' = interval A (a + b) m (by omega) := by
  funext i
  dsimp [interval]
  congr 1
  apply Fin.ext
  simp [Nat.add_assoc]

/-- The interval transfer map is the ordered product selected by list drop and take. -/
theorem transferMap_interval {d D N : ℕ} (A : MPSChainTensor d D N)
    (a n : ℕ) (h : a + n ≤ N) :
    Kraus.transferMap (blockTensor (interval A a n h)) =
      (((List.ofFn fun i => Kraus.transferMap (A i)).drop a).take n).prod := by
  rw [transferMap_blockTensor]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    rfl

end MPSChainTensor
