/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# One positive buffer length for a finite family of nilpotency lengths

Given finitely many nilpotency lengths $N_i$, this file chooses one positive
integer $L$ with $N_i\leq L+1$ for every index $i$.  It is the finite-family
maximum used for the common blocking of a finite family of rectangular MPS
reductions: each reduction needs exterior buffers of length $N_i-1$, and one
block of $L$ original sites then supplies such a buffer for every member.

## Main definitions

* `commonBufferLength`: the maximum of `1` and of every `N i - 1`.

## Main results

* `commonBufferLength_pos`: the common buffer length is positive.
* `le_commonBufferLength_add_one`: every member satisfies `N i ≤ L + 1`.
-/

section CommonBufferLength

variable {ι : Type*} [Fintype ι]

/-- One positive common buffer length for a finite family of nonnegative
integers: the maximum of `1` and of every `N i - 1`.  It is the least positive
`L` with `N i ≤ L + 1` for every index `i`. -/
noncomputable def commonBufferLength (N : ι → ℕ) : ℕ :=
  max 1 (Finset.univ.sup fun i ↦ N i - 1)

/-- The common buffer length is positive. -/
theorem commonBufferLength_pos (N : ι → ℕ) : 0 < commonBufferLength N :=
  lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- Every member of the family is at most the common buffer length plus one. -/
theorem le_commonBufferLength_add_one (N : ι → ℕ) (i : ι) :
    N i ≤ commonBufferLength N + 1 := by
  have hsup : N i - 1 ≤ Finset.univ.sup fun i ↦ N i - 1 :=
    Finset.le_sup (f := fun i ↦ N i - 1) (Finset.mem_univ i)
  have hmax : N i - 1 ≤ commonBufferLength N :=
    hsup.trans (le_max_right _ _)
  omega

/-- The common buffer length is at most any positive length that exceeds every
member of the family minus one. -/
theorem commonBufferLength_le (N : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hN : ∀ i, N i ≤ L + 1) : commonBufferLength N ≤ L := by
  refine max_le hL (Finset.sup_le fun i _ ↦ ?_)
  have := hN i
  omega

end CommonBufferLength
