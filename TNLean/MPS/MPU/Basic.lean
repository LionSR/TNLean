/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixReindexUnitary
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Matrix Product Unitaries — core definition and blocking preservation

This file defines the exact all-`N>1` Matrix Product Unitary (MPU) predicate for
the MPO tensor type `MPOTensor d D`, together with thin unitarity equation lemmas
and the proof that physical blocking preserves the MPU property.

We follow the notation and definitions of
Cirac--Perez-Garcia--Schuch--Verstraete, Section II, lines 297--340:

* `IsMPU U`: the tensor `U` generates a translationally invariant family of
  unitary MPO operators `mpo U N` for every `N > 1`.
* `IsMPU.mpo_mul_conjTranspose_mpo` and `IsMPU.conjTranspose_mpo_mul_mpo`:
  the two defining unitarity equations (thin lemmas).
* `IsMPU.blockTensor`: physical blocking preserves the MPU property,
  proved via `mpo_blockTensor_eq_reindex` and the fact that square-matrix
  reindexing along an equivalence preserves membership in `Matrix.unitaryGroup`
  (see `Matrix.reindex_mem_unitaryGroup`).

## Main definitions

* `IsMPU` — the all-`N>1` MPU predicate (Section II, eq. `UisUnitary`).

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, "Matrix Product Unitaries:
  Structure, Symmetries, and Topological Invariants", Section II, lines 297--340
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-! ### All-`N>1` MPU predicate -/

/-- A tensor `U : MPOTensor d D` generates a **Matrix Product Unitary** (MPU) if
its periodic MPO operator family `mpo U N` is unitary for every system size
`N > 1`.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Section II, equation `UisUnitary`,
lines 327--335. -/
def IsMPU (U : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 1 < N → mpo U N ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ

/-! ### Thin unitarity equation lemmas -/

namespace IsMPU

/-- Membership in `Matrix.unitaryGroup` for a specific system size `N > 1`.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Section II, equation `UisUnitary`,
lines 327--335. -/
lemma mpo_mem_unitaryGroup {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N) :
    mpo U N ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ :=
  hU N hN

/-- The first unitarity equation: `(mpo U N) * (mpo U N)ᴴ = 1` for `N > 1`.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Section II, equation `UisUnitary`,
lines 327--335. -/
lemma mpo_mul_conjTranspose_mpo {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N) :
    mpo U N * (mpo U N)ᴴ = (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) := by
  have hmem := mpo_mem_unitaryGroup hU hN
  rw [Matrix.mem_unitaryGroup_iff] at hmem
  simpa [Matrix.star_eq_conjTranspose] using hmem

/-- The second unitarity equation: `(mpo U N)ᴴ * (mpo U N) = 1` for `N > 1`.

This follows from `Matrix.mem_unitaryGroup_iff'`, which gives the left-multiplied
variant of the unitarity condition.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Section II, equation `UisUnitary`,
lines 327--335. -/
lemma conjTranspose_mpo_mul_mpo {U : MPOTensor d D} (hU : IsMPU U) {N : ℕ} (hN : 1 < N) :
    (mpo U N)ᴴ * mpo U N = (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) := by
  have hmem := mpo_mem_unitaryGroup hU hN
  rw [Matrix.mem_unitaryGroup_iff'] at hmem
  simpa [Matrix.star_eq_conjTranspose] using hmem

end IsMPU

/-! ### Blocking preservation -/

/-- Physical blocking preserves the MPU property: if `U` generates MPU then
`blockTensor U L` also generates MPU for every `L > 0`.

The proof uses `mpo_blockTensor_eq_reindex` to relate the blocked operator
family to the original one, and `Matrix.reindex_mem_unitaryGroup` to transport
unitarity through the index equivalence.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, Definition `blocking`,
lines 297--305, and the definition `MPUblock`, lines 303--305. -/
lemma IsMPU.blockTensor {U : MPOTensor d D} (hU : IsMPU U) (L : ℕ) (hL : 0 < L) :
    IsMPU (blockTensor U L) := by
  intro N hN
  rw [mpo_blockTensor_eq_reindex U L N]
  have hL' : 1 ≤ L := Nat.succ_le_of_lt hL
  have hNL : 1 < N * L :=
    calc
      1 < N := hN
      _ = N * 1 := by simp
      _ ≤ N * L := Nat.mul_le_mul_left N hL'
  apply Matrix.reindex_mem_unitaryGroup
    (MPSTensor.blockedConfigEquiv d N L).symm (mpo U (N * L))
  exact IsMPU.mpo_mem_unitaryGroup hU hNL

end MPOTensor
