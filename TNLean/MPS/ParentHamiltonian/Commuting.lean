/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.RFP.Defs

/-!
# Commuting parent Hamiltonians

This file defines commuting parent Hamiltonians and nearest-neighbor commuting
parent Hamiltonians (NNCPH), and states their connection to the renormalization
fixed point (RFP) property.

## Main definitions

* `MPSTensor.IsCommutingParentHam A L N` — the local terms of the parent
  Hamiltonian on `N` sites with block length `L` mutually commute.
* `MPSTensor.IsNNCPH A N` — nearest-neighbor commuting parent Hamiltonian
  (`L = 2`).

## Main results

* `MPSTensor.rfp_implies_nncph` — RFP ⟹ NNCPH (vacuously true while
  `localTerm` is the zero placeholder)

## References

* arXiv:1606.00608, §3.3 Definition 3.9, Theorem 3.10
* [Beigi–Shor–Whalen, CMP 2012] — ground-space characterization for
  commuting nearest-neighbor Hamiltonians in 1D
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- A parent Hamiltonian has **commuting** local terms when all translated
interaction projectors commute with each other.

See arXiv:1606.00608, Definition 3.9. -/
def IsCommutingParentHam (A : MPSTensor d D) (L N : ℕ) : Prop :=
  ∀ i j : Fin N,
    localTerm A L N i * localTerm A L N j = localTerm A L N j * localTerm A L N i

/-- **Nearest-neighbor commuting parent Hamiltonian** (NNCPH): a commuting
parent Hamiltonian with block length `L = 2`.

See arXiv:1606.00608, Definition 3.9. -/
def IsNNCPH (A : MPSTensor d D) (N : ℕ) : Prop :=
  IsCommutingParentHam A 2 N

/-- NNCPH is a special case of commuting parent Hamiltonian. -/
theorem IsNNCPH.isCommutingParentHam {A : MPSTensor d D} {N : ℕ} (h : IsNNCPH A N) :
    IsCommutingParentHam A 2 N :=
  h

/-- The commuting condition is symmetric: if `h i j` holds, then `h j i` holds. -/
theorem IsCommutingParentHam.symm {A : MPSTensor d D} {L N : ℕ}
    (h : IsCommutingParentHam A L N) (i j : Fin N) :
    localTerm A L N j * localTerm A L N i = localTerm A L N i * localTerm A L N j :=
  (h i j).symm

/-- **PLACEHOLDER — VACUOUSLY TRUE**: If the parent Hamiltonian commutes, then
the Hamiltonian commutes with each local term.

This lemma compiles without `sorry` but is currently **vacuously true** because
`localTerm` is a zero placeholder (see `Defs.lean`). The proof does not use
the commutativity hypothesis `h` and must be completely rewritten once
`localTerm` is implemented with its real definition. Do **not** cite this as
a proven result. -/
theorem IsCommutingParentHam.ham_comm_localTerm {A : MPSTensor d D} {L N : ℕ}
    (_h : IsCommutingParentHam A L N) (i : Fin N) :
    parentHamiltonian A L N * localTerm A L N i =
      localTerm A L N i * parentHamiltonian A L N := by
  -- TODO(parent-hamiltonian): proof is vacuous while localTerm = 0; must use
  -- `_h` once real definition lands. Intended proof structure:
  --   simp [parentHamiltonian, Finset.sum_mul, Finset.mul_sum]
  --   congr 1; ext j; exact _h j i
  simp only [parentHamiltonian, Finset.sum_mul, Finset.mul_sum, localTerm]

/-- **PLACEHOLDER — VACUOUSLY TRUE**: **RFP ⟹ NNCPH** (Theorem 3.10
(i) ⟹ (iii)): If a tensor is an RFP, then its parent Hamiltonian with
`L = 2` has commuting local terms.

This lemma compiles without `sorry` but is currently **vacuously true** because
`localTerm` is a zero placeholder (see `Defs.lean`). With `localTerm := 0`,
the commuting condition reduces to `0 * 0 = 0 * 0`, which holds trivially.

Once `localTerm` is implemented with its true definition, this lemma must
be rewritten to use the structural form of RFP tensors (Theorem 3.11,
issue #233). Do **not** cite this as a proven result. -/
theorem rfp_implies_nncph {A : MPSTensor d D} (N : ℕ)
    (_hRFP : IsRFP A) : IsNNCPH A N := by
  intro i j
  simp [localTerm]

end MPSTensor
