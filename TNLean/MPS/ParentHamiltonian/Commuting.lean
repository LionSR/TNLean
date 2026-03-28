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

* `MPSTensor.rfp_implies_nncph` — RFP ⟹ NNCPH (sorry, pending structural
  form from #233)
* `MPSTensor.nncph_implies_rfp` — NNCPH ⟹ RFP (sorry, gated on [Beigi])

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

/-- The commuting condition is trivially true for any single local term. -/
theorem isCommutingParentHam_self (A : MPSTensor d D) (L N : ℕ) (i : Fin N) :
    localTerm A L N i * localTerm A L N i = localTerm A L N i * localTerm A L N i :=
  rfl

/-- The commuting condition is symmetric: if `h i j` holds, then `h j i` holds. -/
theorem IsCommutingParentHam.symm {A : MPSTensor d D} {L N : ℕ}
    (h : IsCommutingParentHam A L N) (i j : Fin N) :
    localTerm A L N j * localTerm A L N i = localTerm A L N i * localTerm A L N j :=
  (h i j).symm

/-- If the parent Hamiltonian commutes, then the Hamiltonian commutes with each
local term. -/
theorem IsCommutingParentHam.ham_comm_localTerm {A : MPSTensor d D} {L N : ℕ}
    (h : IsCommutingParentHam A L N) (i : Fin N) :
    parentHamiltonian A L N * localTerm A L N i =
      localTerm A L N i * parentHamiltonian A L N := by
  simp only [parentHamiltonian, Finset.sum_mul, Finset.mul_sum, localTerm]

/-- **RFP ⟹ NNCPH** (Theorem 3.10 (i) ⟹ (iii)):
If a tensor is an RFP, then its parent Hamiltonian with `L = 2` has
commuting local terms.

The proof follows from the structural form of RFP tensors (Theorem 3.11,
issue #233): RFP tensors generate product-of-entangled-pair states whose
parent Hamiltonians obviously commute.

TODO: complete once the structural form theorem is available from #233. -/
theorem rfp_implies_nncph {A : MPSTensor d D} (N : ℕ)
    (hRFP : IsRFP A) : IsNNCPH A N := by
  sorry

/-- **NNCPH ⟹ RFP** (Theorem 3.10 (iii) ⟹ (i)):
If a tensor has a nearest-neighbor commuting parent Hamiltonian, then it
is a renormalization fixed point.

This uses the result of Beigi–Shor–Whalen (CMP 2012) that ground spaces
of commuting nearest-neighbor Hamiltonians in 1D with finite degeneracy
are spanned by states that are locally orthogonal — hence RFP by the
structural form characterization (Theorem 3.11).

TODO: complete once [Beigi] is formalized. -/
theorem nncph_implies_rfp {A : MPSTensor d D} {N : ℕ}
    (hNN : IsNNCPH A N) : IsRFP A := by
  sorry

/-- **RFP ⟺ NNCPH** (Theorem 3.10 (i) ⟺ (iii)):
A tensor is an RFP if and only if its parent Hamiltonian with `L = 2`
has commuting local terms. -/
theorem rfp_iff_nncph (A : MPSTensor d D) (N : ℕ) :
    IsRFP A ↔ IsNNCPH A N :=
  ⟨rfp_implies_nncph N, fun h => nncph_implies_rfp h⟩

end MPSTensor
