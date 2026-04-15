/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.StructuralForm

/-!
# Commuting parent Hamiltonians

This file defines commuting parent Hamiltonians and nearest-neighbor commuting
parent Hamiltonians (NNCPH).

## Main definitions

* `MPSTensor.IsCommutingParentHam A L N` — the local terms of the parent
  Hamiltonian on `N` sites with block length `L` mutually commute.
* `MPSTensor.IsNNCPH A N` — nearest-neighbor commuting parent Hamiltonian
  (`L = 2`).

## Main results

* `MPSTensor.IsCommutingParentHam.ham_comm_localTerm` — if local terms commute,
  the full Hamiltonian commutes with each local term.
* `MPSTensor.rfp_implies_nncph` — scaffold for the RFP `⟹` NNCPH direction of
  Theorem 3.10.
* `MPSTensor.nncph_implies_rfp` — scaffold for the NNCPH `⟹` RFP direction of
  Theorem 3.10.

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

/-- If the parent Hamiltonian commutes, then the Hamiltonian commutes with
each local term. -/
theorem IsCommutingParentHam.ham_comm_localTerm {A : MPSTensor d D} {L N : ℕ}
    (_h : IsCommutingParentHam A L N) (i : Fin N) :
    parentHamiltonian A L N * localTerm A L N i =
      localTerm A L N i * parentHamiltonian A L N := by
  simp only [parentHamiltonian, Finset.sum_mul, Finset.mul_sum]
  congr 1
  ext j : 1
  exact _h j i

/-- **Theorem 3.10(i)⟹(iii)** (arXiv:1606.00608): RFP implies NNCPH.
A renormalization fixed-point tensor in left-canonical form has a nearest-neighbor
commuting parent Hamiltonian.

The proof uses the structural form (Lemma B.1): RFP tensors generate
product-of-entangled-pair states, whose parent Hamiltonians have commuting
local terms.

Gated on: the full Appendix B structural decomposition (cf. `rfp_nt_structural`). -/
theorem rfp_implies_nncph (A : MPSTensor d D) [NeZero D]
    (hRFP : IsRFP A) (hNT : IsNormal A)
    (hLeft : IsLeftCanonical A)
    (N : ℕ) (hN : 2 ≤ N) :
    IsNNCPH A N := by
  classical
  -- Missing bridge:
  -- 1. Upgrade the injective rank-one transfer-map classification to the full
  --    Appendix B product-of-entangled-pairs decomposition.
  -- 2. Prove that tensors in that product-of-pairs form have commuting
  --    nearest-neighbor parent projectors after transport through the formal
  --    `groundSpace`/`parentInteraction`/`localTerm` definitions.
  sorry

/-- **Theorem 3.10(iii)⟹(i)** (arXiv:1606.00608): NNCPH implies RFP.
Gated on [Beigi–Shor–Whalen, CMP 2012] — ground-space characterization
for commuting nearest-neighbor Hamiltonians in 1D.

Note: with the present Lean definition, `IsRFP` is a normalization-sensitive
idempotence equation for `transferMap A`, whereas `IsNNCPH` is invariant under
nonzero scalar rescaling of the tensor. A final theorem should therefore include
a normalization hypothesis, such as `IsLeftCanonical A`, before applying the
commuting-Hamiltonian ground-space characterization. -/
theorem nncph_implies_rfp (A : MPSTensor d D) [NeZero D]
    (hNNCPH : ∀ N, 2 ≤ N → IsNNCPH A N)
    (hNT : IsNormal A) :
    IsRFP A := by
  have _hTwoSite : IsNNCPH A 2 := hNNCPH 2 le_rfl
  -- Missing bridge:
  -- 1. A formal Beigi--Shor--Whalen theorem for 1D nearest-neighbor commuting
  --    Hamiltonians, stated for the concrete `localTerm`/`groundSpace` API.
  -- 2. A derivation of zero correlation length or transfer-map idempotence from
  --    that ground-space characterization.
  -- 3. A normalization hypothesis or a normalized representative, since the
  --    current statement is scale-invariant on the NNCPH side but not on the
  --    RFP side.
  sorry

end MPSTensor
