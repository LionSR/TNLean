/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Commuting
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# Overlap reduction for commuting parent-Hamiltonian local terms

For a finite periodic parent Hamiltonian, local terms with disjoint cyclic
supports commute by locality.  Hence the source commutation condition for
interacting translates reduces the all-pairs commuting condition to the pairs
whose cyclic supports overlap.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- To prove that a finite periodic parent Hamiltonian has commuting local
terms, it suffices to check pairs of translated local terms with overlapping
cyclic supports.

The disjoint pairs commute by locality, as recorded in the coefficient-space
non-overlap lemma. This is the finite-chain reduction behind the source
condition \([\tau_j(P_L),P_L]=0\) for interacting translates in
arXiv:1606.00608, Definition 3.9. -/
theorem isCommutingParentHam_of_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {L N : ℕ} (hLN : L ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N L i j →
      localTerm A L N i * localTerm A L N j =
        localTerm A L N j * localTerm A L N i) :
    IsCommutingParentHam A L N := by
  intro i j
  by_cases hij : cyclicWindowsOverlap N L i j
  · exact hOverlap i j hij
  · exact localTerm_commute_of_cyclic_windows_disjoint A hLN
      (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij)

/-- Nearest-neighbor specialization of the overlap reduction for the source
NNCPH commutation equations. -/
theorem isNNCPH_of_twoSite_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {N : ℕ} (hN : 2 ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N 2 i j →
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    IsNNCPH A N :=
  isCommutingParentHam_of_cyclicWindowsOverlap_commute (A := A) (L := 2) hN hOverlap

end MPSTensor
