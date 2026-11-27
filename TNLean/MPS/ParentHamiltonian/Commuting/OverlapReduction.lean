/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Commuting.Defs
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport

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
      haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toLin' ((parentRingInteraction A L N).term i) *
          Matrix.toLin' ((parentRingInteraction A L N).term j) =
        Matrix.toLin' ((parentRingInteraction A L N).term j) *
          Matrix.toLin' ((parentRingInteraction A L N).term i)) :
    IsCommutingParentHam A L N := by
  intro i j
  have : NeZero N := NeZero.of_pos i.pos
  by_cases hij : cyclicWindowsOverlap N L i j
  · exact hOverlap i j hij
  · rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul,
      (commute_parentRingInteraction_term_of_cyclic_windows_disjoint A hLN
        (CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap hij)).eq]

/-- Nearest-neighbor specialization of the overlap reduction for the source
NNCPH commutation equations. -/
theorem isNNCPH_of_twoSite_cyclicWindowsOverlap_commute
    {A : MPSTensor d D} {N : ℕ} (hN : 2 ≤ N)
    (hOverlap : ∀ i j : Fin N, cyclicWindowsOverlap N 2 i j →
      haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toLin' ((parentRingInteraction A 2 N).term i) *
          Matrix.toLin' ((parentRingInteraction A 2 N).term j) =
        Matrix.toLin' ((parentRingInteraction A 2 N).term j) *
          Matrix.toLin' ((parentRingInteraction A 2 N).term i)) :
    IsNNCPH A N :=
  isCommutingParentHam_of_cyclicWindowsOverlap_commute (A := A) (L := 2) hN hOverlap

/-- For nearest-neighbor parent Hamiltonians, commutation of each local term with
its cyclic right neighbor implies the full pairwise commutation condition.

The proof uses the preceding case split for overlapping length-two windows and
the locality lemma for disjoint windows. -/
theorem isNNCPH_of_adjacent_twoSite_commute
    {A : MPSTensor d D} {N : ℕ} (hN : 2 ≤ N)
    (hAdjacent : ∀ i : Fin N,
      haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toLin' ((parentRingInteraction A 2 N).term i) *
          Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) =
        Matrix.toLin' ((parentRingInteraction A 2 N).term (cyclicForwardSite i 1)) *
          Matrix.toLin' ((parentRingInteraction A 2 N).term i)) :
    IsNNCPH A N := by
  refine isNNCPH_of_twoSite_cyclicWindowsOverlap_commute (A := A) hN ?_
  intro i j hOverlap
  rcases cyclicWindowsOverlap_twoSite_cases hOverlap with hji | hji | hij
  · subst j
    rfl
  · subst j
    exact hAdjacent i
  · subst i
    exact (hAdjacent j).symm

end MPSTensor
