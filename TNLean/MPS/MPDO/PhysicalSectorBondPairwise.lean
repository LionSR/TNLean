/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorBondTwoSite

/-!
# Pairwise commutativity of the physical-sector bond

This file assembles the local commutator calculations for the physical-sector
bond into pairwise commutativity on every periodic chain of length at least
two. For chains of length at least three, overlapping two-site windows either coincide or are cyclic
neighbors; all other pairs have disjoint supports. The crossed two-site chain
is treated separately.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition C.8, lines 1571--1593
-/

open scoped Matrix Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Moving one site clockwise is the same cyclic rotation used in the MPO
formulation. -/
private theorem cyclicForwardSite_one_eq_finRotate {N : ℕ} (i : Fin N) :
    MPSTensor.cyclicForwardSite i 1 = finRotate N i := by
  apply Fin.ext
  simp [MPSTensor.cyclicForwardSite, finRotate_apply, Fin.add_def]

/-- All translates of the physical bond commute pairwise on every periodic
chain of length at least two.

This assembles the adjacent, crossed two-site, and disjoint-support
calculations. It uses no positivity, strong-area-law, zero-correlation-length,
or injectivity hypothesis beyond the given physical-sector factorization.

Source: arXiv:1606.00608, Appendix C.2, Proposition C.8, lines
1571--1593. -/
theorem physicalBond_pairwise_comm (F : PhysicalSectorFactorization K)
    {N : ℕ} (hN : 2 ≤ N) (i j : Fin N) :
    embedLocalOperator (d := d) 2 N hN i F.physicalBond *
        embedLocalOperator (d := d) 2 N hN j F.physicalBond =
      embedLocalOperator (d := d) 2 N hN j F.physicalBond *
        embedLocalOperator (d := d) 2 N hN i F.physicalBond := by
  by_cases htwo : N = 2
  · subst N
    fin_cases i <;> fin_cases j
    · rfl
    · exact F.physicalBond_two_zero_one_comm
    · exact F.physicalBond_two_zero_one_comm.symm
    · rfl
  · have hthree : 3 ≤ N := by omega
    by_cases hoverlap : MPSTensor.cyclicWindowsOverlap N 2 i j
    · rcases MPSTensor.cyclicWindowsOverlap_twoSite_cases hoverlap with hji | hji | hij
      · subst j
        rfl
      · subst j
        rw [cyclicForwardSite_one_eq_finRotate]
        exact F.physicalBond_adjacent_comm hthree i
      · subst i
        rw [cyclicForwardSite_one_eq_finRotate]
        exact (F.physicalBond_adjacent_comm hthree j).symm
    · exact F.physicalBond_disjoint_comm hN hoverlap

end MPOTensor.PhysicalSectorFactorization
