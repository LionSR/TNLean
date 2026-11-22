/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Horizontal-ray potential of a finite integer edge flow

An edge indexed by `a` starts at the cell corner `a - (1/2,1/2)`.
Horizontal edges point east and vertical edges point north. Summing the vertical
flow crossing the ray to the right of a cell center gives an integer potential.
Its east increment is minus the crossed vertical edge. For a conserved finite
flow, its north increment is the crossed horizontal edge.

This is an auxiliary discrete winding calculation for the exposed contour
argument in SCP10, arXiv:1001.3807, proof of Theorem 6.9, lines 1935–1990.
The flow is not asserted to be an actual region contour; that identification
and the geometric connectivity argument are separate.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

/-- The finite signed vertical flow crossing the horizontal ray to the right
of an integer cell center. -/
def integerContourRayPotential (V : (ℤ × ℤ) →₀ ℤ) (q : ℤ × ℤ) : ℤ :=
  V.sum fun a v => if a.2 = q.2 ∧ q.1 < a.1 then v else 0

private theorem rayPotential_sub (V W : (ℤ × ℤ) →₀ ℤ) (q : ℤ × ℤ) :
    integerContourRayPotential (V - W) q =
      integerContourRayPotential V q - integerContourRayPotential W q := by
  apply Finsupp.sum_sub_index
  intro a v w
  split_ifs <;> simp

private theorem rayPotential_translate (V : (ℤ × ℤ) →₀ ℤ) (d q : ℤ × ℤ) :
    integerContourRayPotential (Finsupp.domCongr (Equiv.addRight d) V) (q + d) =
      integerContourRayPotential V q := by
  classical
  simp only [integerContourRayPotential, Finsupp.domCongr_apply, Finsupp.sum,
    Finsupp.equivMapDomain, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Moving one cell east removes precisely the signed vertical edge crossed
by that step. No flow-conservation hypothesis is needed. -/
theorem integerContourRayPotential_east (V : (ℤ × ℤ) →₀ ℤ) (q : ℤ × ℤ) :
    integerContourRayPotential V (q + (1, 0)) - integerContourRayPotential V q =
      -V (q + (1, 0)) := by
  classical
  have hterm (a : ℤ × ℤ) (v : ℤ) :
      (if a.2 = (q + (1, 0)).2 ∧ (q + (1, 0)).1 < a.1 then v else 0) -
        (if a.2 = q.2 ∧ q.1 < a.1 then v else 0) =
      -(if a = q + (1, 0) then v else 0) := by
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    by_cases hy : a.2 = q.2
    · by_cases hx : a.1 = q.1 + 1
      · have ha : a = q + (1, 0) := Prod.ext hx (by simpa using hy)
        simp [ha]
      · have ha : a ≠ q + (1, 0) := by intro h; exact hx (congrArg Prod.fst h)
        have he : q.1 + 1 < a.1 ↔ q.1 < a.1 := by omega
        simp [hy, ha, he]
    · have ha : a ≠ q + (1, 0) := by intro h; exact hy (by simpa using congrArg Prod.snd h)
      simp [hy, ha]
  change (∑ a ∈ V.support,
    if a.2 = (q + (1, 0)).2 ∧ (q + (1, 0)).1 < a.1 then V a else 0) -
      (∑ a ∈ V.support, if a.2 = q.2 ∧ q.1 < a.1 then V a else 0) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  change -(V.sum fun a v => if a = q + (1, 0) then v else 0) = _
  rw [Finsupp.sum_ite_self_eq']

/-- For a conserved finite oriented edge flow, moving one cell north adds the
signed horizontal edge crossed by that step. The finite support supplies the
horizontal-ray telescoping boundary condition. -/
theorem integerContourRayPotential_north (H V : (ℤ × ℤ) →₀ ℤ)
    (hflow : ∀ a, H a + V a - H (a - (1, 0)) - V (a - (0, 1)) = 0)
    (q : ℤ × ℤ) :
    integerContourRayPotential V (q + (0, 1)) - integerContourRayPotential V q =
      H (q + (0, 1)) := by
  let HE := Finsupp.domCongr (Equiv.addRight (1, 0)) H
  let VN := Finsupp.domCongr (Equiv.addRight (0, 1)) V
  have hcon : V - VN = HE - H := by
    ext a
    change V a - V (a - (0, 1)) = H (a - (1, 0)) - H a
    have h := hflow a
    omega
  have hn : integerContourRayPotential VN (q + (0, 1)) = integerContourRayPotential V q :=
    rayPotential_translate V (0, 1) q
  have he : integerContourRayPotential HE (q + (0, 1)) =
      integerContourRayPotential H (q + (0, 1) - (1, 0)) := by
    have ht := rayPotential_translate H (1, 0) (q + (0, 1) - (1, 0))
    rw [sub_add_cancel] at ht
    exact ht
  have hc := congrArg (fun F => integerContourRayPotential F (q + (0, 1))) hcon
  rw [rayPotential_sub, rayPotential_sub, hn, he] at hc
  have hg := integerContourRayPotential_east H (q + (0, 1) - (1, 0))
  rw [sub_add_cancel] at hg
  omega

end TNLean.PEPS
