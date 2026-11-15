/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualHomotopyClassification
import Mathlib.GroupTheory.Perm.Basic

/-!
# When displacement uniformly classifies supported dual homotopies

The seam-word detector can be based at any forbidden primal support vertex.
The surrounding square has zero lifted displacement but cannot be contracted
by square moves whose support excludes that vertex. Consequently, lifted
displacement classifies all pairs of labelled dual paths exactly when every
square-move support is allowed. No lower bound on the periods is required.

This characterizes a limitation of the restricted-support interpretation of
SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214. It is a statement about
generated homotopy, not a physical flux measurement or a characterization
of vacuum reduced density. The test group is independent of the physical
insertion group. See
`docs/paper-gaps/scp10_restricted_displacement_criterion.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} {G : Type*} [Group G]
local notation "X" => TorusVertex width height
local instance restrictedCriterionQuiver : Quiver X := torusDualQuiver width height

private def basedSeamStep (c : X) (u v : G) {a b : X} : TorusDualStep a b → G
  | .east x _ => if x + 1 = c.1 then u else 1
  | .west x _ => (if x + 1 = c.1 then u else 1)⁻¹
  | .north _ y => if y + 1 = c.2 then v else 1
  | .south _ y => (if y + 1 = c.2 then v else 1)⁻¹

private theorem basedSeamStep_reverse (c : X) (u v : G) {a b : X}
    (e : TorusDualStep a b) :
    basedSeamStep c u v e.reverse = (basedSeamStep c u v e)⁻¹ := by
  cases e <;> simp [TorusDualStep.reverse, basedSeamStep]

/-- Ordered nonabelian seam transport with its two seams based at a specified
primal support vertex. This detects restricted homotopy beyond displacement;
the group is an arbitrary test group, independent of physical flux insertions. -/
def torusDualSeamWordAt (c : X) (u v : G) {a : X} : {b : X} → TorusDualPath a b → G
  | _, .nil => 1
  | _, .cons p e => torusDualSeamWordAt c u v p * basedSeamStep c u v e

private theorem basedSeamWord_comp (c : X) (u v : G) {a b z : X}
    (p : TorusDualPath a b) (q : TorusDualPath b z) :
    torusDualSeamWordAt c u v (p.comp q) =
      torusDualSeamWordAt c u v p * torusDualSeamWordAt c u v q := by
  induction q with
  | nil => simp [torusDualSeamWordAt]
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, torusDualSeamWordAt, ih, mul_assoc]

private theorem basedSeamWord_reverse (c : X) (u v : G) {a b : X}
    (p : TorusDualPath a b) :
    torusDualSeamWordAt c u v p.reverse = (torusDualSeamWordAt c u v p)⁻¹ := by
  induction p with
  | nil => simp only [Quiver.Path.reverse, torusDualSeamWordAt, inv_one]
  | cons p e ih =>
    simp only [Quiver.Path.reverse, basedSeamWord_comp, Quiver.Hom.toPath,
      torusDualSeamWordAt, ih, mul_inv_rev, one_mul]
    change basedSeamStep c u v e.reverse * (torusDualSeamWordAt c u v p)⁻¹ =
      (basedSeamStep c u v e)⁻¹ * (torusDualSeamWordAt c u v p)⁻¹
    rw [basedSeamStep_reverse]

/-- Every generated homotopy supported away from a specified primal vertex
preserves the nonabelian seam word based at that vertex. -/
theorem TorusDualHomotopy.seamWordAt_eq_of_not_mem
    {R : Set X} {a b : X} {p q : TorusDualPath a b}
    (h : TorusDualHomotopy R p q) (c : X) (hc : c ∉ R) (u v : G) :
    torusDualSeamWordAt c u v p = torusDualSeamWordAt c u v q := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | comp h k ih ik => simp only [basedSeamWord_comp, ih, ik]
  | reverse h ih => simp only [basedSeamWord_reverse, ih]
  | backtrack e =>
    simp only [torusDualSeamWordAt, basedSeamStep_reverse, one_mul, mul_inv_cancel]
  | square x y hxy =>
    by_cases hx : x + 1 = c.1
    · by_cases hy : y + 1 = c.2
      · have h0 : c ∈ R := by simpa only [hx, hy] using hxy
        exact (hc h0).elim
      · simp only [torusDualEastNorth, torusDualNorthEast, torusDualSeamWordAt,
          basedSeamStep, hx, hy, ite_true, ite_false, one_mul, mul_one]
    · simp only [torusDualEastNorth, torusDualNorthEast, torusDualSeamWordAt,
        basedSeamStep, hx, ite_false, one_mul, mul_one]

/-- Every labelled dual square has zero lifted integer displacement, at all periods. -/
@[simp]
theorem torusDualSquareLoop_displacement_zero (x : ZMod width) (y : ZMod height) :
    torusDualPathDisplacement (torusDualSquareLoop x y) = (0, 0) := by
  ext <;> simp [torusDualSquareLoop, TorusDualStep.displacement]

/-- The square surrounding any excluded primal support vertex cannot be
contracted by supported square and backtrack moves. The noncommuting test
permutations are constructed internally, with no physical-group hypothesis. -/
theorem torusDualSquareLoop_not_homotopic_of_support_excludes
    (R : Set X) (c : X) (hc : c ∉ R) :
    ¬ TorusDualHomotopy R (torusDualSquareLoop (c.1 - 1) (c.2 - 1)) .nil := by
  intro h
  let u := Equiv.swap (0 : Fin 3) 1
  let v := Equiv.swap (1 : Fin 3) 2
  have huv : u * v ≠ v * u := by decide
  have hs := h.seamWordAt_eq_of_not_mem c hc u v
  have hcomm : u * v * u⁻¹ * v⁻¹ = 1 := by
    simpa only [torusDualSquareLoop, torusDualSeamWordAt, basedSeamStep,
      sub_add_cancel, ite_true, one_mul] using hs
  apply huv
  calc
    u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by simp [mul_assoc]
    _ = v * u := by rw [hcomm, one_mul]

/-- Lifted displacement classifies every pair of paths with the same
endpoints under supported homotopy if and only if every primal square-move
support is allowed. This is a uniform criterion over all finite labelled
paths, not a decision procedure for individual restricted homotopies.
Mathematical limitation of the restricted reading of SCP10, Lemma 6.14. -/
theorem torusDualHomotopy_displacement_complete_iff_support_univ (R : Set X) :
    (∀ {a b : X} (p q : TorusDualPath a b),
      torusDualPathDisplacement p = torusDualPathDisplacement q →
        TorusDualHomotopy R p q) ↔ R = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro c
    by_contra hc
    have hd : torusDualPathDisplacement (torusDualSquareLoop (c.1 - 1) (c.2 - 1)) =
        torusDualPathDisplacement (.nil : TorusDualPath (c.1 - 1, c.2 - 1)
          (c.1 - 1, c.2 - 1)) := by
      simp
    exact torusDualSquareLoop_not_homotopic_of_support_excludes R c hc (h _ _ hd)
  · intro h a b p q hd
    rw [h]
    exact (torusDualHomotopy_univ_iff_displacement_eq p q).mpr hd

end TNLean.PEPS
