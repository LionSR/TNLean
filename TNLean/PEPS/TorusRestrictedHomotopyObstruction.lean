/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualWinding
import Mathlib.GroupTheory.Perm.Basic

/-!
# A nonabelian obstruction to restricted dual homotopy

When square moves must avoid the primal origin, a nonabelian seam word is
preserved by every generated homotopy. The square surrounding that forbidden
origin has zero lifted displacement, but its seam word is the commutator of
the two seam generators. A noncommuting pair therefore detects that it cannot
be contracted without sweeping the origin.

This is a mathematical limitation of a restricted-support interpretation of
SCP10, arXiv:1001.3807v3, Lemma 6.14, source lines 2199–2214. Seam words here
are homotopy invariants valued in an arbitrary test group, not physical flux
insertions or an assertion about physical reduced density. In particular,
lifted displacement alone cannot classify these restricted homotopies.
See `docs/paper-gaps/scp10_restricted_homotopy_obstruction.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} {G : Type*} [Group G]
local notation "X" => TorusVertex width height
local instance restrictedWordQuiver : Quiver X := torusDualQuiver width height

private def seamStep (u v : G) {a b : X} : TorusDualStep a b → G
  | .east x _ => if x + 1 = 0 then u else 1
  | .west x _ => (if x + 1 = 0 then u else 1)⁻¹
  | .north _ y => if y + 1 = 0 then v else 1
  | .south _ y => (if y + 1 = 0 then v else 1)⁻¹

private theorem seamStep_reverse (u v : G) {a b : X} (e : TorusDualStep a b) :
    seamStep u v e.reverse = (seamStep u v e)⁻¹ := by
  cases e <;> simp [TorusDualStep.reverse, seamStep]

/-- Ordered seam transport in an arbitrary test group. East and north seam
crossings contribute the two generators, west and south their inverses.
This retains nonabelian information beyond lifted displacement.
Mathematical obstruction for the restricted reading of SCP10, Lemma 6.14. -/
def torusDualSeamWord (u v : G) {a : X} : {b : X} → TorusDualPath a b → G
  | _, .nil => 1
  | _, .cons p e => torusDualSeamWord u v p * seamStep u v e

private theorem seamWord_comp (u v : G) {a b c : X}
    (p : TorusDualPath a b) (q : TorusDualPath b c) :
    torusDualSeamWord u v (p.comp q) =
      torusDualSeamWord u v p * torusDualSeamWord u v q := by
  induction q with
  | nil => simp [torusDualSeamWord]
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, torusDualSeamWord, ih, mul_assoc]

private theorem seamWord_reverse (u v : G) {a b : X} (p : TorusDualPath a b) :
    torusDualSeamWord u v p.reverse = (torusDualSeamWord u v p)⁻¹ := by
  induction p with
  | nil => simp only [Quiver.Path.reverse, torusDualSeamWord, inv_one]
  | cons p e ih =>
    simp only [Quiver.Path.reverse, seamWord_comp, Quiver.Hom.toPath,
      torusDualSeamWord, ih, mul_inv_rev, one_mul]
    change seamStep u v e.reverse * (torusDualSeamWord u v p)⁻¹ =
      (seamStep u v e)⁻¹ * (torusDualSeamWord u v p)⁻¹
    rw [seamStep_reverse]

/-- A generated homotopy whose allowed square supports exclude the origin
preserves every nonabelian seam word. No equality of transports is assumed.
Mathematical obstruction for the restricted reading of SCP10, Lemma 6.14. -/
theorem TorusDualHomotopy.seamWord_eq_of_origin_not_mem
    {R : Set X} {a b : X} {p q : TorusDualPath a b}
    (h : TorusDualHomotopy R p q) (hR : (0, 0) ∉ R) (u v : G) :
    torusDualSeamWord u v p = torusDualSeamWord u v q := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | comp h k ih ik => simp only [seamWord_comp, ih, ik]
  | reverse h ih => simp only [seamWord_reverse, ih]
  | backtrack e =>
    simp only [torusDualSeamWord, seamStep_reverse, one_mul, mul_inv_cancel]
  | square x y hxy =>
    by_cases hx : x + 1 = 0
    · by_cases hy : y + 1 = 0
      · have h0 : (0, 0) ∈ R := by simpa only [hx, hy] using hxy
        exact (hR h0).elim
      · simp only [torusDualEastNorth, torusDualNorthEast, torusDualSeamWord,
          seamStep, hx, hy, ite_true, ite_false, one_mul, mul_one]
    · simp only [torusDualEastNorth, torusDualNorthEast, torusDualSeamWord,
        seamStep, hx, ite_false, one_mul, mul_one]

/-- A square surrounding a forbidden origin has zero displacement but cannot
be contracted by square moves supported away from that origin. A noncommuting
pair in any test group supplies the nonabelian obstruction. No torus period
size assumption is required. Mathematical limitation of the restricted
interpretation of SCP10, Lemma 6.14. -/
theorem torusDualSquareLoop_obstructs_restricted_completeness
    (u v : G) (huv : u * v ≠ v * u) :
    let p := torusDualSquareLoop (-1 : ZMod width) (-1 : ZMod height)
    torusDualPathDisplacement p = 0 ∧
      ¬ TorusDualHomotopy {w : X | w ≠ (0, 0)} p .nil := by
  constructor
  · ext <;> simp [torusDualSquareLoop, TorusDualStep.displacement]
  · intro h
    have hs := h.seamWord_eq_of_origin_not_mem (by simp) u v
    have hc : u * v * u⁻¹ * v⁻¹ = 1 := by
      simpa only [torusDualSquareLoop, torusDualSeamWord, seamStep,
        neg_add_cancel, ite_true, one_mul] using hs
    apply huv
    calc
      u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by simp [mul_assoc]
      _ = v * u := by rw [hc, one_mul]

/-- The restricted contraction is impossible on every labelled torus. The
noncommuting test pair is constructed internally from two transpositions on
three elements, rather than supplied as a hypothesis. This is a geometric
obstruction, independent of any physical flux group. -/
theorem torusDualSquareLoop_not_homotopic_avoiding_origin :
    ¬ TorusDualHomotopy {w : X | w ≠ (0, 0)}
      (torusDualSquareLoop (-1 : ZMod width) (-1 : ZMod height)) .nil := by
  have h : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap (0 : Fin 3) 1 := by decide
  exact (torusDualSquareLoop_obstructs_restricted_completeness _ _ h).2

end TNLean.PEPS
