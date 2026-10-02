/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusRegionLiftGauge
import TNLean.PEPS.TorusWalkWinding

/-!
# Crossing numbers of projected integer unit steps

An integer lattice point records its deck coordinate by Euclidean division by
the two torus periods. For a projected horizontal or vertical unit step, the
change in this coordinate is exactly its oriented seam crossing number. This
applies equally to internal, boundary, and exterior steps.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, seam deformation and
the complement argument, local source lines 1622–1647 and 1935–1990.

**Scope restriction (simple torus graph):** Width and height are at least
three, as recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS

/-- The integer deck coordinate relative to the two torus periods.
Source: SCP10, native torus seam deformation, lines 1622–1647. -/
def torusIntegerDeckCoordinate (width height : ℕ) (a : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 / (width : ℤ), a.2 / (height : ℤ))

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

private theorem winding_right_integer (a : ℤ × ℤ) :
    torusDirectedWinding (torusGraph_adj_right (a.1 : ZMod width) (a.2 : ZMod height)) =
      torusIntegerDeckCoordinate width height (a + (1, 0)) -
        torusIntegerDeckCoordinate width height a := by
  rw [torusDirectedWinding_right (width := width) (height := height)
    ((a.1 : ZMod width), (a.2 : ZMod height))]
  have hd := int_ediv_step_eq_add_seam_indicator a.1 (a.1 : ZMod width) rfl
  apply Prod.ext <;> simp [torusIntegerDeckCoordinate, hd]

private theorem winding_up_integer (a : ℤ × ℤ) :
    torusDirectedWinding (torusGraph_adj_up (a.1 : ZMod width) (a.2 : ZMod height)) =
      torusIntegerDeckCoordinate width height (a + (0, 1)) -
        torusIntegerDeckCoordinate width height a := by
  rw [torusDirectedWinding_up (width := width) (height := height)
    ((a.1 : ZMod width), (a.2 : ZMod height))]
  have hd := int_ediv_step_eq_add_seam_indicator a.2 (a.2 : ZMod height) rfl
  apply Prod.ext <;> simp [torusIntegerDeckCoordinate, hd]

/-- Projecting an integer unit step gives exactly the difference of its
endpoint deck coordinates as its seam crossing numbers. No region or path
condition is required. Source: SCP10, complement geometry, lines 1935–1990. -/
theorem torusDirectedWinding_eq_of_integerUnitStep (a b : ℤ × ℤ)
    (hab : a + (1, 0) = b ∨ a = b + (1, 0) ∨
      a + (0, 1) = b ∨ a = b + (0, 1))
    (h : (torusGraph width height).Adj
      ((a.1 : ZMod width), (a.2 : ZMod height))
      ((b.1 : ZMod width), (b.2 : ZMod height))) :
    torusDirectedWinding h = torusIntegerDeckCoordinate width height b -
      torusIntegerDeckCoordinate width height a := by
  rcases hab with he | he | he | he
  · subst b
    simpa only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, add_zero] using
      winding_right_integer (width := width) (height := height) a
  · subst a
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, add_zero] at h ⊢
    change torusDirectedWinding (torusGraph_adj_right (b.1 : ZMod width)
      (b.2 : ZMod height)).symm = _
    rw [torusDirectedWinding_symm (torusGraph_adj_right (b.1 : ZMod width)
      (b.2 : ZMod height)), winding_right_integer]
    abel
  · subst b
    simpa only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, add_zero] using
      winding_up_integer (width := width) (height := height) a
  · subst a
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, add_zero] at h ⊢
    change torusDirectedWinding (torusGraph_adj_up (b.1 : ZMod width)
      (b.2 : ZMod height)).symm = _
    rw [torusDirectedWinding_symm (torusGraph_adj_up (b.1 : ZMod width)
      (b.2 : ZMod height)), winding_up_integer]
    abel

end TNLean.PEPS
