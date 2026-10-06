import TNLean.PEPS.TorusDualRectangleFlux
import TNLean.PEPS.TorusDualWinding

/-! Regressions for the finite embedded rectangular case of SCP10 Lemma 6.14.
The first two examples include reverse steps and nontrivial detours. -/
namespace TNLean.PEPS

local instance : Quiver (ℕ × ℕ) := rectDualQuiver 2 2
local instance : Quiver (TorusVertex 5 5) := torusDualQuiver 5 5

private def patch : TorusDualRectangle 5 5 := ⟨(4, 4), 2, 2, by decide, by decide⟩

private def detour : Quiver.Path (0, 0) (1, 0) :=
  (((Quiver.Path.nil.cons (RectDualStep.north 0 0 (by decide) (by decide))).cons
    (RectDualStep.east 0 1 (by decide) (by decide))).cons
      (RectDualStep.south 1 0 (by decide) (by decide)))

private def straight : Quiver.Path (0, 0) (1, 0) :=
  Quiver.Path.nil.cons (RectDualStep.east 0 0 (by decide) (by decide))

example : TorusDualHomotopy (torusRectInterior (4 : ZMod 5) (4 : ZMod 5) 2 2)
    (rectDualPathToTorus (4 : ZMod 5) (4 : ZMod 5) detour)
    (rectDualPathToTorus (4 : ZMod 5) (4 : ZMod 5) straight) :=
  patch.homotopy detour straight

example : TorusDualHomotopy (torusRectInterior (0 : ZMod 5) (0 : ZMod 5) 2 2)
    (rectDualPathToTorus (0 : ZMod 5) (0 : ZMod 5)
      (straight.cons (RectDualStep.west 0 0 (by decide) (by decide))))
    Quiver.Path.nil :=
  rectDualPath_homotopy _ _ _ Quiver.Path.nil

-- Start away from the comb root: the proof must cancel a nonempty prefix.
private def reverseDetour : Quiver.Path (1, 1) (0, 1) :=
  (((Quiver.Path.nil.cons (RectDualStep.south 1 0 (by decide) (by decide))).cons
    (RectDualStep.west 0 0 (by decide) (by decide))).cons
      (RectDualStep.north 0 0 (by decide) (by decide)))

example : TorusDualHomotopy (torusRectInterior (4 : ZMod 5) (4 : ZMod 5) 2 2)
    (rectDualPathToTorus (4 : ZMod 5) (4 : ZMod 5) reverseDetour)
    (rectDualPathToTorus (4 : ZMod 5) (4 : ZMod 5)
      (Quiver.Path.nil.cons (RectDualStep.west 0 1 (by decide) (by decide)))) :=
  patch.homotopy reverseDetour _

example (P : TorusDualRectangle 5 5) {a b : ℕ × ℕ}
    (p q : @Quiver.Path (ℕ × ℕ) (rectDualQuiver P.cols P.rows) a b) :
    torusDualPathDisplacement (rectDualPathToTorus P.origin.1 P.origin.2 p) =
      torusDualPathDisplacement (rectDualPathToTorus P.origin.1 P.origin.2 q) :=
  (P.homotopy p q).displacement_eq

-- Width zero is a legitimate one-column patch.
example : TorusDualRectangle 1 3 := ⟨(0, 0), 0, 2, by decide, by decide⟩

-- A full period is not an embedded closed interval.
example : ¬ ∃ P : TorusDualRectangle 2 3, P.cols = 2 := by
  rintro ⟨P, h⟩
  have := P.cols_lt
  omega

#print axioms torusRectColumn_east
#print axioms RectDualStep.comb
#print axioms rectDualPath_homotopy
#print axioms TorusDualRectangle.injective
#print axioms TorusDualRectangle.homotopy
#print axioms TorusDualRectangle.torusBondNetwork_eq_with_exterior

end TNLean.PEPS
