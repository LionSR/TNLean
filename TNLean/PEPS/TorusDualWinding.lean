/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualHomotopy

/-!
# Winding obstruction to global dual-string deformation

The signed integer displacement of a dual path is invariant under the
specified elementary moves. Paths with the same torus endpoints can therefore
belong to distinct generated homotopy classes. This keeps the finite version
of SCP10, Lemma 6.14, separate from any claim about changing topological sectors.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance : Quiver X := torusDualQuiver width height

/-- The lifted integer displacement of one dual step. -/
def TorusDualStep.displacement {a b : X} : TorusDualStep a b → ℤ × ℤ
  | .east _ _ => (1, 0)
  | .west _ _ => (-1, 0)
  | .north _ _ => (0, 1)
  | .south _ _ => (0, -1)

@[simp]
theorem TorusDualStep.displacement_reverse {a b : X} (e : TorusDualStep a b) :
    e.reverse.displacement = -e.displacement := by cases e <;> rfl

/-- Total displacement in the integer cover, before taking periodic endpoints. -/
def torusDualPathDisplacement {a : X} : {b : X} → TorusDualPath a b → ℤ × ℤ
  | _, .nil => 0
  | _, .cons p e => torusDualPathDisplacement p + e.displacement

@[simp]
theorem torusDualPathDisplacement_nil (a : X) :
    torusDualPathDisplacement (.nil : TorusDualPath a a) = 0 := rfl

@[simp]
theorem torusDualPathDisplacement_cons {a b c : X} (p : TorusDualPath a b)
    (e : TorusDualStep b c) :
    torusDualPathDisplacement (p.cons e) = torusDualPathDisplacement p + e.displacement := rfl

@[simp]
theorem torusDualPathDisplacement_comp {a b c : X}
    (p : TorusDualPath a b) (q : TorusDualPath b c) :
    torusDualPathDisplacement (p.comp q) =
      torusDualPathDisplacement p + torusDualPathDisplacement q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, add_assoc]

@[simp]
theorem torusDualPathDisplacement_reverse {a b : X} (p : TorusDualPath a b) :
    torusDualPathDisplacement p.reverse = -torusDualPathDisplacement p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Quiver.Path.reverse, torusDualPathDisplacement_comp, Quiver.Hom.toPath,
      torusDualPathDisplacement_cons, torusDualPathDisplacement_nil, zero_add, ih]
    change e.reverse.displacement + -torusDualPathDisplacement p =
      -(torusDualPathDisplacement p + e.displacement)
    rw [TorusDualStep.displacement_reverse]
    abel

/-- Reducing one lifted displacement modulo the periods gives its actual
change of dual-plaquette coordinates. -/
theorem TorusDualStep.displacement_cast {a b : X} (e : TorusDualStep a b) :
    ((e.displacement.1 : ZMod width), (e.displacement.2 : ZMod height)) = b - a := by
  cases e <;> simp [displacement, Prod.sub_def]

/-- The lifted displacement reduces to the endpoint difference on the torus.
Together with homotopy invariance, this distinguishes endpoint data from winding. -/
theorem torusDualPathDisplacement_cast {a b : X} (p : TorusDualPath a b) :
    (((torusDualPathDisplacement p).1 : ZMod width),
      ((torusDualPathDisplacement p).2 : ZMod height)) = b - a := by
  induction p with
  | nil => simp
  | cons p e ih =>
    have he := e.displacement_cast
    apply Prod.ext
    · have hi := congrArg Prod.fst ih
      have hj := congrArg Prod.fst he
      simp only [Prod.fst_sub] at hi hj
      simp only [torusDualPathDisplacement_cons, Prod.fst_add, Int.cast_add, Prod.fst_sub]
      rw [hi, hj]
      abel
    · have hi := congrArg Prod.snd ih
      have hj := congrArg Prod.snd he
      simp only [Prod.snd_sub] at hi hj
      simp only [torusDualPathDisplacement_cons, Prod.snd_add, Int.cast_add, Prod.snd_sub]
      rw [hi, hj]
      abel

/-- Each generated homotopy preserves lifted integer displacement. On a torus,
this prevents equating arbitrary common-endpoint paths with different winding. -/
theorem TorusDualHomotopy.displacement_eq {R : Set X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy R p q) :
    torusDualPathDisplacement p = torusDualPathDisplacement q := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | comp h k ih ik => simp only [torusDualPathDisplacement_comp, ih, ik]
  | reverse h ih => simp only [torusDualPathDisplacement_reverse, ih]
  | backtrack e => simp
  | square x y h =>
    simp [torusDualEastNorth, torusDualNorthEast, TorusDualStep.displacement, add_comm]

end TNLean.PEPS
