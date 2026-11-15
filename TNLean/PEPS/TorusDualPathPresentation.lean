/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualRectangle
import Mathlib.GroupTheory.PresentedGroup

/-!
# A finite presentation from native dual steps and allowed squares

Each positive east or north step is a free generator at its actual native
base vertex. Reverse steps use inverse letters. Words act in reverse path
order, as transports do. The relations are the finitely many allowed square
words and one word for each fixed route from the origin to a vertex.
These root routes fix the vertex coordinates of the groupoid presentation.

Source: SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214,
for the finite generated supported-homotopy interpretation. Both periods
are positive and the labelled steps remain distinct at periods one and two.
A finite presentation does not itself provide a terminating word algorithm.
See `docs/paper-gaps/scp10_dual_finite_presentation.tex`.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance presentationQuiver : Quiver X := torusDualQuiver width height

/-- The free letter of a labelled native step: east and north use the two
copies of the native vertex set, and reverse steps use inverse letters. -/
def torusDualStepWord {a b : X} : TorusDualStep a b → FreeGroup (X ⊕ X)
  | .east x y => FreeGroup.of (Sum.inl (x, y))
  | .west x y => (FreeGroup.of (Sum.inl (x, y)))⁻¹
  | .north x y => FreeGroup.of (Sum.inr (x, y))
  | .south x y => (FreeGroup.of (Sum.inr (x, y)))⁻¹

private theorem stepWord_reverse {a b : X} (e : TorusDualStep a b) :
    torusDualStepWord e.reverse = (torusDualStepWord e)⁻¹ := by
  cases e <;> simp [TorusDualStep.reverse, torusDualStepWord]

/-- The reverse-ordered free word of a finite labelled native dual path. -/
def torusDualPathWord {a : X} : {b : X} → TorusDualPath a b → FreeGroup (X ⊕ X)
  | _, .nil => 1
  | _, .cons p e => torusDualStepWord e * torusDualPathWord p

private theorem pathWord_comp {a b c : X} (p : TorusDualPath a b) (q : TorusDualPath b c) :
    torusDualPathWord (p.comp q) = torusDualPathWord q * torusDualPathWord p := by
  induction q with
  | nil => simp [torusDualPathWord]
  | cons q e ih => simp only [Quiver.Path.comp_cons, torusDualPathWord, ih, mul_assoc]

private theorem pathWord_reverse {a b : X} (p : TorusDualPath a b) :
    torusDualPathWord p.reverse = (torusDualPathWord p)⁻¹ := by
  induction p with
  | nil => simp only [Quiver.Path.reverse, torusDualPathWord, inv_one]
  | cons p e ih =>
    simp only [Quiver.Path.reverse, pathWord_comp, Quiver.Hom.toPath,
      torusDualPathWord, ih, mul_inv_rev, mul_one]
    change (torusDualPathWord p)⁻¹ * torusDualStepWord e.reverse = _
    rw [stepWord_reverse]

variable [NeZero width] [NeZero height]

/-- A fixed actual path from the origin to each native vertex, obtained from
the integer-coordinate comb. The origin is assigned the constant path. -/
def torusDualRootRoute (v : X) : TorusDualPath ((0, 0) : X) v := by
  by_cases hv : v = (0, 0)
  · subst v
    exact .nil
  · simpa only [torusRectCoord_eq, zero_add, ZMod.natCast_zmod_val] using
      torusRectComb (0 : ZMod width) (0 : ZMod height) v.1.val v.2.val

/-- The fixed origin route is the constant labelled path. -/
theorem torusDualRootRoute_zero :
    torusDualRootRoute ((0, 0) : X) = .nil := by
  simp [torusDualRootRoute]

/-- The local face relator at its lower-left dual vertex compares the two
positive east-north and north-east paths. Its primal support is one step
east and north from this native base vertex. -/
def torusDualFaceWord (v : X) : FreeGroup (X ⊕ X) :=
  torusDualPathWord (torusDualEastNorth v.1 v.2) *
    (torusDualPathWord (torusDualNorthEast v.1 v.2))⁻¹

/-- The finite defining relators: all fixed root-route words and the local
face words at exactly the allowed primal square-move supports. -/
def torusDualPresentationRelators (R : Finset X) : Finset (FreeGroup (X ⊕ X)) := by
  classical
  exact (Finset.univ.image fun v : X => torusDualPathWord (torusDualRootRoute v)) ∪
    (Finset.univ.filter fun v : X => (v.1 + 1, v.2 + 1) ∈ R).image torusDualFaceWord

/-- The presentation has at most twice as many defining relators as native
vertices. The generator type likewise consists of two copies of the vertices. -/
theorem card_torusDualPresentationRelators_le (R : Finset X) :
    (torusDualPresentationRelators R).card ≤ 2 * Fintype.card X := by
  classical
  unfold torusDualPresentationRelators
  calc
    _ ≤ (Finset.univ.image fun v : X => torusDualPathWord (torusDualRootRoute v)).card +
        ((Finset.univ.filter fun v : X => (v.1 + 1, v.2 + 1) ∈ R).image
          torusDualFaceWord).card := Finset.card_union_le _ _
    _ ≤ Fintype.card X + Fintype.card X := by
      exact Nat.add_le_add (by simpa only [Finset.card_univ] using
        (Finset.card_image_le (s := Finset.univ)
          (f := fun v : X => torusDualPathWord (torusDualRootRoute v))))
        (Finset.card_image_le.trans (by simpa only [Finset.card_univ] using
          (Finset.card_le_card (Finset.filter_subset
            (fun v : X => (v.1 + 1, v.2 + 1) ∈ R) Finset.univ))))
    _ = 2 * Fintype.card X := by omega

/-- Every generated supported homotopy preserves the image of the actual
native word in the finite presentation defined by the allowed squares.
No word equality is assumed. Source: SCP10, Lemma 6.14, generated moves. -/
theorem TorusDualHomotopy.presentation_word_eq {R : Finset X} {a b : X}
    {p q : TorusDualPath a b} (h : TorusDualHomotopy (R : Set X) p q) :
    PresentedGroup.mk (torusDualPresentationRelators R : Set (FreeGroup (X ⊕ X)))
        (torusDualPathWord p) =
      PresentedGroup.mk (torusDualPresentationRelators R : Set (FreeGroup (X ⊕ X)))
        (torusDualPathWord q) := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | comp h k ih ik => simp only [pathWord_comp, map_mul, ih, ik]
  | reverse h ih => simp only [pathWord_reverse, map_inv, ih]
  | backtrack e =>
    simp only [torusDualPathWord, stepWord_reverse, map_one,
      mul_one, inv_mul_cancel]
  | square x y hxy =>
    apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
    change _ ∈ torusDualPresentationRelators R
    have hm : torusDualFaceWord (x, y) ∈ torusDualPresentationRelators R := by
      classical
      unfold torusDualPresentationRelators
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩)
    exact hm

end TNLean.PEPS
