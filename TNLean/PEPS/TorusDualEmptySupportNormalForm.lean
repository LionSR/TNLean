/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualPresentationCompleteness
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Reduced-word classification when no square moves are permitted

Record the actual base vertex and direction of every native dual edge, in
reverse traversal order, and cancel adjacent inverse letters. For positive
torus periods, two parallel paths are homotopic using only backtracks exactly
when their reduced words agree. The Boolean decision procedure computes
only a finite list reduction; no quotient-word oracle is supplied.

Source: the generated-move interpretation of SCP10, arXiv:1001.3807v3,
Lemma 6.14, lines 2199–2214. The empty square-support restriction is explicit.
Periods one and two retain their separate edge labels. This does not decide
homotopy for arbitrary proper nonempty support or identify paths by endpoints.
See docs/paper-gaps/scp10_dual_empty_support_normal_form.tex.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local instance emptySupportQuiver : Quiver X := torusDualQuiver width height

/-- A signed native edge letter, retaining its positive edge's actual base vertex. -/
def torusDualStepLetter {a b : X} : TorusDualStep a b → (X ⊕ X) × Bool
  | .east x y => (Sum.inl (x, y), true)
  | .west x y => (Sum.inl (x, y), false)
  | .north x y => (Sum.inr (x, y), true)
  | .south x y => (Sum.inr (x, y), false)

/-- The finite list of signed native letters in reverse traversal order. -/
def torusDualPathLetters {a : X} :
    {b : X} → TorusDualPath a b → List ((X ⊕ X) × Bool)
  | _, .nil => []
  | _, .cons p e => torusDualStepLetter e :: torusDualPathLetters p

/-- Cancel adjacent inverse native edge letters using Mathlib's free-word reduction. -/
def torusDualReducedWord {a b : X} (p : TorusDualPath a b) :
    List ((X ⊕ X) × Bool) :=
  FreeGroup.reduce (torusDualPathLetters p)

/-- A Boolean algorithm comparing finite native reduced words. Its homotopy
interpretation below requires positive periods and empty square support. -/
def torusDualEmptyHomotopyDecision {a b : X} (p q : TorusDualPath a b) : Bool :=
  decide (torusDualReducedWord p = torusDualReducedWord q)

private theorem stepLetter_word {a b : X} (e : TorusDualStep a b) :
    FreeGroup.mk [torusDualStepLetter e] = torusDualStepWord e := by
  cases e <;> simp [torusDualStepLetter, torusDualStepWord, FreeGroup.of,
    FreeGroup.inv_mk, FreeGroup.invRev]

/-- Interpreting the computable native letter list gives the actual free-group path word. -/
theorem torusDualPathLetters_word {a b : X} (p : TorusDualPath a b) :
    FreeGroup.mk (torusDualPathLetters p) = torusDualPathWord p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change FreeGroup.mk ([torusDualStepLetter e] ++ torusDualPathLetters p) =
      torusDualStepWord e * torusDualPathWord p
    rw [← FreeGroup.mul_mk, stepLetter_word, ih]

private theorem reducedWord_eq_toWord {a b : X} (p : TorusDualPath a b) :
    torusDualReducedWord p = (torusDualPathWord p).toWord := by
  change (FreeGroup.mk (torusDualPathLetters p)).toWord = _
  rw [torusDualPathLetters_word]

private theorem stepWord_reverse {a b : X} (e : TorusDualStep a b) :
    torusDualStepWord e.reverse = (torusDualStepWord e)⁻¹ := by
  cases e <;> simp [TorusDualStep.reverse, torusDualStepWord]

private noncomputable def freeWordTransport :
    TorusDualFlatTransport (∅ : Set (TorusVertex width height))
      (fun _ => FreeGroup (X ⊕ X)) where
  step e z := torusDualStepWord e * z
  reverse_step e z := by
    rw [stepWord_reverse, ← mul_assoc, inv_mul_cancel, one_mul]
  square _ _ h := False.elim h

private theorem freeWordTransport_eval {a b : X}
    (p : TorusDualPath a b) (z : FreeGroup (X ⊕ X)) :
    freeWordTransport.eval p z = torusDualPathWord p * z := by
  induction p with
  | nil => exact (one_mul z).symm
  | cons p e ih =>
    change torusDualStepWord e * freeWordTransport.eval p z =
      (torusDualStepWord e * torusDualPathWord p) * z
    rw [ih, mul_assoc]

variable [NeZero width] [NeZero height]

/-- Equal reduced native edge words imply generated homotopy for any allowed
square support. The finite-presentation criterion supplies completeness. -/
theorem torusDualHomotopy_of_reducedWord_eq (R : Finset X) {a b : X}
    (p q : TorusDualPath a b) (h : torusDualReducedWord p = torusDualReducedWord q) :
    TorusDualHomotopy (R : Set X) p q := by
  have hw : torusDualPathWord p = torusDualPathWord q := by
    apply FreeGroup.toWord_injective
    simpa only [reducedWord_eq_toWord] using h
  apply (torusDualHomotopy_iff_presentation_word_eq R p q).mpr
  exact congrArg
    (PresentedGroup.mk (torusDualPresentationRelators R : Set (FreeGroup (X ⊕ X)))) hw

/-- With no allowed square supports, finite native parallel paths are
generated-homotopic exactly when their actual reduced edge words agree.
No word equality or homotopy witness is supplied in either direction. -/
theorem torusDualHomotopy_empty_iff_reducedWord_eq {a b : X}
    (p q : TorusDualPath a b) :
    TorusDualHomotopy (∅ : Set X) p q ↔
      torusDualReducedWord p = torusDualReducedWord q := by
  constructor
  · intro h
    have ht := h.flatTransport_eval_eq freeWordTransport (1 : FreeGroup (X ⊕ X))
    have hw : torusDualPathWord p = torusDualPathWord q := by
      simpa only [freeWordTransport_eval, mul_one] using ht
    simp only [reducedWord_eq_toWord, hw]
  · intro h
    simpa only [Finset.coe_empty] using torusDualHomotopy_of_reducedWord_eq ∅ p q h

/-- The finite-list Boolean procedure decides actual empty-support homotopy
on a native torus with positive periods, including periods one and two. -/
theorem torusDualEmptyHomotopyDecision_eq_true {a b : X}
    (p q : TorusDualPath a b) :
    torusDualEmptyHomotopyDecision p q = true ↔
      TorusDualHomotopy (∅ : Set X) p q := by
  simp only [torusDualEmptyHomotopyDecision, decide_eq_true_eq]
  exact (torusDualHomotopy_empty_iff_reducedWord_eq p q).symm

end TNLean.PEPS
