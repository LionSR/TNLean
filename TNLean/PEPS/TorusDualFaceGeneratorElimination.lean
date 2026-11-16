/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualPathPresentation

/-!
# Elementary elimination of a native dual face generator

Solve the actual four-edge face word for its west or south edge. The resulting
free-group substitution preserves every representation in which that face
is flat. It kills the face relation when the corresponding transverse period
exceeds one and fixes every face not incident to the removed generator.

This is a local algebraic step toward a finite geometric normal form for
proper square supports. No ordering of faces, global classification, or
decision algorithm for general proper support is asserted here.

Source: the generated-move interpretation of SCP10, arXiv:1001.3807v3,
Lemma 6.14, lines 2199–2214. See
docs/paper-gaps/scp10_dual_face_generator_elimination.tex.
-/

namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height
local notation "FG" => FreeGroup (X ⊕ X)

private def eastLetter (v : X) : FG := FreeGroup.of (Sum.inl v)
private def northLetter (v : X) : FG := FreeGroup.of (Sum.inr v)

private def westReplacement (v : X) : FG :=
  (eastLetter (v.1, v.2 + 1))⁻¹ * northLetter (v.1 + 1, v.2) * eastLetter v

private def southReplacement (v : X) : FG :=
  (northLetter (v.1 + 1, v.2))⁻¹ * eastLetter (v.1, v.2 + 1) * northLetter v

/-- Replace the west edge generator of the actual dual face based at v
by the other three sides. All other native generators remain fixed. -/
def torusDualWestFaceElimination (v : X) : FG →* FG :=
  FreeGroup.lift fun a => if a = Sum.inr v then westReplacement v else FreeGroup.of a

/-- Replace the south edge generator of the actual dual face based at v
by the other three sides. All other native generators remain fixed. -/
def torusDualSouthFaceElimination (v : X) : FG →* FG :=
  FreeGroup.lift fun a => if a = Sum.inl v then southReplacement v else FreeGroup.of a

/-- Compose a finite list of native face substitutions. A true tag selects
the west edge and a false tag the south edge; the tail acts after the head. -/
def torusDualFaceEliminationSequence : List (X × Bool) → (FG →* FG)
  | [] => MonoidHom.id _
  | (v, b) :: l => (torusDualFaceEliminationSequence l).comp
      (if b then torusDualWestFaceElimination v else torusDualSouthFaceElimination v)

private theorem faceWord_eq (v : X) :
    torusDualFaceWord v =
      northLetter (v.1 + 1, v.2) * eastLetter v *
        (northLetter v)⁻¹ * (eastLetter (v.1, v.2 + 1))⁻¹ := by
  simp [torusDualFaceWord, torusDualPathWord, torusDualEastNorth,
    torusDualNorthEast, torusDualStepWord, eastLetter, northLetter, mul_assoc]

private theorem right_ne [Fact (1 < width)] (v : X) : (v.1 + 1, v.2) ≠ v := by
  intro h
  have h1 : (1 : ZMod width) = 0 := by
    simpa only [add_eq_left] using congrArg Prod.fst h
  exact one_ne_zero h1

private theorem up_ne [Fact (1 < height)] (v : X) : (v.1, v.2 + 1) ≠ v := by
  intro h
  have h1 : (1 : ZMod height) = 0 := by
    simpa only [add_eq_left] using congrArg Prod.snd h
  exact one_ne_zero h1

/-- West-edge substitution kills the actual face relator when the horizontal
period exceeds one, so its two north-edge generators are distinct. -/
theorem torusDualWestFaceElimination_face
    [NeZero width] [NeZero height]
    [Fact (1 < width)] (v : X) :
    torusDualWestFaceElimination v (torusDualFaceWord v) = 1 := by
  rw [faceWord_eq]
  simp [torusDualWestFaceElimination, eastLetter, northLetter,
    right_ne v, westReplacement, mul_assoc]

/-- South-edge substitution kills the actual face relator when the vertical
period exceeds one, so its two east-edge generators are distinct. -/
theorem torusDualSouthFaceElimination_face
    [NeZero width] [NeZero height]
    [Fact (1 < height)] (v : X) :
    torusDualSouthFaceElimination v (torusDualFaceWord v) = 1 := by
  rw [faceWord_eq]
  simp [torusDualSouthFaceElimination, eastLetter, northLetter,
    up_ne v, southReplacement, mul_assoc]

/-- Every other face not using the removed west generator is fixed.
The two excluded bases are precisely this face and its west neighbour. -/
theorem torusDualWestFaceElimination_face_eq
    [NeZero width] [NeZero height]
    (v w : X)
    (hw : w ≠ v) (hwr : (w.1 + 1, w.2) ≠ v) :
    torusDualWestFaceElimination v (torusDualFaceWord w) = torusDualFaceWord w := by
  simp [faceWord_eq, torusDualWestFaceElimination, eastLetter, northLetter, hw, hwr]

/-- Every other face not using the removed south generator is fixed.
The two excluded bases are precisely this face and its south neighbour. -/
theorem torusDualSouthFaceElimination_face_eq
    [NeZero width] [NeZero height]
    (v w : X)
    (hw : w ≠ v) (hwu : (w.1, w.2 + 1) ≠ v) :
    torusDualSouthFaceElimination v (torusDualFaceWord w) = torusDualFaceWord w := by
  simp [faceWord_eq, torusDualSouthFaceElimination, eastLetter, northLetter, hw, hwu]

variable {H : Type*} [Group H]

private theorem flat_face_equation
    [NeZero width] [NeZero height]
    (φ : FG →* H) (v : X)
    (h : φ (torusDualFaceWord v) = 1) :
    φ (northLetter (v.1 + 1, v.2)) * φ (eastLetter v) =
      φ (eastLetter (v.1, v.2 + 1)) * φ (northLetter v) := by
  rw [faceWord_eq, map_mul, map_mul, map_mul, map_inv, map_inv] at h
  have he := congrArg
    (fun z => z * φ (eastLetter (v.1, v.2 + 1)) * φ (northLetter v)) h
  simpa [mul_assoc] using he

/-- A representation flat on the selected native face is unchanged by its
west-edge substitution. No commutativity or finite-group hypothesis is used. -/
theorem torusDualWestFaceElimination_preserves_flatRepresentation
    [NeZero width] [NeZero height]
    (φ : FG →* H) (v : X) (h : φ (torusDualFaceWord v) = 1) :
    φ.comp (torusDualWestFaceElimination v) = φ := by
  have he := flat_face_equation φ v h
  have hp : φ (westReplacement v) = φ (northLetter v) := by
    simp only [westReplacement, map_mul, map_inv]
    calc
      (φ (eastLetter (v.1, v.2 + 1)))⁻¹ *
          φ (northLetter (v.1 + 1, v.2)) * φ (eastLetter v) =
        (φ (eastLetter (v.1, v.2 + 1)))⁻¹ *
          (φ (northLetter (v.1 + 1, v.2)) * φ (eastLetter v)) := mul_assoc _ _ _
      _ = (φ (eastLetter (v.1, v.2 + 1)))⁻¹ *
          (φ (eastLetter (v.1, v.2 + 1)) * φ (northLetter v)) := by rw [he]
      _ = φ (northLetter v) := by simp
  apply FreeGroup.ext_hom
  intro a
  by_cases ha : a = Sum.inr v
  · subst a
    simpa only [MonoidHom.comp_apply, torusDualWestFaceElimination,
      FreeGroup.lift_apply_of, ite_true, northLetter] using hp
  · simp [MonoidHom.comp_apply, torusDualWestFaceElimination, ha]

/-- A representation flat on the selected native face is unchanged by its
south-edge substitution. No commutativity or finite-group hypothesis is used. -/
theorem torusDualSouthFaceElimination_preserves_flatRepresentation
    [NeZero width] [NeZero height]
    (φ : FG →* H) (v : X) (h : φ (torusDualFaceWord v) = 1) :
    φ.comp (torusDualSouthFaceElimination v) = φ := by
  have he := flat_face_equation φ v h
  have hp : φ (southReplacement v) = φ (eastLetter v) := by
    simp only [southReplacement, map_mul, map_inv]
    calc
      (φ (northLetter (v.1 + 1, v.2)))⁻¹ *
          φ (eastLetter (v.1, v.2 + 1)) * φ (northLetter v) =
        (φ (northLetter (v.1 + 1, v.2)))⁻¹ *
          (φ (eastLetter (v.1, v.2 + 1)) * φ (northLetter v)) := mul_assoc _ _ _
      _ = (φ (northLetter (v.1 + 1, v.2)))⁻¹ *
          (φ (northLetter (v.1 + 1, v.2)) * φ (eastLetter v)) := by rw [he]
      _ = φ (eastLetter v) := by simp
  apply FreeGroup.ext_hom
  intro a
  by_cases ha : a = Sum.inl v
  · subst a
    simpa only [MonoidHom.comp_apply, torusDualSouthFaceElimination,
      FreeGroup.lift_apply_of, ite_true, eastLetter] using hp
  · simp [MonoidHom.comp_apply, torusDualSouthFaceElimination, ha]

/-- Any finite composition of selected face substitutions preserves every
representation flat on those original native faces. No order is assumed. -/
theorem torusDualFaceEliminationSequence_preserves_flatRepresentation
    [NeZero width] [NeZero height]
    (φ : FG →* H) (l : List (X × Bool))
    (h : ∀ d ∈ l, φ (torusDualFaceWord d.1) = 1) :
    φ.comp (torusDualFaceEliminationSequence l) = φ := by
  revert h
  induction l with
  | nil =>
    intro _
    rfl
  | cons d l ih =>
    intro h
    obtain ⟨v, b⟩ := d
    have hh : φ (torusDualFaceWord v) = 1 := h (v, b) (by simp)
    have ht := ih (fun d hd => h d (by simp only [List.mem_cons]; exact Or.inr hd))
    have hs : φ.comp
        (if b then torusDualWestFaceElimination v else torusDualSouthFaceElimination v) =
          φ := by
      cases b
      · exact torusDualSouthFaceElimination_preserves_flatRepresentation φ v hh
      · exact torusDualWestFaceElimination_preserves_flatRepresentation φ v hh
    apply MonoidHom.ext
    intro z
    have ht' := congrArg (fun f : FG →* H => f
      ((if b then torusDualWestFaceElimination v else torusDualSouthFaceElimination v) z)) ht
    have hs' := congrArg (fun f : FG →* H => f z) hs
    exact ht'.trans hs'

end TNLean.PEPS
