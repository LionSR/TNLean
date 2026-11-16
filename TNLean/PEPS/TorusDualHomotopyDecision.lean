/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualComputedFacePlan
import TNLean.PEPS.TorusDualEmptySupportNormalForm
import TNLean.PEPS.TorusDualHomotopyClassification

/-!
# Executable homotopy decisions for every finite native square support

For full support, compare lifted integer displacements. For proper support,
compute a checked finite face-elimination plan and compare the reduced images
of the actual labelled edge words. The correctness theorem covers all finite
supports and all parallel finite paths on positive-period native tori,
including periods one and two.

The bounded fallback search may be exponential. No word-problem oracle,
supplied plan, endpoint-only classification, or physical density conclusion
is assumed or asserted.

Source: the generated-move interpretation of SCP10, arXiv:1001.3807v3,
Lemma 6.14, lines 2199–2214. See the accompanying paper-gap note.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height
local instance homotopyDecisionQuiver : Quiver X := torusDualQuiver width height

/-- Decide generated homotopy for any finite allowed square support on a
positive-period native torus. The definition computes only finite support
checks, displacement sums, face substitutions, and free-word reductions. -/
def torusDualHomotopyDecision (R : Finset X) {a b : X}
    (p q : TorusDualPath a b) : Bool :=
  if R = Finset.univ then
    decide (torusDualPathDisplacement p = torusDualPathDisplacement q)
  else
    let Φ := torusDualFaceEliminationSequence (torusDualComputedFacePlan R)
    decide ((Φ (FreeGroup.mk (torusDualPathLetters p))).toWord =
      (Φ (FreeGroup.mk (torusDualPathLetters q))).toWord)

/-- The computable Boolean procedure decides the actual relation generated
by backtracks and allowed native square moves, for every finite support.
The paths have common endpoints; winding and missing-face obstructions
are retained by the computed invariant. -/
theorem torusDualHomotopyDecision_eq_true (R : Finset X) {a b : X}
    (p q : TorusDualPath a b) :
    torusDualHomotopyDecision R p q = true ↔ TorusDualHomotopy (R : Set X) p q := by
  by_cases hR : R = Finset.univ
  · subst R
    simp only [torusDualHomotopyDecision, if_pos rfl, decide_eq_true_eq, Finset.coe_univ]
    exact (torusDualHomotopy_univ_iff_displacement_eq p q).symm
  · obtain ⟨_, hm, hf⟩ := torusDualComputedFacePlan_spec R hR
    simp only [torusDualHomotopyDecision, if_neg hR, decide_eq_true_eq,
      torusDualPathLetters_word]
    exact ((torusDualHomotopy_iff_faceElimination_word_eq R
      (torusDualComputedFacePlan R) hm hf p q).trans FreeGroup.toWord_inj.symm).symm

end TNLean.PEPS
