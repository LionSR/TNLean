/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairReplacementRegions

/-!
# Sector identifiers chosen from the current regions

For each elementary working wedge, choose a current identifier whose open
region contains that wedge whenever such an identifier exists. The choice is
defined for every nonempty identifier set. Existence and uniqueness for the
actual current regions require the local coverage and frontier arguments.

The initial dummy identifier supplies nonemptiness. Subsequent region index
types retain every old identifier. Neither a global current cover nor coverage
by remembered birth regions is used: terminal interiors are unassigned, and
an ancestor birth can contain a descendant birth.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417,
and `geometry:repair-induction`, lines 471–514, especially 486–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The closed elementary triangle in the eight-triangle fan with center v
and positive half-side r. The interior of this whole triangle is the working
open wedge. Source: area-law Section 11, lines 404–417 and 506–514. -/
def repairCurrentFanTriangle (v : ℝ × ℝ) (r : ℝ) (s : RepairFanSlot) :
    Set (ℝ × ℝ) :=
  (fun x : ℝ × ℝ ↦ v + r • x) ''
    (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region

/-- The identifier whose current open region contains a working open wedge,
when such an identifier exists. The definition is total; it makes no claim
of existence or uniqueness. Those conclusions must be proved from the actual
local current family before this choice is used in a repair step.
Source: area-law Section 11, lines 404–407 and 486–514. -/
def repairCurrentSectorAssignment {ι : Type*} [Nonempty ι]
    (R : ι → Set (ℝ × ℝ)) (v : ℝ × ℝ) (r : ℝ) : RepairFanSlot → ι :=
  fun s ↦ Classical.epsilon fun i ↦ interior (repairCurrentFanTriangle v r s) ⊆ R i

/-- The current assignment at each parent is read in its working square of
half-side 6d(S). The repair margin puts that square inside the parent's
isolated star. This choice uses the current open regions before simultaneous
removal. Source: area-law Section 11, `geometry:repair-induction`, lines 486–494. -/
def repairCurrentAssignments {ι κ : Type*} [Nonempty ι]
    (R : ι → Set (ℝ × ℝ)) (v : κ → ℝ × ℝ) (S : κ → ℝ) :
    κ → RepairFanSlot → ι :=
  fun p ↦ repairCurrentSectorAssignment R (v p) (6 * repairHalfSide (S p))

end TNLean.PEPS.AreaLaw.Geometry
