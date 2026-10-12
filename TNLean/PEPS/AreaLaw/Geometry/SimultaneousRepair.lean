/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Removal squares and repair children

For a positive parent scale `S`, the removal square has half-side
`d(S) = 2 ^ ⌊ρ₀ * log₂ S⌋`. At each generation, every old actual region
loses the same union of these closed squares. Labels and remembered birth
regions retain their values at this step. Terminal squares are included
in the removal; replacement regions are created afterwards.

A parent contributes children when its removal half-side is at least the
stopping threshold. Their locations are the center, corners and side
midpoints of its removal square; their assigned scale is that half-side.
The child index retains the parent and the offset. Child-star preservation,
replacement sectors and geometric induction are separate assertions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:trim-radius`, lines 380–399,
  replacement instructions, lines 401–409, `geometry:repair-induction`,
  lines 506–524 and 538–541, and `geometry:birth-separation`, lines 584–591.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The dyadic removal half-side `d(S) = 2 ^ ⌊ρ₀ * log₂ S⌋`, used at
positive parent scales. The floor and the exponent are integers.
Source: area-law Section 11, `geometry:trim-radius`, lines 380–385. -/
def repairHalfSide (S : ℝ) : ℝ :=
  (2 : ℝ) ^ (⌊(Exponents.rho : ℝ) * Real.logb 2 S⌋ : ℤ)

/-- The closed removal square about a mark at its assigned parent scale.
The product metric is the maximum of the two coordinate distances.
Source: area-law Section 11, `geometry:trim-radius`, lines 398–399. -/
def repairSquare (v : ℝ × ℝ) (S : ℝ) : Set (ℝ × ℝ) :=
  Metric.closedBall v (repairHalfSide S)

/-- The union of the closed removal squares over a family of mark occurrences,
each with a location `v j` and an assigned scale `S j`. This same union is
removed from every old region. Occurrences are indexed separately from their
locations, so coincident marks with different scales each contribute a square.
Source: area-law Section 11, `geometry:trim-radius`, lines 393–399. -/
def repairRemovalSet {κ : Type*} (v : κ → ℝ × ℝ) (S : κ → ℝ) : Set (ℝ × ℝ) :=
  ⋃ j, repairSquare (v j) (S j)

/-- The remnants of every old actual region after simultaneous removal.
The old identifiers are retained; birth regions and labels retain their
values separately. Removal precedes the creation of replacement regions.
Source: area-law Section 11, `geometry:trim-radius`, lines 398–399, and
`geometry:birth-separation`, lines 584–591. -/
def simultaneousRepairRemnants {ι κ : Type*} (R : ι → Set (ℝ × ℝ))
    (v : κ → ℝ × ℝ) (S : κ → ℝ) : ι → Set (ℝ × ℝ) :=
  fun i ↦ R i \ repairRemovalSet v S

/-- The nine centered offsets, with each coordinate in `{-1, 0, 1}`.
The `Fin 3 × Fin 3` indexing agrees with the existing belt-cell marks.
Source: area-law Section 11, `geometry:repair-induction`, lines 506–512. -/
def repairChildOffset (p : Fin 3 × Fin 3) : ℝ × ℝ :=
  ((p.1.val : ℝ) - 1, (p.2.val : ℝ) - 1)

/-- The child occurrences in the next generation: a nonterminal current
parent together with one of the nine offsets. A terminal cut has no child.
Source: area-law Section 11, lines 401–409, and
`geometry:repair-induction`, lines 538–541. -/
abbrev RepairChildIndex {ι : Type*} (S : ι → ℝ) (Sstar : ℝ) :=
  {i : ι // Sstar ≤ repairHalfSide (S i)} × (Fin 3 × Fin 3)

/-- A child's location is its parent location plus the computed removal
half-side times its centered offset.
Source: area-law Section 11, lines 404–409, and
`geometry:repair-induction`, lines 506–512. -/
def repairChildLocation {ι : Type*} (v : ι → ℝ × ℝ) (S : ι → ℝ)
    (Sstar : ℝ) (j : RepairChildIndex S Sstar) : ℝ × ℝ :=
  v j.1.val + repairHalfSide (S j.1.val) • repairChildOffset j.2

/-- Every child of a nonterminal parent has scale equal to that parent's
computed removal half-side.
Source: area-law Section 11, lines 404–409, and
`geometry:repair-induction`, lines 506–512. -/
def repairChildScale {ι : Type*} (S : ι → ℝ) (Sstar : ℝ)
    (j : RepairChildIndex S Sstar) : ℝ :=
  repairHalfSide (S j.1.val)

end TNLean.PEPS.AreaLaw.Geometry
