/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Simultaneous removal of repair squares

For a positive parent scale `S`, the removal square has half-side
`d(S) = 2 ^ ⌊ρ₀ * log₂ S⌋`. At each generation, every old actual region
loses the same union of these closed squares. Labels and remembered birth
regions retain their values at this step. Terminal squares are included
in the removal; replacement regions are created afterwards.

The definitions concern the removal step alone. The stopping threshold,
replacement sectors and geometric induction are separate assertions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:trim-radius`, lines 380–399,
  and `geometry:birth-separation`, lines 584–591.
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

/-- The union of the closed removal squares over a finite marked set with
assigned scales. This same union is removed from every old region.
Source: area-law Section 11, `geometry:trim-radius`, lines 393–399. -/
def repairRemovalSet (M : Finset (ℝ × ℝ)) (S : M → ℝ) : Set (ℝ × ℝ) :=
  ⋃ v : M, repairSquare v.val (S v)

/-- The remnants of every old actual region after simultaneous removal.
The old identifiers are retained; birth regions and labels retain their
values separately. Removal precedes the creation of replacement regions.
Source: area-law Section 11, `geometry:trim-radius`, lines 398–399, and
`geometry:birth-separation`, lines 584–591. -/
def simultaneousRepairRemnants {ι : Type*} (R : ι → Set (ℝ × ℝ))
    (M : Finset (ℝ × ℝ)) (S : M → ℝ) : ι → Set (ℝ × ℝ) :=
  fun i ↦ R i \ repairRemovalSet M S

end TNLean.PEPS.AreaLaw.Geometry
