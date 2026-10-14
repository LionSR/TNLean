/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

The half-side satisfies `S ^ ρ₀ / 2 ≤ d(S) ≤ S ^ ρ₀` at every positive
scale, `d(S) < S` when `S > 1`, and `d(S) ≤ (a₀ / 1000) S` for all
sufficiently large `S`, for every positive constant `a₀`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:trim-radius`, lines 380–399,
  `geometry:trim-margins`, lines 386–391,
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

/-- The real exponent `ρ₀` lies strictly between zero and one.
Source: area-law Section 11, `geometry:exponents` and `geometry:exponent-gaps`. -/
theorem rho_pos_lt_one : 0 < (Exponents.rho : ℝ) ∧ (Exponents.rho : ℝ) < 1 := by
  constructor <;> norm_num [Exponents.rho, Exponents.beta, Exponents.boxError]

/-- At a positive scale, the power `S ^ ρ₀` equals `2 ^ (ρ₀ log₂ S)`. -/
private theorem rpow_rho_eq_two_rpow {S : ℝ} (hS : 0 < S) :
    S ^ (Exponents.rho : ℝ) = (2 : ℝ) ^ ((Exponents.rho : ℝ) * Real.logb 2 S) := by
  conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hS]
  rw [← Real.rpow_mul (by norm_num), mul_comm]

/-- The removal half-side is at most `S ^ ρ₀` at every positive scale.
Source: area-law Section 11, `geometry:trim-margins`, lines 386–391. -/
theorem repairHalfSide_le_rpow {S : ℝ} (hS : 0 < S) :
    repairHalfSide S ≤ S ^ (Exponents.rho : ℝ) := by
  rw [rpow_rho_eq_two_rpow hS, repairHalfSide, ← Real.rpow_intCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)

/-- The removal half-side is at least `S ^ ρ₀ / 2` at every positive scale.
Source: area-law Section 11, `geometry:trim-margins`, lines 386–391. -/
theorem half_rpow_le_repairHalfSide {S : ℝ} (hS : 0 < S) :
    1 / 2 * S ^ (Exponents.rho : ℝ) ≤ repairHalfSide S := by
  set x := (Exponents.rho : ℝ) * Real.logb 2 S
  have h : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((⌊x⌋ : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.lt_floor_add_one x).le
  rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_intCast] at h
  rw [rpow_rho_eq_two_rpow hS, repairHalfSide]
  linarith

/-- The removal half-side is strictly smaller than every scale `S > 1`.
Source: area-law Section 11, `geometry:trim-radius` and `geometry:trim-margins`,
lines 380–391, with `ρ₀ < 1` from `geometry:exponent-gaps`. -/
theorem repairHalfSide_lt_self {S : ℝ} (hS : 1 < S) : repairHalfSide S < S := by
  calc repairHalfSide S ≤ S ^ (Exponents.rho : ℝ) := repairHalfSide_le_rpow (by linarith)
    _ < S ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hS rho_pos_lt_one.2
    _ = S := Real.rpow_one S

/-- For every positive constant `a₀`, the removal half-side is eventually at
most `(a₀ / 1000) S`.
Source: area-law Section 11, `geometry:trim-margins`, lines 386–391. -/
theorem eventually_repairHalfSide_le {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ S in Filter.atTop, repairHalfSide S ≤ a₀ / 1000 * S := by
  have hlim : Filter.Tendsto (fun S : ℝ ↦ S ^ (-(1 - (Exponents.rho : ℝ))))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith [rho_pos_lt_one.2])
  filter_upwards [hlim.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < a₀ / 1000)),
    Filter.eventually_gt_atTop 0] with S hle hS
  have hsplit : S ^ (Exponents.rho : ℝ) = S ^ (-(1 - (Exponents.rho : ℝ))) * S := by
    rw [neg_sub, Real.rpow_sub_one hS.ne', div_mul_cancel₀ _ hS.ne']
  calc repairHalfSide S ≤ S ^ (Exponents.rho : ℝ) := repairHalfSide_le_rpow hS
    _ ≤ a₀ / 1000 * S := by rw [hsplit]; exact mul_le_mul_of_nonneg_right hle hS.le

/-- For every positive constant `a₀`, all sufficiently large scales satisfy the
three removal margins `S ^ ρ₀ / 2 ≤ d(S) ≤ S ^ ρ₀` and `d(S) ≤ (a₀ / 1000) S`;
a stopping scale `S_*` may be taken as large as required.
Source: area-law Section 11, `geometry:trim-margins`, lines 380–391. -/
theorem eventually_repairHalfSide_margins {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ S in Filter.atTop, 1 / 2 * S ^ (Exponents.rho : ℝ) ≤ repairHalfSide S ∧
      repairHalfSide S ≤ S ^ (Exponents.rho : ℝ) ∧ repairHalfSide S ≤ a₀ / 1000 * S := by
  filter_upwards [eventually_repairHalfSide_le ha₀, Filter.eventually_gt_atTop 0] with S h hS
  exact ⟨half_rpow_le_repairHalfSide hS, repairHalfSide_le_rpow hS, h⟩

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
