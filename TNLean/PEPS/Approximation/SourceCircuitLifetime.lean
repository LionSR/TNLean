/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitChoiceProduct
import TNLean.PEPS.Approximation.CorrectedPositionCost

/-! # Lifetime bounds for the actual corrected source positions of a circuit -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-choice-cost.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-physical-sourcecircuitlifetime-01
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.card_touched_correctedMask_le

Provenance-ID: 8769-physical-sourcecircuitlifetime-02
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.coefficient_physical_cost_eq

Provenance-ID: 8769-physical-sourcecircuitlifetime-03
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.coefficient_physical_cost_le

Provenance-ID: 8769-physical-sourcecircuitlifetime-04
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.correctedMask

Provenance-ID: 8769-physical-sourcecircuitlifetime-05
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.corrected_slot_isTouched

Provenance-ID: 8769-physical-sourcecircuitlifetime-06
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.isTouched_correctedMask_iff

Provenance-ID: 8769-physical-sourcecircuitlifetime-07
Downstream declaration:
TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_mul_conj_le_lifetime

-/


noncomputable section
open scoped NNReal
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type}

open Classical in
/-- The affected parties are exactly the endpoints of the corrected source
occurrences. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–364. -/
def correctedMask {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : P → Bool :=
  fun p ↦ decide (p ∈ correctedParties (endpoints w) S)

open Classical in
/-- The circuit's touching predicate agrees with the complete lifetime incidence
set at the corrected endpoints.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 356–364. -/
theorem isTouched_correctedMask_iff {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (g : gateLocations w) :
    IsTouched (correctedMask w S) w g ↔
      g ∈ gatesTouching Finset.univ (participants w) (correctedParties (endpoints w) S) := by
  simp only [IsTouched, correctedMask, decide_eq_true_eq, mem_gatesTouching,
    Finset.mem_univ, true_and]
  exact exists_congr fun _ ↦ and_comm

open Classical in
private theorem touched_correctedMask_eq {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    Finset.univ.filter (IsTouched (correctedMask w S) w) =
      gatesTouching Finset.univ (participants w) (correctedParties (endpoints w) S) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isTouched_correctedMask_iff]

open Classical in
/-- The gate occurrence containing every corrected slot is touched, by the actual endpoint
incidence of that slot. No incidence certificate is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–364. -/
theorem corrected_slot_isTouched {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) {e : sourceLocations w} (he : e ∈ S) :
    IsTouched (correctedMask w S) w e.1 := by
  rw [isTouched_correctedMask_iff]
  exact owner_mem_gatesTouching_correctedParties Finset.univ (participants w)
    (endpoints w) (fun e ↦ e.1) S he (Finset.mem_univ _)
    (endpoints_mem_participants w e).1

open Classical in
/-- Whole-lifetime participation bounds the actual touched gate occurrences by
twice the lifetime bound times the number of corrected slots.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 356–372. -/
theorem card_touched_correctedMask_le {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (lifetime : ℕ)
    (hlifetime : ∀ p ∈ correctedParties (endpoints w) S,
      (incidentGates Finset.univ (participants w) p).card ≤ lifetime) :
    (Finset.univ.filter (IsTouched (correctedMask w S) w)).card ≤
      2 * lifetime * S.card := by
  rw [touched_correctedMask_eq]
  exact card_gatesTouching_correctedParties_le Finset.univ (participants w)
    (endpoints w) S lifetime hlifetime

open Classical in
/-- The actual ket–bra coefficient sum, with prescribed physical-entry counts,
is precisely the existing corrected-position choice cost.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 365–381. -/
theorem coefficient_physical_cost_eq {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (physicalDim : P → ℕ) :
    (∑ ξ : Choices (correctedMask w S) w, ∑ ζ : Choices (correctedMask w S) w,
      ‖coefficient (correctedMask w S) w ξ * star (coefficient (correctedMask w S) w ζ)‖) *
        (∏ p ∈ correctedParties (endpoints w) S, (physicalDim p : ℝ) ^ 2) =
      (correctedPositionChoiceCost Finset.univ (participants w) (endpoints w) S
        (fun g ↦ (Finset.univ : Finset (branchLabels w g)))
        (fun g ξ ↦ ‖branchCoefficient w g ξ‖₊) physicalDim : ℝ) := by
  rw [sum_norm_coefficient_mul_conj_eq_prod_sq, touched_correctedMask_eq]
  simp only [correctedPositionChoiceCost, ketBraCoefficientCost, NNReal.coe_mul,
    NNReal.coe_prod, NNReal.coe_pow, NNReal.coe_sum, coe_nnnorm, NNReal.coe_natCast,
    Finset.prod_pow]

open Classical in
/-- The actual partial-choice coefficients and prescribed physical-entry counts
obey the corrected-position bound. Only touched gate coefficients and affected
physical dimensions are bounded; private memories are unrestricted.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 356–381. -/
theorem coefficient_physical_cost_le {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (physicalDim : P → ℕ)
    (lifetime : ℕ) (B d : ℝ≥0) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hlifetime : ∀ p ∈ correctedParties (endpoints w) S,
      (incidentGates Finset.univ (participants w) p).card ≤ lifetime)
    (hcoeff : ∀ g, IsTouched (correctedMask w S) w g →
      ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖₊ ≤ B)
    (hphysical : ∀ p ∈ correctedParties (endpoints w) S, (physicalDim p : ℝ≥0) ≤ d) :
    (∑ ξ : Choices (correctedMask w S) w, ∑ ζ : Choices (correctedMask w S) w,
      ‖coefficient (correctedMask w S) w ξ * star (coefficient (correctedMask w S) w ζ)‖) *
        (∏ p ∈ correctedParties (endpoints w) S, (physicalDim p : ℝ) ^ 2) ≤
      ((B : ℝ) ^ (4 * lifetime) * (d : ℝ) ^ 4) ^ S.card := by
  rw [coefficient_physical_cost_eq]
  have h := correctedPositionChoiceCost_le Finset.univ (participants w) (endpoints w) S
    (fun g ↦ (Finset.univ : Finset (branchLabels w g)))
    (fun g ξ ↦ ‖branchCoefficient w g ξ‖₊) physicalDim lifetime B d hB hd hlifetime
    (fun g hg ↦ hcoeff g ((isTouched_correctedMask_iff w S g).mpr hg)) hphysical
  exact_mod_cast h

open Classical in
/-- Whole-lifetime participation gives the actual ket–bra coefficient bound
with exponent four times the lifetime bound times the number of corrected slots.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 356–373. -/
theorem sum_norm_coefficient_mul_conj_le_lifetime {a b : Layout P}
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (lifetime : ℕ) (B : ℝ≥0) (hB : 1 ≤ B)
    (hlifetime : ∀ p ∈ correctedParties (endpoints w) S,
      (incidentGates Finset.univ (participants w) p).card ≤ lifetime)
    (hcoeff : ∀ g, IsTouched (correctedMask w S) w g →
      ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖₊ ≤ B) :
    (∑ ξ : Choices (correctedMask w S) w, ∑ ζ : Choices (correctedMask w S) w,
      ‖coefficient (correctedMask w S) w ξ * star (coefficient (correctedMask w S) w ζ)‖) ≤
      (B : ℝ) ^ (4 * lifetime * S.card) := by
  have h := coefficient_physical_cost_le w S (fun _ ↦ 1) lifetime B 1 hB le_rfl
    hlifetime hcoeff (fun _ _ ↦ by simp)
  simpa only [Nat.cast_one, one_pow, Finset.prod_const_one, mul_one, NNReal.coe_one,
    ← pow_mul] using h

end TNLean.PEPS.PairEffect.SourceCircuit
