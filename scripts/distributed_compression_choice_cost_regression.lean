/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation

/-!
# Corrected-position cost regressions

Run after building `TNLean.PEPS.Approximation.CorrectedPositionCost`:
`lake env lean scripts/distributed_compression_choice_cost_regression.lean`.

The second gate acts on a disjoint party pair. Its absolute coefficient and its
parties' physical dimensions are arbitrary, so including exterior costs would
invalidate the uniform bound below. The empty-correction case likewise permits
arbitrary coefficient families because no gate is expanded.
-/

namespace TNLean.PEPS.Approximation.CorrectedPositionCostRegression

open scoped NNReal

variable {Party Gate Position : Type*} [DecidableEq Party] [DecidableEq Gate]

-- No coefficient or dimension hypotheses are needed when there is no correction.
example (gates : Finset Gate) (participants : Gate → Finset Party)
    (endpoints : Position → Party × Party) {Labels : Gate → Type*}
    (labels : ∀ g, Finset (Labels g)) (coeff : ∀ g, Labels g → ℝ≥0)
    (physicalDim : Party → ℕ) :
    correctedPositionChoiceCost gates participants endpoints ∅ labels coeff physicalDim = 1 := by
  simp [correctedPositionChoiceCost, correctedParties, gatesTouching]

/-- Two nonprivate gates act on disjoint participant pairs. -/
private def disjointParticipants (g : Fin 2) : Finset (Fin 4) :=
  if g = 0 then {0, 1} else {2, 3}

/-- A source position at the first gate joins only parties zero and one. -/
private def endpoints (_ : Fin 1) : Fin 4 × Fin 4 := (0, 1)

/-- A single monomial suffices for the independence-from-exterior-cost test. -/
private def labels (_ : Fin 2) : Finset (Fin 1) := {0}

/-- The exterior gate has an arbitrary absolute coefficient. -/
private def coeff (outside : ℝ≥0) (g : Fin 2) (_ : Fin 1) : ℝ≥0 :=
  if g = 0 then 1 else outside

/-- Corrected parties have dimension two; exterior physical dimensions are arbitrary. -/
private def physicalDim (outside : ℕ) (p : Fin 4) : ℕ :=
  if p = 0 ∨ p = 1 then 2 else outside

-- Arbitrary exterior weights and dimensions do not enter the choice cost.
example (outsideCoeff : ℝ≥0) (outsideDim : ℕ) :
    correctedPositionChoiceCost {0, 1} disjointParticipants endpoints {0}
      labels (coeff outsideCoeff) (physicalDim outsideDim) = (2 : ℝ≥0) ^ 4 := by
  have hparties : correctedParties endpoints ({0} : Finset (Fin 1)) = {0, 1} := by
    decide
  have hgates : gatesTouching ({0, 1} : Finset (Fin 2)) disjointParticipants {0, 1} = {0} := by
    decide
  simp only [correctedPositionChoiceCost, hparties, hgates, Finset.prod_singleton]
  simp [ketBraCoefficientCost, labels, coeff, physicalDim, ← pow_add]

#print axioms ketBraCoefficientCost
#print axioms ketBraCoefficientCost_eq_sum
#print axioms correctedPositionChoiceCost
#print axioms correctedPositionChoiceCost_le
#print axioms compressionChoiceBase_le_of_monomial_bounds

end TNLean.PEPS.Approximation.CorrectedPositionCostRegression
