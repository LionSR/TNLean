/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EffectReplacementExpansion
import TNLean.PEPS.Approximation.EffectCircuitResources
import TNLean.PEPS.Approximation.DistributedLifetime

/-!
# Gate bounds at actual source-circuit occurrences

The recursive expansion bounds imply the label and coefficient bounds at
every chronological occurrence. The same occurrence set computes both the
whole-lifetime participation count and the incidence count used in the
corrected-source estimate.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–147,
199–229 and 356–381.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-sourcecircuitresourcebounds-01
TNLean.PEPS.PairEffect.SourceCircuit.IsExpansionBounded.at_gate
Provenance-ID: 8769-source-resource-sourcecircuitresourcebounds-02
TNLean.PEPS.PairEffect.SourceCircuit.participationCount_eq_card_incidentGates
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}

/-- Expansion bounds hold at every actual gate occurrence, including repeated
uses of the same gate. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 199–212 and 351–381. -/
theorem IsExpansionBounded.at_gate {K : ℕ} {S : ℝ}
    {w : SourceCircuit a b} (hw : w.IsExpansionBounded K S) (g : w.gateLocations) :
    Fintype.card (w.branchLabels g) ≤ K ∧
      (∑ ξ : w.branchLabels g, ‖w.branchCoefficient g ξ‖) ≤ S := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv => cases g with
    | inl g => exact ihw hw.1 g
    | inr g => exact ihv hw.2 g
  | localMap => exact nomatch g
  | gate => exact hw
  | swap => exact nomatch g
  | frame r w ih => exact ih hw g

open Classical in
/-- The full participation count equals the incidence count at all original
gate occurrences. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 140–142 and 356–364. -/
theorem participationCount_eq_card_incidentGates (w : SourceCircuit a b) (p : P) :
    w.participationCount p = (incidentGates Finset.univ (participants w) p).card := by
  classical
  rw [participationCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end TNLean.PEPS.PairEffect.SourceCircuit
