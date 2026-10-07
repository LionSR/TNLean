/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation

/-!
# Distributed-compression incidence regressions

Run after building both production modules:
`lake env lean scripts/distributed_compression_layout_regression.lean`.

Two distinct gate occurrences use the same participant pair. Only a source at
the first occurrence is corrected. Both gates must be expanded, and both their
star and sample links must survive as distinct parallel links. A third party is
isolated. The zero-position and zero-gate cases impose no nonemptiness assumption.
The small finite computations below use kernel-checked `decide`.
-/

namespace TNLean.PEPS.Approximation.DistributedLayoutRegression

variable {Position Gate : Type*}

/-- Distinct identifiers for two occurrences of the same operation. -/
private def gates : Finset (Fin 2) := {0, 1}

/-- Both occurrences have the same two parties; the third party is isolated. -/
private def participants (_ : Fin 2) : Finset (Fin 3) := {0, 1}

/-- Party zero is the common-label star root in each gate. -/
private def root (_ : Fin 2) : Fin 3 := 0

/-- The single corrected source position joins parties zero and one. -/
private def endpoints (_ : Fin 1) : Fin 3 × Fin 3 := (0, 1)

/-- Only the first gate's source position is corrected. -/
private def corrected : Finset (Fin 1) := {0}

-- The uncorrected second occurrence touches corrected endpoints.
example :
    gatesTouching gates participants (correctedParties endpoints corrected) = gates := by
  decide

-- Repeated operations are two occurrences over a party's entire lifetime.
example : (incidentGates gates participants 0).card = 2 := by decide

example : (correctedParties endpoints corrected).card = 2 := by decide

-- Distinct gate tags and disjoint link kinds preserve all four parallel links.
example : (distributedLinks gates participants root).card = 4 := by decide

example : (incidentDistributedLinks gates participants root 0).card = 4 := by decide

-- The isolated party neither triggers expansion nor receives any virtual link.
example : gatesTouching gates participants {2} = ∅ := by decide

example : incidentDistributedLinks gates participants root 2 = ∅ := by decide

-- The source bound also covers coincident endpoints without requiring a source rank.
example :
    (correctedParties (fun _ : Fin 1 ↦ ((0 : Fin 3), (0 : Fin 3))) corrected).card = 1 := by
  decide

-- Empty corrected sets and empty gate lists are genuine zero-resource cases.
example (slots : Position → Fin 3 × Fin 3) : correctedParties slots ∅ = ∅ := by
  simp [correctedParties]

example (parties : Gate → Finset (Fin 3)) (roots : Gate → Fin 3) [DecidableEq Gate] :
    distributedLinks ∅ parties roots = ∅ := by
  simp [distributedLinks]

-- Apply the general bounds using only the actual lifetime and arity counts.
example :
    (gatesTouching gates participants (correctedParties endpoints corrected)).card ≤
      2 * 2 * corrected.card := by
  apply card_gatesTouching_correctedParties_le
  intro p hp
  apply (Finset.card_filter_le gates _).trans
  decide

example : (incidentDistributedLinks gates participants root 0).card ≤ 2 * 2 * (2 - 1) := by
  apply card_incidentDistributedLinks_le
  · intro g hg
    change (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3))
    decide
  · intro g hg
    change ({0, 1} : Finset (Fin 3)).card ≤ 2
    decide
  · decide

#print axioms sourceEndpoints
#print axioms correctedParties
#print axioms incidentGates
#print axioms gatesTouching
#print axioms card_correctedParties_le
#print axioms card_gatesTouching_correctedParties_le
#print axioms disjoint_participants_of_not_mem_gatesTouching
#print axioms card_pairSampleLabels
#print axioms filter_pairSampleLabels_eq_map
#print axioms card_gateLinkParties
#print axioms distributedLinkParties_subset
#print axioms card_distributedLinkParties
#print axioms exists_common_gate_of_mem_distributedLinkParties
#print axioms card_incidentDistributedLinks_le

end TNLean.PEPS.Approximation.DistributedLayoutRegression
