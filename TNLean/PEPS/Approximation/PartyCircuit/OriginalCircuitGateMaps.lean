/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Network.SampledApproximation.DistributedGateMapConstruction

/-!
# Exact local operators of an original distributed circuit

At each original nonprivate occurrence, use its recorded monomial sum as
the prescribed operator. The resulting chronological evaluation is the
original operator, and every local approximation error is zero. Private
maps, their contraction bounds, and the original participating sets are retained.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 21–43 and 137–151, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.OriginalCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

/-- The exact gate sums of the original chronology at the same occurrences: at every
nonprivate occurrence, the sum of its recorded monomial list.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 21–43 and 137–151. -/
def canonicalGateMaps (w : OriginalCircuit X Y) : w.toEffectCircuit.GateMaps :=
  w.toEffectCircuit.expansionGateMaps

/-- Canonical maps retain the original full operator, including private maps.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 21–43. -/
theorem evalWithGateMaps_canonicalGateMaps [Fintype P] (w : OriginalCircuit X Y) :
    w.toEffectCircuit.evalWithGateMaps w.canonicalGateMaps = w.op :=
  (EffectCircuit.evalWithGateMaps_expansionGateMaps _).trans w.op_toEffectCircuit

/-- Every prescribed gate is its exact sum, with zero local approximation error.
The contraction and monomial allowedness conditions are those of the original gate.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 28–43 and 137–151. -/
theorem isGateApproximation_zero_canonicalGateMaps (w : OriginalCircuit X Y) :
    w.toEffectCircuit.IsGateApproximation 0 w.canonicalGateMaps := by
  induction w with
  | done => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | gate D hY g =>
      exact ⟨g.card_ne_one, g.monomials_allowed, g.norm_ev_le_one,
        norm_le_zero_iff.mpr (sub_eq_zero.mpr rfl)⟩
  | localOp p hY U hU => exact hU
  | localOps U hU => exact hU

end QuantumCircuit.Party.OriginalCircuit
