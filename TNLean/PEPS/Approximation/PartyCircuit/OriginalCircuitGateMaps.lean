/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedGateMapConstruction

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

namespace TNLean.Lattice.PartyCircuit.OriginalCircuit

variable {P : Type}

/-- The exact gate sums of the original chronology at the same occurrences: at every
nonprivate occurrence, the sum of its recorded monomial list.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 21–43 and 137–151. -/
def canonicalGateMaps {a b : Layout P} (w : OriginalCircuit a b) : w.produce.GateMaps :=
  w.produce.expansionGateMaps

/-- Canonical maps retain the original full operator, including private maps.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 21–43. -/
theorem evalWithGateMaps_canonicalGateMaps {a b : Layout P} (w : OriginalCircuit a b) :
    w.produce.evalWithGateMaps w.canonicalGateMaps = w.eval :=
  w.produce.evalWithGateMaps_expansionGateMaps.trans w.eval_produce

/-- Every prescribed gate is its exact sum, with zero local approximation error.
The contraction and monomial allowedness conditions are those of the original gate.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 28–43 and 137–151. -/
theorem isGateApproximation_zero_canonicalGateMaps {a b : Layout P}
    (w : OriginalCircuit a b) :
    w.produce.IsGateApproximation 0 w.canonicalGateMaps := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | privateMap p ha hb A hA tail => exact hA
  | nonprivateGate owner hC L hL hG tail =>
      dsimp only [produce, canonicalGateMaps, EffectCircuit.expansionGateMaps,
        EffectCircuit.IsGateApproximation]
      exact ⟨hC, hL, hG, by simp only [sub_self, norm_zero, le_refl]⟩
  | swap => trivial
  | frame r w ih => exact ih

end TNLean.Lattice.PartyCircuit.OriginalCircuit
