/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalCircuitLift
import TNLean.PEPS.Approximation.EffectCircuitResources

/-!
# Gate counts and participating sets under identification of equal layouts

Identifying equal input and output register layouts leaves the number of
actual gate occurrences involving a party unchanged. Any property of the
participating sets is preserved as well.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 140–142 and 199–229; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.PairEffect.OriginalCircuit

variable {P : Type}

/-- Identifying equal layouts preserves a party's actual occurrence count.
Source: polynomial-PEPS manuscript, 04-compression.tex, lines 140–142 and 199–229. -/
theorem participationCount_castLayouts {a b a' b' : Layout P}
    (w : OriginalCircuit a b) (ha : a = a') (hb : b = b') (p : P) :
    (w.castLayouts ha hb).participationCount p = w.participationCount p :=
  castLayouts_rec w ha hb (motive := fun c ↦ c.participationCount p = w.participationCount p) rfl

/-- A property of all participating sets is unchanged by identifying equal
layouts. Source: polynomial-PEPS manuscript, Proposition 7.1,
06-geometry.tex, lines 25–37. -/
theorem forall_participants_castLayouts {a b a' b' : Layout P}
    (w : OriginalCircuit a b) (ha : a = a') (hb : b = b')
    (Q : Finset P → Prop)
    (h : ∀ g : w.nonprivateLocations, Q (w.participants g)) :
    ∀ g : (w.castLayouts ha hb).nonprivateLocations,
      Q ((w.castLayouts ha hb).participants g) :=
  castLayouts_rec w ha hb (motive := fun c ↦ ∀ g, Q (c.participants g)) h

end TNLean.PEPS.PairEffect.OriginalCircuit
