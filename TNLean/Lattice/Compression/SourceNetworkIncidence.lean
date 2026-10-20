/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceGateRoot
import TNLean.Lattice.Compression.SourceCircuitResourceBounds
import TNLean.Lattice.Compression.DistributedLinks

/-! # Incidence of the actual sampled density network

Removing gate occurrences with empty participant sets preserves the full
participation count of every party. Hence the network on the original
nonempty occurrences inherits the same constant incidence estimate as the
original circuit. Parallel star and sample links are counted separately.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142
and 581–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}

open Classical in
/-- The retained nonempty occurrences preserve each party's complete
participation count. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 140–142 and 581–588. -/
theorem card_incidentNonemptyGates_eq_participationCount (w : SourceCircuit a b) (p : P) :
    (incidentGates (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) p).card = w.participationCount p := by
  let e : {g : w.nonemptyGateLocations // p ∈ w.participants g.1} ≃
      {g : w.gateLocations // p ∈ w.participants g} :=
    { toFun := fun g ↦ ⟨g.1.1, g.2⟩
      invFun := fun g ↦ ⟨⟨g.1, ⟨p, g.2⟩⟩, g.2⟩
      left_inv := fun g ↦ by cases g; rfl
      right_inv := fun g ↦ by cases g; rfl }
  rw [w.participationCount_eq_card_incidentGates p]
  simpa only [Fintype.card_subtype, incidentGates] using Fintype.card_congr e

open Classical in
/-- The actual density links have incidence at most `2*b*(b-1)` under
original arity and participation bounds. Root membership is derived from
its original participant set. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 581–588. -/
theorem card_incidentSourceDensityLinks_le (w : SourceCircuit a b) (b : ℕ)
    (harity : ∀ g : w.nonemptyGateLocations, (w.participants g.1).card ≤ b)
    (hlifetime : ∀ p, w.participationCount p ≤ b) (p : P) :
    (incidentDistributedLinks (Finset.univ : Finset w.nonemptyGateLocations)
      (fun g ↦ w.participants g.1) (sourceGateRoot w) p).card ≤ 2 * b * (b - 1) := by
  apply card_incidentDistributedLinks_le
    (Finset.univ : Finset w.nonemptyGateLocations)
    (fun g ↦ w.participants g.1) (sourceGateRoot w) b
    (fun g _ ↦ sourceGateRoot_mem w g) (fun g _ ↦ harity g) p
  rw [card_incidentNonemptyGates_eq_participationCount]
  exact hlifetime p

end TNLean.PEPS.PairEffect.SourceCircuit
