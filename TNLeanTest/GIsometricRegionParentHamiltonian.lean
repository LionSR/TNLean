/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GIsometricRegionParentHamiltonian

/-! # Physical regional-parent commutation: signature and axiom regression -/

open TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] {d : ℕ}

-- No ambient-surjectivity, nonzero-image, or supplied commutation premise.
example (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R S : Finset V) :
    Commute (regionLocalTerm R (canonicalRegionParentInteraction (groupBondTensor a) R))
      (regionLocalTerm S (canonicalRegionParentInteraction (groupBondTensor a) S)) :=
  regularIsometric_canonicalRegionParentInteractions_commute a ha R S

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.regularIsometric_canonicalRegionParentInteractions_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.regularIsometric_canonicalRegionParentInteractions_commute
