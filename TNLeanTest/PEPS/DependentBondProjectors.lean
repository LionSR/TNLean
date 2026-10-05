/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondProjectorExpansion

/-!
# Unequal-dimensional canonical projector regressions

Two independently labelled self edges have dimensions two and three. All four
endpoint incidences survive, giving a 36-dimensional local virtual space.
The edge actions and inserted matrices are independent parameters.
-/

noncomputable section
open scoped BigOperators Matrix
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork

namespace TNLeanTest.DependentBondProjectors

private abbrev edgeDim (e : Bool) := Fin (if e then 3 else 2)
private def atVertex (_ : Bool) : Unit := ()

example : Fintype.card (edgeDim false) = 2 := rfl
example : Fintype.card (edgeDim true) = 3 := rfl

-- Both incidences of both self edges occur at the same vertex.
example : Fintype.card (IncidentEndpoint atVertex atVertex ()) = 4 := by decide
example : Fintype.card (LocalConfig atVertex atVertex edgeDim ()) = 36 := by decide

section GeneralGroup
variable {G : Type*} [Group G]

-- The four factors form a representation without finiteness or unitarity of G.
example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ) (g h : G) :
    incidentMatrix atVertex atVertex edgeDim U () (g * h) =
      incidentMatrix atVertex atVertex edgeDim U () g *
        incidentMatrix atVertex atVertex edgeDim U () h :=
  incidentMatrix_mul atVertex atVertex edgeDim U () g h

example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ) :
    incidentMatrix atVertex atVertex edgeDim U () 1 = 1 :=
  incidentMatrix_one atVertex atVertex edgeDim U ()

variable [Fintype G]
attribute [local instance] Representation.invertibleFintypeCardComplex

-- The actual canonical coefficient map is the averaging projector.
example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ) :
    localSiteMap atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim U) () =
      (incidentRepresentation atVertex atVertex edgeDim U ()).averageMap :=
  localSiteMap_averagingSite atVertex atVertex edgeDim U ()

example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ) :
    IsGInjective (incidentRepresentation atVertex atVertex edgeDim U ())
      (localSiteMap atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim U) ()) :=
  DependentBondNetwork.isGInjective_averagingSite atVertex atVertex edgeDim U ()

-- The expansion retains the original two-by-two and three-by-three matrices.
example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ)
    (B : (e : Bool) → Matrix (edgeDim e) (edgeDim e) ℂ)
    (σ : EndpointConfig edgeDim) :
    network atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim U) B
        (endpointSiteEquiv atVertex atVertex edgeDim σ) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Unit *
        ∑ q : Unit → G, ∏ e,
          (U e (q ()) * B e * U e ((q ())⁻¹)) (σ (e, true)) (σ (e, false)) := by
  simpa only [Equiv.symm_apply_apply, atVertex] using
    network_averagingSite atVertex atVertex edgeDim U B
      (endpointSiteEquiv atVertex atVertex edgeDim σ)

-- The canonical state is unchanged by simultaneous endpoint gauge changes,
-- including noncommuting p and q in an arbitrary finite group.
example (U : (e : Bool) → G →* Matrix (edgeDim e) (edgeDim e) ℂ)
    (p : Bool → G) (q : Unit → G)
    (σ : (v : Unit) → LocalConfig atVertex atVertex edgeDim v) :
    network atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim U)
        (fun e => U e (q () * p e * (q ())⁻¹)) σ =
      network atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim U)
        (fun e => U e (p e)) σ :=
  network_averagingSite_vertexGauge atVertex atVertex edgeDim U p q σ

end GeneralGroup

-- With the trivial group, even non-diagonal insertions have their head index
-- as row and tail index as column, and the global normalization is exactly one.
example (B : (e : Bool) → Matrix (edgeDim e) (edgeDim e) ℂ)
    (σ : EndpointConfig edgeDim) :
    network atVertex atVertex edgeDim
        (DependentBondNetwork.averagingSite atVertex atVertex edgeDim
          (fun e => (1 : Unit →* Matrix (edgeDim e) (edgeDim e) ℂ))) B
        (endpointSiteEquiv atVertex atVertex edgeDim σ) =
      B false (σ (false, true)) (σ (false, false)) *
        B true (σ (true, true)) (σ (true, false)) := by
  rw [network_averagingSite]
  simp [mul_comm]

end TNLeanTest.DependentBondProjectors

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.DependentBondNetwork.incidentMatrix_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.incidentMatrix_mul

/--
info: 'TNLean.PEPS.DependentBondNetwork.isGInjective_representationAveragingSite' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.isGInjective_representationAveragingSite

/--
info: 'TNLean.PEPS.DependentBondNetwork.network_averagingSite' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.network_averagingSite

/--
info: 'TNLean.PEPS.DependentBondNetwork.network_averagingSite_vertexGauge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.network_averagingSite_vertexGauge
