/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusDualFluxParent

/-!
# Genuine local-parent regressions for nonabelian flux paths

These tests use the actual canonical regular-projector tensor and its actual
canonical local parent. The winding loop remains outside the nil homotopy
class despite satisfying every local parent constraint.
-/

noncomputable section
open scoped Matrix
namespace TNLeanTest.TorusDualFluxParent

open TNLean.PEPS
local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Quiver (TorusVertex 3 3) := torusDualQuiver 3 3
local notation "S₃" => Equiv.Perm (Fin 3)
local notation "A" => projectorSiteFin S₃

/-- An order-three permutation, so inverse labels cannot disappear as involutions.
Duplicated from the flux-string regression file to keep this parent regression a
standalone test module with no cross-test-file object import. -/
def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- An eastward dual segment crossing the downward bond on its right. -/
def eastPath : TorusDualPath ((0, 0) : TorusVertex 3 3) (1, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.east 0 0)

/-- A full eastward winding, closed on the torus but moving three units in the cover. -/
def eastWinding : TorusDualPath ((0, 0) : TorusVertex 3 3) (0, 0) :=
  ((Quiver.Path.nil.cons (TorusDualStep.east 0 0)).cons
    (TorusDualStep.east 1 0)).cons (TorusDualStep.east 2 0)

/-- The canonical parent away from an open-string endpoint annihilates a
concrete nonzero, nonabelian regular-projector flux state. -/
theorem s3_open_string_canonical_parent :
    regionLocalTerm (torusPlaquetteRegion ((0, 2) : TorusVertex 3 3))
        (canonicalRegionParentInteraction (groupBondTensor (torusNativeIncidentSite A))
          (torusPlaquetteRegion ((0, 2) : TorusVertex 3 3))) *ᵥ
      torusDualFluxState (leftRegularMatrix S₃) (fun _ => A) cycle eastPath = 0 :=
  torusDualFluxState_canonicalParent_annihilates_of_ne (leftRegularMatrix S₃) A
    (projectorSiteFin_isGIsometric S₃).invariant cycle eastPath (0, 2)
    (by decide) (by decide)

/-- A noncontractible closed string meets all canonical local constraints. -/
theorem s3_winding_canonical_parent (v : TorusVertex 3 3) :
    regionLocalTerm (torusPlaquetteRegion v)
        (canonicalRegionParentInteraction (groupBondTensor (torusNativeIncidentSite A))
          (torusPlaquetteRegion v)) *ᵥ
      torusDualFluxState (leftRegularMatrix S₃) (fun _ => A) cycle eastWinding = 0 :=
  torusDualFluxState_canonicalParent_annihilates_loop (leftRegularMatrix S₃) A
    (projectorSiteFin_isGIsometric S₃).invariant cycle eastWinding v

/-- The local-parent regression is not explained by a zero PEPS vector. -/
theorem s3_open_string_ne_zero :
    torusDualFluxState (leftRegularMatrix S₃) (fun _ => A) cycle eastPath ≠ 0 :=
  (projectorSiteFin_isGIsometric S₃).torusDualFlux_state_ne_zero cycle eastPath

/-- The same nonvanishing applies to the closed winding state. -/
theorem s3_winding_state_ne_zero :
    torusDualFluxState (leftRegularMatrix S₃) (fun _ => A) cycle eastWinding ≠ 0 :=
  (projectorSiteFin_isGIsometric S₃).torusDualFlux_state_ne_zero cycle eastWinding

end TNLeanTest.TorusDualFluxParent
