/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.DependentRegionOperatorLift

/-!
# Single-qubit configuration coordinates

The two basis states identify with configurations on one vertex. Extending an
operator on this full region leaves it unchanged.
-/

open TNLean.PEPS

namespace TNLeanTest.SingleQubitConfig

/-- Configurations of the full one-vertex region with two basis states. -/
abbrev Config := (v : (Finset.univ : Finset Unit)) → Fin 2

/-- Identify the two basis states with single-qubit configurations. -/
def configEquiv : Fin 2 ≃ Config where
  toFun i := fun _ ↦ i
  invFun σ := σ ⟨(), by simp⟩
  left_inv _ := rfl
  right_inv σ := by ext v; congr 1

/-- An operator on the full single-qubit region is its own identity extension. -/
theorem lift_univ (K : Matrix Config Config ℂ) :
    dependentRegionOperatorLift (Out := fun _ : Unit ↦ Fin 2) Finset.univ K = K := by
  ext α β
  simp [dependentRegionOperatorLift_apply]

end TNLeanTest.SingleQubitConfig
