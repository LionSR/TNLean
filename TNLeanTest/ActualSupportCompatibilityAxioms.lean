/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SupportCompatibility

/-! Expected foundational dependencies of augmented support compatibility. -/

set_option autoImplicit false

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_supportCompatible_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.chargeTransportData_supportCompatible_domainGraph

-- Neither fixed auxiliary factor belongs to an embedded physical support.
example {V : Type*} (B : Finset V) :
    Sum.inr false ∉ B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) ∧
    Sum.inr true ∉ B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool) := by
  simp
