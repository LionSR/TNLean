/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FixedConfigurationExtension
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary cases and an axiom check for extension by a fixed configuration. -/

open TNLean.MPS.AreaLaw

-- A nonzero scalar core has internal budget zero; its two-site extension has bond one.
example :
    IsOpenMPS 2 2 1 (fun σ ↦
      if (fun v : {v : Fin 2 // ¬(0 ≤ v.val ∧ v.val < 0)} ↦ σ v.val) =
        (fun _ ↦ (0 : Fin 2)) then (2 : ℂ) else 0) := by
  let ψ : EuclideanSpace ℂ (Fin 0 → Fin 2) := WithLp.toLp 2 (fun _ ↦ (2 : ℂ))
  have hψ : IsOpenMPS 0 2 0 (fun x ↦ ψ x) := by
    apply isOpenMPS_of_internal_cutMatrix_rank_le ψ
    intro j hj0 hjL
    omega
  simpa only [Nat.max_eq_left (show 0 ≤ 1 by omega)] using
    hψ.extend_interval_by_configuration (T := 2) 0 (by omega) (fun _ ↦ (0 : Fin 2))

-- A nonconstant one-site core likewise has budget zero before the two exterior sites are added.
example :
    IsOpenMPS 3 2 1 (fun σ ↦
      if (fun v : {v : Fin 3 // ¬(1 ≤ v.val ∧ v.val < 2)} ↦ σ v.val) =
        (fun _ ↦ (0 : Fin 2)) then
          (if σ 1 = 0 then (2 : ℂ) else 3) else 0) := by
  let ψ : EuclideanSpace ℂ (Fin 1 → Fin 2) :=
    WithLp.toLp 2 (fun σ ↦ if σ 0 = 0 then (2 : ℂ) else 3)
  have hψ : IsOpenMPS 1 2 0 (fun x ↦ ψ x) := by
    apply isOpenMPS_of_internal_cutMatrix_rank_le ψ
    intro j hj0 hjL
    omega
  simpa [ψ] using
    hψ.extend_interval_by_configuration (T := 3) 1 (by omega) (fun _ ↦ (0 : Fin 2))

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.MPS.AreaLaw.IsOpenMPS.extend_interval_by_configuration
  let axioms ← Lean.collectAxioms decl
  unless axioms.size == expected.size && axioms.all (expected.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
