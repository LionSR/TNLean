/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortIO

/-!
# Original-port and external-reference tests

An arbitrary qubit-to-qutrit onsite enlargement, qutrit matching layer, and
qutrit-to-qubit onsite output map compile to four physical qubit-port layers.
The input and output occupy the original ports, with all designated data/scratch memory
reset to zero.
-/

open Matrix QuantumCircuit

example (A : OnsiteChannel 2 3 (Fin 2)) (L : ChannelLayer 3 2)
    (B : OnsiteChannel 3 2 (Fin 2)) :
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout 2 (Nat.clog 2 3)) 4 Γ ∧
      Γ ∘ₗ PortRegisters.wordInitialization (PortRegisters.portWordCode 2 (Nat.clog 2 3)) =
        PortRegisters.wordInitialization (PortRegisters.portWordCode 2 (Nat.clog 2 3)) ∘ₗ
          (B.map ∘ₗ (L.map ∘ₗ A.map)) := by
  have h := ((IsDimensionBoundedLocalChannelProtocol.onsite A
    (by decide : 0 < 2 ∧ 2 ≤ 3) (by decide : 0 < 3 ∧ 3 ≤ 3)).layer L).onsite_comp B
      (by decide : 0 < 2 ∧ 2 ≤ 3)
  have hsim := h.exists_physicalPortIO (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)
  have hcost : 2 * Nat.clog 2 3 * (0 + 1) = 4 := by decide
  simpa only [hcost] using hsim

example {N B T d : ℕ} [NeZero N] [NeZero d] {δ : Type*}
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N (Nat.clog d B))
        (2 * Nat.clog d B * T) Γ ∧
      tensorMapIdLM (δ := δ) Γ ∘ₗ tensorMapIdLM
          (PortRegisters.wordInitialization (PortRegisters.portWordCode d (Nat.clog d B))) =
        tensorMapIdLM (PortRegisters.wordInitialization
          (PortRegisters.portWordCode d (Nat.clog d B))) ∘ₗ tensorMapIdLM Ψ := by
  obtain ⟨Γ, hΓ, hIO⟩ := h.exists_physicalPortIO hd hN
  refine ⟨Γ, hΓ, ?_⟩
  simpa only [tensorMapIdLM_comp] using congrArg (tensorMapIdLM (δ := δ)) hIO

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'QuantumCircuit.IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO

end AxiomChecks
