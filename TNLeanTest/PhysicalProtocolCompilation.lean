/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalProtocolCompilation

/-!
# Non-power alphabet and reference tests for the complete bounded protocol compiler

A native qutrit layer is encoded into two physical qubits per data register. Its actual
physical channel has depth at most four and obeys the full referenced intertwining
identity. This is an arbitrary channel layer, not only a product-state example.
-/

open Matrix QuantumCircuit
open scoped ComplexOrder

example (L : ChannelLayer 3 2) :
    let E := (OnsiteChannel.encodeRegisters fun _ : Fin 2 =>
      Fin.castLEEmb (by decide : 3 ≤ 2 ^ Nat.clog 2 3)).map
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout 2 (Nat.clog 2 3)) 4 Γ ∧
      Γ ∘ₗ PortRegisters.physicalEncoding E =
        PortRegisters.physicalEncoding E ∘ₗ tensorMapIdLM L.map := by
  have h : IsDimensionBoundedLocalChannelProtocol 3 1 L.map := by
    simpa only [OnsiteChannel.id_map, LinearMap.comp_id] using
      (IsDimensionBoundedLocalChannelProtocol.onsite (OnsiteChannel.id 3 (Fin 2))
        (by decide) (by decide)).layer L
  have hsim := h.exists_physicalPortSimulation (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)
  have hcost : 2 * Nat.clog 2 3 * 1 = 4 := by decide
  simpa only [hcost, boundedAlphabetCode] using hsim

example {N m q : ℕ} (e : Fin N → (Fin m ↪ Fin q))
    (ρ : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    (OnsiteChannel.decodeRegisters e ρ hρ htr).map ∘ₗ
      (OnsiteChannel.encodeRegisters e).map = LinearMap.id :=
  OnsiteChannel.decodeRegisters_encodeRegisters e ρ hρ htr

#print axioms QuantumCircuit.IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation
#print axioms QuantumCircuit.PortRegisters.physicalEncoding_isKrausCPTP
#print axioms QuantumCircuit.PortRegisters.physicalDecoding_encoding
