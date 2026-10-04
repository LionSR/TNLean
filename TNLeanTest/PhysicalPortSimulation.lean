/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PortSimulation
import TNLean.Circuit.Channel.OnsiteRegisterEncoding

/-!
# Boundary and reference tests for physical-port simulation

Check a non-power local dimension, the zero-width one-dimensional code, the
one-site self-loop, and the product decoder on arbitrary referenced chain inputs.
-/

open Matrix QuantumCircuit
open scoped BigOperators ComplexOrder

example : 3 ≤ 2 ^ Nat.clog 2 3 := le_registerDimension (by decide) le_rfl

example : 2 * Nat.clog 2 3 = 4 := by decide

example (d : ℕ) : 2 * Nat.clog d 1 = 0 := by simp

example : (PortMatching.layer 2 ({0} : Finset (Fin 1)) (by simp)).op = 1 :=
  PortMatching.layer_op_one_site _ _

example : ∃ (r : Fin 2 → ℕ)
    (A : ∀ i, Fin (r i) → Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ),
    IsPhysicalPortProtocol (PortRegisters.layout 2 0) 0
      (PortRegisters.matchingChannel (by decide) A ({0} : Finset (Fin 2)) (by simp)) := by
  have h := exists_bounded_matching_simulation (d := 2) (B := 1) (m := 1) (N := 2)
    (by decide) le_rfl (by decide) (fun _ => LinearMap.id)
    ({0} : Finset (Fin 2)) (by simp) (fun _ _ => isKrausCPTP_id)
    (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) Matrix.PosSemidef.one (by simp)
  simp only [Nat.clog_one_right, Nat.mul_zero] at h
  obtain ⟨r, A, _, _, hA⟩ := h
  exact ⟨r, A, hA⟩

example {N m q : ℕ} {δ : Type*}
    (e : Fin N → (Fin m ↪ Fin q)) (ρ : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1) :
    tensorMapIdLM (δ := δ) (OnsiteChannel.decodeRegisters e ρ hρ htr).map ∘ₗ
      tensorMapIdLM (δ := δ) (OnsiteChannel.encodeRegisters e).map = LinearMap.id :=
  OnsiteChannel.decodeRegisters_encodeRegisters_reference e ρ hρ htr

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'QuantumCircuit.exists_bounded_matching_simulation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.exists_bounded_matching_simulation

/--
info: 'QuantumCircuit.PortRegisters.matchingChannel_isPhysicalPortProtocol'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.PortRegisters.matchingChannel_isPhysicalPortProtocol

/--
info: 'QuantumCircuit.OnsiteChannel.encoded_map_encodeRegisters'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.OnsiteChannel.encoded_map_encodeRegisters

end AxiomChecks
