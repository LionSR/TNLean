/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortUnitaryCompilation

/-!
# Fresh local environments and physical-port unitary compilation

Regression tests cover the empty environment, arbitrary external references, and
a genuine qubit-to-qutrit intermediate register compiled back to the original ports.
-/

open Matrix QuantumCircuit

-- Unused empty environments do not change the actual reduced operation.
example {d N W T : ℕ} [NeZero d] [NeZero N]
    (P : PhysicalPortLayout N W)
    (U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (hU : IsPhysicalPortUnitary P T U) :
    IsPhysicalPortUnitary (P.append (Fin.elim0 : Fin 0 → Fin N)) T
        (embedOp (Fin.castAdd 0) U) ∧
      discardAppendedEnvironment W 0 d ∘ₗ singleKrausMap (embedOp (Fin.castAdd 0) U) ∘ₗ
        appendEnvironmentInput W 0 d = singleKrausMap U :=
  ⟨(P.appendEmbedding Fin.elim0).unitary hU, discardAppendedEnvironment_lift U⟩

-- The entire protocol, including correlations with a reference, has one final discard.
example {d N W T : ℕ} [NeZero d] [NeZero N] {δ : Type*}
    {P : PhysicalPortLayout N W}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) T U ∧
        tensorMapIdLM (δ := δ) (discardAppendedEnvironment W A d) ∘ₗ
          tensorMapIdLM (singleKrausMap U) ∘ₗ
          tensorMapIdLM (appendEnvironmentInput W A d) = tensorMapIdLM Φ :=
  hΦ.exists_appended_unitary_dilation_reference

-- Arbitrary dimension changes and a qutrit pair channel cost four physical qubit layers.
example (A : OnsiteChannel 2 3 (Fin 2)) (L : ChannelLayer 3 2)
    (B : OnsiteChannel 3 2 (Fin 2)) :
    ∃ E : ℕ, ∃ owner : Fin E → Fin 2,
      ∃ U : Matrix (Fin (10 + E) → Fin 2) (Fin (10 + E) → Fin 2) ℂ,
        IsPhysicalPortUnitary ((PortRegisters.layout 2 2).append owner) 4 U ∧
        discardAppendedEnvironment 10 E 2 ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput 10 E 2 ∘ₗ
          PortRegisters.wordInitialization (PortRegisters.portWordCode 2 2) =
          PortRegisters.wordInitialization (PortRegisters.portWordCode 2 2) ∘ₗ
            (B.map ∘ₗ (L.map ∘ₗ A.map)) := by
  have h := ((IsDimensionBoundedLocalChannelProtocol.onsite A
    (by decide : 0 < 2 ∧ 2 ≤ 3) (by decide : 0 < 3 ∧ 3 ≤ 3)).layer L).onsite_comp B
      (by decide : 0 < 2 ∧ 2 ≤ 3)
  have hsim := h.exists_physicalPortUnitaryIO (by decide : 2 ≤ 2) (by decide : 2 ≤ 2)
  have hk : Nat.clog 2 3 = 2 := by decide
  dsimp only at hsim
  rw [hk] at hsim
  exact hsim

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'QuantumCircuit.IsPhysicalPortProtocol.exists_appended_unitary_dilation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.IsPhysicalPortProtocol.exists_appended_unitary_dilation

/--
info: 'QuantumCircuit.IsPhysicalPortProtocol.exists_appended_unitary_dilation_reference'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.IsPhysicalPortProtocol.exists_appended_unitary_dilation_reference

/--
info: 'QuantumCircuit.IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO

end AxiomChecks
