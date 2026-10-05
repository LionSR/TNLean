/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortDilation
import TNLean.Circuit.Channel.PhysicalPortIO

/-!
# Bounded native channels compiled to unitary physical-port circuits

The bounded native compiler and the generic physical-port dilation theorem compose
without changing the intersite-depth bound. The input occupies the original physical
ports; designated data/scratch wires and additional local dilation environments all
start in product-zero states. After one final trace of the dilation environments,
the output returns to its original ports and the designated data/scratch wires reset.

**Scope restriction (finite channel identity):** this is an actual unitary circuit
with fixed physical communication ports, following the resource convention of
Piroli, Styliaris and Cirac, arXiv:2103.13367, pp. 1 and 7–8. Discarded environments
are not asserted to reset. Source QCcc measurement/control and pure-output ancilla
conditions remain separate; see `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.
-/

open Matrix

namespace QuantumCircuit

variable {N B T d : ℕ} [NeZero N] [NeZero d]

/-- A bounded native channel has an actual unitary physical-port realization with
one final environment trace, original-port input/output and designated memory reset.
The overhead is `2 * Nat.clog d B * T`; all environments are local and initialized once. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d ∘ₗ
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ := by
  obtain ⟨Γ, hΓ, hports⟩ := h.exists_physicalPortIO hd hN
  obtain ⟨A, owner, U, hU, heq⟩ := hΓ.exists_appended_unitary_dilation
  refine ⟨A, owner, U, hU, ?_⟩
  apply LinearMap.ext
  intro X
  exact (LinearMap.congr_fun heq
    (PortRegisters.wordInitialization (PortRegisters.portWordCode d (Nat.clog d B)) X)).trans
      (LinearMap.congr_fun hports X)

end QuantumCircuit
