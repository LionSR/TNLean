/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.DataInitialization
import TNLean.Circuit.Channel.PhysicalProtocolCompilation

/-!
# Bounded native protocols with original physical-port input and output

The logical input and output dimensions equal the physical port dimension. Initialize
every local memory digit to zero, perform a zero-depth local port-to-data conversion,
run the bounded encoded compiler, and convert the data back to the original ports.
The result has the same intersite-depth bound and resets all designated data/scratch
memory digits to zero.
The exact channel identity holds for all logical input operators, not only product
states; it can also be tensored with any external reference.

**Scope restriction (bounded reduced-channel port I/O):** this supplies product ancillary
initialization and physical-port input/output for the
finite reduced-channel resource comparison. The depth counts only physical-port intersite
layers; the free onsite-unitary convention is arXiv:2103.13367, main text p. 1.
An explicit local unitary-dilation/source
QCcc protocol-block witness is a separate representation layer, not an assumption or
consequence of this theorem. See `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.
-/

open Matrix

namespace QuantumCircuit

variable {N B T d : ℕ} [NeZero N] [NeZero d]

/-- A bounded native channel with the physical input/output alphabet has an actual
fixed-port implementation using product-zero local memory, returning the output to
its original ports and resetting every designated data/scratch memory digit. The cost is at most
`2 * Nat.clog d B * T`, with no dependence on the number of sites beyond the supplied
native depth and the common dimension bound. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ ∧
      Γ ∘ₗ PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
        PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ := by
  dsimp only
  let k := Nat.clog d B
  have hB : B ≤ d ^ k := Nat.le_pow_clog hd B
  let c : Fin d ↪ Fin (d ^ k) := boundedAlphabetCode hB h.dimension_bounds.1.2
  let E := (OnsiteChannel.encodeRegisters fun _ : Fin N => c).map
  obtain ⟨Γ, hΓ, hinter⟩ := h.exists_physicalPortSimulation hd hN
  change IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ at hΓ
  change Γ ∘ₗ PortRegisters.physicalEncoding E =
    PortRegisters.physicalEncoding E ∘ₗ tensorMapIdLM Ψ at hinter
  have hinit := PortRegisters.wordInitialization_data_eq_physicalEncoding (N := N) c
  have hdata : Γ ∘ₗ PortRegisters.wordInitialization (PortRegisters.dataWordCode c) =
      PortRegisters.wordInitialization (PortRegisters.dataWordCode c) ∘ₗ Ψ := by
    apply LinearMap.ext
    intro X
    calc
      Γ (PortRegisters.wordInitialization (PortRegisters.dataWordCode c) X) =
          Γ (PortRegisters.physicalEncoding E (PortRegisters.zeroDataReferencePrep X)) :=
        congrArg Γ (LinearMap.congr_fun hinit X)
      _ = PortRegisters.physicalEncoding E
          (tensorMapIdLM Ψ (PortRegisters.zeroDataReferencePrep X)) :=
        LinearMap.congr_fun hinter _
      _ = PortRegisters.physicalEncoding E (PortRegisters.zeroDataReferencePrep (Ψ X)) :=
        congrArg (PortRegisters.physicalEncoding E)
          (LinearMap.congr_fun (PortRegisters.tensorMapId_comp_zeroDataReferencePrep Ψ) X)
      _ = PortRegisters.wordInitialization (PortRegisters.dataWordCode c) (Ψ X) :=
        (LinearMap.congr_fun hinit (Ψ X)).symm
  obtain ⟨pre, post, hpre, hpost, hpreI, hpostI⟩ :=
    PortRegisters.exists_portDataTransfers (N := N) c
      (registerFallbackDensity (NeZero.pos d)) (registerFallbackDensity_posSemidef (NeZero.pos d))
      (trace_registerFallbackDensity (NeZero.pos d))
  refine ⟨post ∘ₗ (Γ ∘ₗ pre), ?_, ?_⟩
  · simpa only [Nat.zero_add, Nat.add_zero] using (hpre.comp hΓ).comp hpost
  · apply LinearMap.ext
    intro X
    change post (Γ (pre (PortRegisters.wordInitialization (PortRegisters.portWordCode d k) X))) =
      PortRegisters.wordInitialization (PortRegisters.portWordCode d k) (Ψ X)
    rw [show pre (PortRegisters.wordInitialization (PortRegisters.portWordCode d k) X) =
        PortRegisters.wordInitialization (PortRegisters.dataWordCode c) X from
      LinearMap.congr_fun hpreI X]
    rw [show Γ (PortRegisters.wordInitialization (PortRegisters.dataWordCode c) X) =
        PortRegisters.wordInitialization (PortRegisters.dataWordCode c) (Ψ X) from
      LinearMap.congr_fun hdata X]
    exact LinearMap.congr_fun hpostI (Ψ X)

end QuantumCircuit
