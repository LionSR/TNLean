/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PortRouting

/-!
# Adding local environment wires without changing physical ports

A site-preserving embedding of layouts preserves every counted physical-port gate.
The extra wires are untouched by the lifted circuit. This is the geometric step for
fresh local environments in the physical-port resource comparison of
Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix

namespace QuantumCircuit

noncomputable section

variable {d N W W' : ℕ} [NeZero N]

/-- Include old wires in a larger layout, preserving both their spatial owners and
all designated physical ports. -/
structure PhysicalPortEmbedding (P : PhysicalPortLayout N W)
    (Q : PhysicalPortLayout N W') where
  /-- Placement of old wires among the enlarged local memories. -/
  wires : Fin W ↪ Fin W'
  /-- No wire changes its spatial owner. -/
  site_wires : ∀ j, Q.site (wires j) = P.site j
  /-- The original communication ports remain the communication ports. -/
  wires_port : ∀ i, wires (P.port i) = Q.port i

/-- Append fresh wires with explicitly assigned spatial owners. The original physical
ports are retained, and no new wire is a communication port. -/
def PhysicalPortLayout.append (P : PhysicalPortLayout N W) {A : ℕ}
    (owner : Fin A → Fin N) : PhysicalPortLayout N (W + A) where
  site := Fin.addCases P.site owner
  port := ⟨fun i => Fin.castAdd A (P.port i), by
    intro i j h
    apply P.port.injective
    exact Fin.ext (congrArg (@Fin.val (W + A)) h)⟩
  site_port i := by
    change Fin.addCases P.site owner (Fin.castAdd A (P.port i)) = i
    simpa only [Fin.addCases_left] using P.site_port i

/-- The original layout is a port-preserving sublayout of its fresh-wire extension. -/
def PhysicalPortLayout.appendEmbedding (P : PhysicalPortLayout N W) {A : ℕ}
    (owner : Fin A → Fin N) : PhysicalPortEmbedding P (P.append owner) where
  wires := ⟨Fin.castAdd A, fun _ _ h => Fin.ext (congrArg (@Fin.val (W + A)) h)⟩
  site_wires j := by
    change Fin.addCases P.site owner (Fin.castAdd A j) = P.site j
    simp
  wires_port _ := rfl

namespace PhysicalPortEmbedding

/-- Every physical-port unitary circuit lifts to the larger layout at the same
intersite depth, acting identically on all additional environment wires. -/
theorem unitary {P : PhysicalPortLayout N W} {Q : PhysicalPortLayout N W'}
    (e : PhysicalPortEmbedding P Q) {T : ℕ} {U}
    (hU : IsPhysicalPortUnitary (d := d) P T U) :
    IsPhysicalPortUnitary Q T (embedOp e.wires U) := by
  induction hU with
  | onsite i hU hs =>
    apply IsPhysicalPortUnitary.onsite i (embedOp_mem_unitary e.wires.injective hU)
    apply supportedOperators_mono _ (embedOp_mem_supportedOperators_image e.wires.injective hs)
    rintro _ ⟨j, hj, rfl⟩
    exact (e.site_wires j).trans hj
  | onsitePermutation π hπ =>
    rw [embedOp_permOp_viaEmbedding]
    apply IsPhysicalPortUnitary.onsitePermutation
    intro j
    by_cases hj : j ∈ Set.range e.wires
    · obtain ⟨i, rfl⟩ := hj
      rw [Equiv.Perm.viaEmbedding_apply, e.site_wires, e.site_wires, hπ]
    · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hj]
  | layer L =>
    rw [embedOp_embedOp e.wires.injective]
    have hp : (e.wires : Fin W → Fin W') ∘ P.port = Q.port := funext e.wires_port
    rw [hp]
    exact .layer L
  | mul _ _ ihU ihV =>
    rw [← embedOp_mul e.wires.injective]
    exact ihU.mul ihV
  | mono _ hTS ih => exact ih.mono hTS

end PhysicalPortEmbedding

end

end QuantumCircuit
