/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Layer
import TNLean.Circuit.Channel.PortMatching

/-!
# Fixed physical ports with separate local memories

Every wire carries a `d`-dimensional qudit. A layout assigns wires to spatial sites and
selects one physical port at each site. Only a layer acting on these ports incurs
intersite depth. Channels whose Kraus operators act within one site's wires are free
local operations. They can include local memory, fresh local environments, and their
partial traces; no intersite operation may act directly on those memory wires.

The distinction is the one used by Piroli, Styliaris and Cirac,
arXiv:2103.13367, Supplement pp. 7–8. This finite, fixed-memory channel model records
the physical-port gate cost. Source pure-state ancilla conditions, a fixed number of composed
QCcc blocks, and their internal measurement/control rules remain additional conditions.
They do not follow from the quantum-depth index.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

/-- Assign qudit wires to spatial sites, selecting exactly one physical port per site. -/
structure PhysicalPortLayout (N W : ℕ) where
  /-- The spatial site containing each wire. -/
  site : Fin W → Fin N
  /-- The physical qudit through which each site communicates. -/
  port : Fin N ↪ Fin W
  /-- A port belongs to its named site. -/
  site_port : ∀ i, site (port i) = i

variable {d N W : ℕ} [NeZero N]

/-- Unitary circuits with free onsite gates and counted physical-port layers. -/
inductive IsPhysicalPortUnitary (P : PhysicalPortLayout N W) : ℕ →
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ → Prop
  /-- Unitary operations on one site's wires are free. -/
  | onsite (i : Fin N) {U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ}
      (hU : U ∈ unitary (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ))
      (hs : U ∈ supportedOperators d (P.site ⁻¹' {i})) : IsPhysicalPortUnitary P 0 U
  /-- Reordering wires separately within each spatial site is a free local unitary.
  The site-preservation equation forbids moving a wire between sites. -/
  | onsitePermutation (π : Equiv.Perm (Fin W)) (hπ : ∀ x, P.site (π x) = P.site x) :
      IsPhysicalPortUnitary P 0 (permOp π)
  /-- Count one nearest-neighbor layer on the physical ports alone. -/
  | layer (L : Layer d N) : IsPhysicalPortUnitary P 1 (embedOp P.port L.op)
  /-- Multiplying circuit operators adds their physical depths. -/
  | mul {T S : ℕ} {U V} (hU : IsPhysicalPortUnitary P T U)
      (hV : IsPhysicalPortUnitary P S V) : IsPhysicalPortUnitary P (T + S) (U * V)
  /-- Enlarge the physical-depth upper bound. -/
  | mono {T S : ℕ} {U} (hU : IsPhysicalPortUnitary P T U) (hTS : T ≤ S) :
      IsPhysicalPortUnitary P S U

namespace IsPhysicalPortUnitary

/-- Every physical-port unitary circuit is unitary. -/
theorem mem_unitary {P : PhysicalPortLayout N W} {T : ℕ} {U}
    (h : IsPhysicalPortUnitary (d := d) P T U) :
    U ∈ unitary (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) := by
  induction h with
  | onsite _ hU _ => exact hU
  | onsitePermutation π _ => exact permOp_mem_unitary π
  | layer L => exact embedOp_mem_unitary P.port.injective L.op_mem_unitary
  | mul _ _ ihU ihV => exact Submonoid.mul_mem _ ihU ihV
  | mono _ _ ih => exact ih

/-- Reversing a unitary circuit preserves its physical depth. -/
theorem conjTranspose {P : PhysicalPortLayout N W} {T : ℕ} {U}
    (h : IsPhysicalPortUnitary (d := d) P T U) : IsPhysicalPortUnitary P T Uᴴ := by
  induction h with
  | onsite i hU hs => exact .onsite i (Unitary.star_mem hU) (star_mem_supportedOperators hs)
  | onsitePermutation π hπ =>
    rw [permOp_conjTranspose]
    exact .onsitePermutation π.symm (fun x => by simpa using (hπ (π.symm x)).symm)
  | layer L =>
    have h := IsPhysicalPortUnitary.layer (P := P) L.adjoint
    simpa only [Layer.adjoint_op, star_eq_conjTranspose, embedOp_conjTranspose] using h
  | mul _ _ ihU ihV => simpa only [conjTranspose_mul, Nat.add_comm] using ihV.mul ihU
  | mono _ hTS ih => exact ih.mono hTS

/-- The identity needs no physical layers. -/
theorem one (P : PhysicalPortLayout N W) :
    IsPhysicalPortUnitary (d := d) P 0 1 :=
  .onsite 0 (Submonoid.one_mem _) (one_mem_supportedOperators _)

/-- Swapping wires inside one spatial site costs no physical layer. -/
theorem onsite_swap (P : PhysicalPortLayout N W) {a b : Fin W}
    (hab : a ≠ b) (hs : P.site a = P.site b) :
    IsPhysicalPortUnitary (d := d) P 0 (permOp (Equiv.swap a b)) := by
  apply onsite (P.site a) (permOp_mem_unitary _)
  rw [permOp_swap_eq_embedOp hab]
  apply supportedOperators_mono _ (embedOp_mem_supportedOperators (pairSites_injective hab) _)
  rintro x ⟨j, rfl⟩
  fin_cases j <;> simp [pairSites, hs]

end IsPhysicalPortUnitary

/-- A finite channel protocol whose counted gates act only on fixed-dimensional physical
ports. The remaining wires are local memory. The depth is an upper bound; local channels
cost zero and composition adds the bounds. -/
inductive IsPhysicalPortProtocol (P : PhysicalPortLayout N W) : ℕ →
    (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ) → Prop
  /-- A circuit whose counted gates act only on ports induces a channel of the same depth. -/
  | unitary {T : ℕ} {U : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ}
      (hU : IsPhysicalPortUnitary P T U) :
      IsPhysicalPortProtocol P T (singleKrausMap U)
  /-- An arbitrary local instrument with its outcome discarded is a free onsite channel. -/
  | onsite (i : Fin N) {r : ℕ}
      (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
      (hK : ∀ j, K j ∈ supportedOperators d (P.site ⁻¹' {i}))
      (htrace : ∑ j, (K j)ᴴ * K j = 1) :
      IsPhysicalPortProtocol P 0 (rectangularKrausMap K)
  /-- Compose actual channels in execution order and add their physical depths. -/
  | comp {T S : ℕ} {Φ Ψ}
      (hΦ : IsPhysicalPortProtocol P T Φ) (hΨ : IsPhysicalPortProtocol P S Ψ) :
      IsPhysicalPortProtocol P (T + S) (Ψ ∘ₗ Φ)
  /-- A larger upper bound also holds. -/
  | mono {T S : ℕ} {Φ} (hΦ : IsPhysicalPortProtocol P T Φ) (hTS : T ≤ S) :
      IsPhysicalPortProtocol P S Φ

namespace IsPhysicalPortProtocol

/-- Physical-port protocols act as channels on every input operator. -/
theorem isKrausCPTP {P : PhysicalPortLayout N W} {T : ℕ} {Φ}
    (h : IsPhysicalPortProtocol (d := d) P T Φ) : IsKrausCPTP Φ := by
  induction h with
  | unitary hU => exact singleKrausMap_isKrausCPTP _ (Unitary.star_mul_self_of_mem hU.mem_unitary)
  | onsite _ K _ hK => exact rectangularKrausMap_isKrausCPTP K hK
  | comp _ _ ihΦ ihΨ => exact isKrausCPTP_comp ihΦ ihΨ
  | mono _ _ ih => exact ih

/-- The identity channel needs no physical layers. -/
theorem one (P : PhysicalPortLayout N W) :
    IsPhysicalPortProtocol (d := d) P 0
      (1 : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)) := by
  have h := IsPhysicalPortProtocol.unitary (IsPhysicalPortUnitary.one (d := d) P)
  convert h using 1
  apply LinearMap.ext
  intro X
  simp only [Module.End.one_apply, singleKrausMap_apply, conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

end IsPhysicalPortProtocol

end QuantumCircuit
