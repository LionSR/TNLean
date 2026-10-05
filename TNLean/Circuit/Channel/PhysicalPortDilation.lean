/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPortLocalDilation
import TNLean.Circuit.Channel.PhysicalPortEnvironmentComposition

/-!
# Physical-port protocols with all environments discarded at the end

Every finite physical-port channel protocol has an actual unitary realization on a
port-preserving extension by local environment wires. All environment wires are
initialized in a product-zero state at the start, remain part of the joint system
through the circuit, and are discarded only at the end. The intersite depth is
unchanged. The proof replaces each supported local channel by its local dilation,
then uses disjoint fresh environment blocks to compose the actual circuits.

This is the finite unitary-dilation step in the resource comparison of Piroli,
Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8. It does not impose source
QCcc block/control restrictions or assert that discarded dilation environments reset.
-/

open Matrix

namespace QuantumCircuit

noncomputable section

variable {d N W : ℕ} [NeZero d] [NeZero N]

/-- Compile every local-channel protocol into a circuit with fresh local pure
ancillas, unchanged physical ports and intersite depth, and one final environment trace.
The equality is on all original-system operators, not only density matrices. -/
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) T U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = Φ := by
  induction hΦ with
  | unitary hU =>
    let owner : Fin 0 → Fin N := Fin.elim0
    refine ⟨0, owner, _, (P.appendEmbedding owner).unitary hU, ?_⟩
    exact discardAppendedEnvironment_lift _
  | onsite i K hs hnorm => exact exists_onsite_appended_dilation P i K hs hnorm
  | comp _ _ ihΦ ihΨ =>
    obtain ⟨A, ownerA, U, hU, hΦ⟩ := ihΦ
    obtain ⟨B, ownerB, V, hV, hΨ⟩ := ihΨ
    refine ⟨A + B, Fin.append ownerA ownerB, _,
      hU.appendEnvironment_comp P ownerA ownerB hV, ?_⟩
    rw [appendEnvironment_comp_channel, hΦ, hΨ]
  | mono _ hTS ih =>
    obtain ⟨A, owner, U, hU, hΦ⟩ := ih
    exact ⟨A, owner, U, hU.mono hTS, hΦ⟩

/-- The compiled final-discard realization preserves every external reference. -/
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation_reference
    {δ : Type*} {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) T U ∧
        tensorMapIdLM (δ := δ) (discardAppendedEnvironment W A d) ∘ₗ
          tensorMapIdLM (singleKrausMap U) ∘ₗ
          tensorMapIdLM (appendEnvironmentInput W A d) = tensorMapIdLM Φ := by
  obtain ⟨A, owner, U, hU, heq⟩ := hΦ.exists_appended_unitary_dilation
  refine ⟨A, owner, U, hU, ?_⟩
  rw [← tensorMapIdLM_comp, ← tensorMapIdLM_comp, heq]

end

end QuantumCircuit
