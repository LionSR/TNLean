/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.EncodedChannelProtocol
import TNLean.Circuit.Channel.NativePortLayer
import TNLean.Circuit.Channel.PhysicalRegisterEncoding

/-!
# Compiling bounded native protocols through fixed physical ports

A native protocol whose every intermediate site dimension is positive and at most `B`
first compiles into a word on `d ^ k` levels, where `k = Nat.clog d B`. Each onsite
operation is local on its data register. Each pair-channel layer shares a forward and
backward register routing. The resulting actual physical-port protocol has depth at
most `2 * k * T` and intertwines exactly with the independent input and output codes.
The entire port/scratch configuration is retained as an arbitrary reference. The bound
counts intersite layers only, following the free onsite-unitary resource convention in
arXiv:2103.13367, main text p. 1; the local CPTP dilation bridge remains separate.

**Scope restriction (bounded encoded-input comparison):** the assumptions `d ≥ 2`, `N ≥ 2`,
and one common intermediate dimension bound are
explicit. Uniform family overhead requires choosing `B` before the chain length.
Full source QCcc dilation, ancilla-factorization, and protocol-block conditions remain
separate from this finite reduced-channel resource comparison. See
`docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.
-/

open Matrix

namespace QuantumCircuit

namespace PortRegisters

variable {N k d : ℕ} [NeZero N]

private theorem lift_word_cons (op : FixedRegisterOperation (d ^ k) N)
    (ops : List (FixedRegisterOperation (d ^ k) N)) :
    dataChannelLift N k d (FixedRegisterOperation.wordMap (op :: ops)) =
      dataChannelLift N k d (FixedRegisterOperation.map op) ∘ₗ
        dataChannelLift N k d (FixedRegisterOperation.wordMap ops) :=
  map_mul (dataChannelLift N k d) _ _

private theorem wordDepth_cons (op : FixedRegisterOperation (d ^ k) N)
    (ops : List (FixedRegisterOperation (d ^ k) N)) :
    FixedRegisterOperation.wordDepth (op :: ops) =
      FixedRegisterOperation.depth op + FixedRegisterOperation.wordDepth ops := rfl

/-- Compile an explicit fixed-register operation word. Only pair layers incur physical
cost, and each incurs at most twice the register width. -/
theorem dataChannelLift_word (hd : 0 < d) (hN : 2 ≤ N)
    (ops : List (FixedRegisterOperation (d ^ k) N)) :
    IsPhysicalPortProtocol (layout N k) (2 * k * FixedRegisterOperation.wordDepth ops)
      (dataChannelLift N k d (FixedRegisterOperation.wordMap ops)) := by
  induction ops with
  | nil =>
    simpa only [FixedRegisterOperation.wordDepth, FixedRegisterOperation.wordMap,
      List.map_nil, List.sum_nil, List.prod_nil, Nat.mul_zero, map_one] using
      IsPhysicalPortProtocol.one (d := d) (layout N k)
  | cons op ops ih =>
    rw [lift_word_cons, wordDepth_cons]
    cases op with
    | inl Φ =>
      change IsPhysicalPortProtocol (layout N k)
        (2 * k * (0 + FixedRegisterOperation.wordDepth ops))
        (dataChannelLift N k d Φ.map ∘ₗ
          dataChannelLift N k d (FixedRegisterOperation.wordMap ops))
      simpa only [Nat.zero_add, Nat.add_zero] using
        ih.comp (dataChannelLift_onsiteChannel (N := N) (k := k) (d := d) Φ)
    | inr L =>
      change IsPhysicalPortProtocol (layout N k)
        (2 * k * (1 + FixedRegisterOperation.wordDepth ops))
        (dataChannelLift N k d L.map ∘ₗ
          dataChannelLift N k d (FixedRegisterOperation.wordMap ops))
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        ih.comp (dataChannelLift_channelLayer (k := k) hd hN L)

end PortRegisters

variable {N B m n T d : ℕ} [NeZero N]

/-- A bounded native protocol has a constructive fixed-physical-port realization with
uniform overhead `2 * Nat.clog d B`. Its exact simulation identity holds for arbitrary
operators jointly on the original input and every complementary port/scratch register. -/
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation
    {Ψ : Matrix (Fin N → Fin m) (Fin N → Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin n) (Fin N → Fin n) ℂ}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    let hB : B ≤ d ^ k := Nat.le_pow_clog hd B
    let E := (OnsiteChannel.encodeRegisters fun _ : Fin N =>
      boundedAlphabetCode hB h.dimension_bounds.1.2).map
    let F := (OnsiteChannel.encodeRegisters fun _ : Fin N =>
      boundedAlphabetCode hB h.dimension_bounds.2.2).map
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ ∧
      Γ ∘ₗ PortRegisters.physicalEncoding E =
        PortRegisters.physicalEncoding F ∘ₗ tensorMapIdLM Ψ := by
  dsimp only
  let k := Nat.clog d B
  have hB : B ≤ d ^ k := Nat.le_pow_clog hd B
  obtain ⟨ops, hdepth, hinter⟩ := h.exists_fixedRegisterWord hN hB
  refine ⟨PortRegisters.dataChannelLift N k d (FixedRegisterOperation.wordMap ops), ?_, ?_⟩
  · simpa only [hdepth] using PortRegisters.dataChannelLift_word
      (show 0 < d by omega) hN ops
  · exact PortRegisters.dataChannelLift_physicalEncoding _ _ _ _ hinter

end QuantumCircuit
