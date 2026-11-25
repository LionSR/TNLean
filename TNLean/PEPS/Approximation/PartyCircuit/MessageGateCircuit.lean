/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.GateExpansion.Messages
import QICLean.Circuit.Party.Original.Basic

/-!
# Original circuit gates constructed from bounded messages

The actual expanded monomial list is inserted into the existing original
circuit constructor. Its contraction bound follows from equality with the
original message-containing operator. The cell of the gate is unchanged, and
the parties outside it keep their bases. Original monomial, coefficient and pair-effect
bounds give the resource assumptions used in source-only reduction.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.MessageGate

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P}

/-- The weighted gate of the actual message expansion. -/
def toWeightedGate (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s)) : WeightedGate D X Y :=
  ⟨L.expand⟩

omit [Fintype P] in
/-- The matrix of the expanded gate is the original operator of the message gate. -/
theorem ev_toWeightedGate (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s)) :
    WeightedGate.ev L.toWeightedGate () = L.op :=
  (WeightedGate.ev_eq_gate_toGate _ ()).trans L.op_expand

/-- Construct the original gate on the cell `D` from the actual message expansion.
The norm hypothesis concerns the original operator, before expansion. -/
def toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) : OriginalCircuit X Y :=
  OriginalCircuit.gate D hY (OriginalGate.ofWeightedGate L.toWeightedGate hD
    (L.isAllowed_expand hL) ((congrArg norm L.ev_toWeightedGate).trans_le hG))

/-- The operator is exactly the original operator placed on its cell. -/
theorem op_toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) :
    (L.toOriginalCircuit hY hD hL hG).op = placeBetween D hY L.op := by
  rw [toOriginalCircuit, OriginalCircuit.op_gate]
  exact congrArg (placeBetween D hY) L.ev_toWeightedGate

omit [Fintype P] in
/-- Message expansion does not split the original nonprivate occurrence. -/
theorem nonprivateCount_toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) : (L.toOriginalCircuit hY hD hL hG).nonprivateCount = 1 :=
  OriginalCircuit.nonprivateCount_gate _ _ _

omit [Fintype P] in
/-- The prescribed participating set is unchanged, including empty scalar gates. -/
theorem participants_toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) (j : (L.toOriginalCircuit hY hD hL hG).nonprivateLocations) :
    (L.toOriginalCircuit hY hD hL hG).participants j = D := rfl

omit [Fintype P] in
/-- The original effect bound is unchanged, and the actual coefficient mass
increases by at most the bounded message-dimension factor. -/
theorem isExpansionBounded_toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) (D₀ S : ℝ) (m r : ℕ)
    (hD₀ : 1 ≤ D₀) (hS : (L.map fun q ↦ ‖q.1‖).sum ≤ S)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D₀)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m)
    (hr : ∀ q ∈ L, q.2.effectCount ≤ r) :
    (L.toOriginalCircuit hY hD hL hG).IsExpansionBounded r (S * D₀ ^ m) := by
  refine ⟨L.effectCount_expand_le hL hr, ?_⟩
  exact (L.expansion_size_le D₀ m L.length hD₀ le_rfl hd hm).2.trans
    (mul_le_mul_of_nonneg_right hS (by positivity))

omit [Fintype P] in
/-- A real dimension bound gives an explicit integer monomial bound on the
actual constructed original gate. -/
theorem isMonomialBounded_toOriginalCircuit (L : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (hY : ∀ s ∉ D, Y s = X s) (hD : D.card ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.op‖ ≤ 1) (D₀ : ℝ) (m K : ℕ)
    (hD₀ : 1 ≤ D₀) (hK : L.length ≤ K)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D₀)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m) :
    (L.toOriginalCircuit hY hD hL hG).IsMonomialBounded ⌈(K : ℝ) * D₀ ^ m⌉₊ := by
  change L.expand.length ≤ ⌈(K : ℝ) * D₀ ^ m⌉₊
  exact_mod_cast (L.expansion_size_le D₀ m K hD₀ hK hd hm).1.trans
    (Nat.le_ceil ((K : ℝ) * D₀ ^ m))

end QuantumCircuit.Party.MessageGate
