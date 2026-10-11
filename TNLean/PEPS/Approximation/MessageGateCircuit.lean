/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.MessageGateExpansion
import TNLean.PEPS.Approximation.EffectReplacementExpansion

/-!
# Original circuit gates constructed from bounded messages

The actual expanded monomial list is inserted into the existing original
circuit constructor. Its contraction bound follows from equality with the
original message-containing operator. The owner embedding and spectator
registers are unchanged. Original monomial, coefficient and pair-effect
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
namespace TNLean.PEPS.PairEffect.MessageGate
variable {P C : Type} [Fintype C] {a b : Layout C}

/-- Construct the existing original gate from the actual message expansion.
The norm hypothesis concerns the original operator, before expansion. -/
def toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P) :
    OriginalCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail) :=
  .nonprivateGate owner hC L.expand (L.isAllowed_expand hL)
    ((congrArg norm L.eval_expand).trans_le hG) tail

/-- Evaluation is exactly the original operator extended by the original
participant and spectator isometries. -/
theorem eval_toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P) :
    (L.toOriginalCircuit owner hC hL hG tail).eval =
      gateMemoryMap owner a b tail L.eval := by
  simp only [toOriginalCircuit, OriginalCircuit.eval, L.eval_expand, gateMemoryMap]

/-- Message expansion does not split the original nonprivate occurrence. -/
theorem nonprivateCount_toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P) :
    (L.toOriginalCircuit owner hC hL hG tail).nonprivateCount = 1 := rfl

/-- The prescribed participating set is unchanged, including empty scalar gates. -/
theorem participants_toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P)
    (j : (L.toOriginalCircuit owner hC hL hG tail).nonprivateLocations) :
    (L.toOriginalCircuit owner hC hL hG tail).participants j = Finset.univ.map owner := rfl

/-- The original effect bound is unchanged, and the actual coefficient mass
increases by at most the bounded message-dimension factor. -/
theorem isExpansionBounded_toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P) (D S : ℝ) (m r : ℕ)
    (hD : 1 ≤ D) (hS : (L.map fun q ↦ ‖q.1‖).sum ≤ S)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m)
    (hr : ∀ q ∈ L, q.2.effectCount ≤ r) :
    (L.toOriginalCircuit owner hC hL hG tail).IsExpansionBounded r (S * D ^ m) := by
  refine ⟨L.effectCount_expand_le hL hr, ?_⟩
  exact (L.expansion_size_le D m L.length hD le_rfl hd hm).2.trans
    (mul_le_mul_of_nonneg_right hS (by positivity))

/-- A real dimension bound gives an explicit integer monomial bound on the
actual constructed original gate. -/
theorem isMonomialBounded_toOriginalCircuit (L : MessageGate a b) (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) (hL : ∀ q ∈ L, q.2.IsAllowed)
    (hG : ‖L.eval‖ ≤ 1) (tail : Layout P) (D : ℝ) (m K : ℕ)
    (hD : 1 ≤ D) (hK : L.length ≤ K)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m) :
    (L.toOriginalCircuit owner hC hL hG tail).IsMonomialBounded ⌈(K : ℝ) * D ^ m⌉₊ := by
  change L.expand.length ≤ ⌈(K : ℝ) * D ^ m⌉₊
  exact_mod_cast (L.expansion_size_le D m K hD hK hd hm).1.trans
    (Nat.le_ceil ((K : ℝ) * D ^ m))

end TNLean.PEPS.PairEffect.MessageGate
