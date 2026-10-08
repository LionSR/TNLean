/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.TransferGateExpansion
import TNLean.PEPS.Approximation.PartyGateComposition
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Expansion of monomials containing finite-dimensional messages

A monomial may contain the existing local operations, pair sources and pair
effects, together with transfers of finite-dimensional registers. Expanding
each transfer in an orthonormal basis gives an actual list of the existing
monomials. The number of terms and absolute coefficient sum are exactly the
product of the transferred dimensions, and the pair-effect count is unchanged.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-message-resources-messagemonomial-01
TNLean.PEPS.PairEffect.MessageMonomial
Provenance-ID: 8769-message-resources-messagemonomial-02
TNLean.PEPS.PairEffect.MessageMonomial.IsAllowed
Provenance-ID: 8769-message-resources-messagemonomial-03
TNLean.PEPS.PairEffect.MessageMonomial.effectCount
Provenance-ID: 8769-message-resources-messagemonomial-04
TNLean.PEPS.PairEffect.MessageMonomial.eval
Provenance-ID: 8769-message-resources-messagemonomial-05
TNLean.PEPS.PairEffect.MessageMonomial.eval_expand
Provenance-ID: 8769-message-resources-messagemonomial-06
TNLean.PEPS.PairEffect.MessageMonomial.expand
Provenance-ID: 8769-message-resources-messagemonomial-07
TNLean.PEPS.PairEffect.MessageMonomial.expansion_size
Provenance-ID: 8769-message-resources-messagemonomial-08
TNLean.PEPS.PairEffect.MessageMonomial.expansion_size_le
Provenance-ID: 8769-message-resources-messagemonomial-09
TNLean.PEPS.PairEffect.MessageMonomial.expansion_size_le_of_power_bounds
Provenance-ID: 8769-message-resources-messagemonomial-10
TNLean.PEPS.PairEffect.MessageMonomial.isAllowed_effectCount_expand
Provenance-ID: 8769-message-resources-messagemonomial-11
TNLean.PEPS.PairEffect.MessageMonomial.messageDimensions
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- An existing monomial, a finite-dimensional identity transfer, or their
chronological composition. Only a transferred register changes its owner;
all spectator registers remain literal tensor factors. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 32–43. -/
inductive MessageMonomial : Layout P → Layout P → Type 1
  | segment {a b : Layout P} (M : PartyChain a b) : MessageMonomial a b
  | transfer (sender receiver : P) (H : HSpace) [FiniteDimensional ℂ H]
      (tail : Layout P) : MessageMonomial (⟨sender, H⟩ :: tail) (⟨receiver, H⟩ :: tail)
  | comp {a b c : Layout P} (M : MessageMonomial a b) (N : MessageMonomial b c) :
      MessageMonomial a c

namespace MessageMonomial

/-- The literal operator of the monomial, before any expansion of messages.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43. -/
def eval : {a b : Layout P} → MessageMonomial a b → Mem a →L[ℂ] Mem b
  | _, _, .segment M => M.toEffectChain.eval
  | _, _, @MessageMonomial.transfer _ _ _ H _ tail =>
      ContinuousLinearMap.id ℂ (H ⊗[ℂ] Mem tail)
  | _, _, .comp M N => N.eval ∘L M.eval

/-- The original monomial segments are allowed; finite-dimensional identity
transfers require no further normalization hypothesis. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
def IsAllowed : {a b : Layout P} → MessageMonomial a b → Prop
  | _, _, .segment M => M.IsAllowed
  | _, _, @MessageMonomial.transfer .. => True
  | _, _, .comp M N => M.IsAllowed ∧ N.IsAllowed

/-- The dimensions of all actual message occurrences, in chronological order.
Its length counts messages with their original multiplicities. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
def messageDimensions : {a b : Layout P} → MessageMonomial a b → List ℕ
  | _, _, .segment _ => []
  | _, _, @MessageMonomial.transfer _ _ _ H _ _ => [Module.finrank ℂ H]
  | _, _, .comp M N => M.messageDimensions ++ N.messageDimensions

/-- The number of original pair effects; message transfers introduce none.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
def effectCount : {a b : Layout P} → MessageMonomial a b → ℕ
  | _, _, .segment M => M.toEffectChain.effectCount
  | _, _, @MessageMonomial.transfer .. => 0
  | _, _, .comp M N => M.effectCount + N.effectCount

/-- Expand every actual message in a finite orthonormal basis and compose the
resulting lists. The basis is chosen from finite-dimensionality; no expansion
is supplied as an assumption. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 32–43. -/
def expand : {a b : Layout P} → MessageMonomial a b → PartyGate a b
  | _, _, .segment M => [(1, M)]
  | _, _, @MessageMonomial.transfer _ sender receiver H _ tail =>
      PartyGate.transfer sender receiver H (stdOrthonormalBasis ℂ H) tail
  | _, _, .comp M N => PartyGate.comp M.expand N.expand

/-- The constructed expansion evaluates to the original monomial, on its actual
input and output memories. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 32–43. -/
theorem eval_expand {a b : Layout P} (M : MessageMonomial a b) :
    gate (toGate M.expand) = M.eval := by
  induction M with
  | segment M => simp only [expand, toGate, gate, one_smul, add_zero, eval]
  | transfer sender receiver H tail => exact PartyGate.eval_transfer _ _ _ _ _
  | comp M N ihM ihN =>
      rw [expand, PartyGate.gate_comp, ihM, ihN]
      rfl

/-- Every expanded branch is allowed and has exactly the original number of
pair effects. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 32–43 and 143–149. -/
theorem isAllowed_effectCount_expand {a b : Layout P} (M : MessageMonomial a b)
    (hM : M.IsAllowed) :
    ∀ t ∈ M.expand, t.2.IsAllowed ∧ t.2.toEffectChain.effectCount = M.effectCount := by
  induction M with
  | segment M =>
      simpa only [expand, List.mem_singleton, forall_eq, effectCount, and_true, IsAllowed] using hM
  | transfer sender receiver H tail =>
      exact fun _ ht ↦ PartyGate.isAllowed_effectCount_transfer _ _ _ _ _ ht
  | comp M N ihM ihN =>
      intro t ht
      obtain ⟨l, hl, k, hk, rfl⟩ := PartyGate.mem_comp.mp ht
      exact ⟨PartyChain.isAllowed_comp _ _ (ihM hM.1 l hl).1 (ihN hM.2 k hk).1,
        (PartyChain.effectCount_comp _ _).trans
          (congrArg₂ Nat.add (ihM hM.1 l hl).2 (ihN hM.2 k hk).2)⟩

/-- Both the literal number of branches and the absolute coefficient sum are
the product of the dimensions of the actual message occurrences. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
theorem expansion_size {a b : Layout P} (M : MessageMonomial a b) :
    M.expand.length = M.messageDimensions.prod ∧
      (M.expand.map fun t ↦ ‖t.1‖).sum = (M.messageDimensions.prod : ℝ) := by
  induction M with
  | segment M => simp [expand, messageDimensions]
  | transfer sender receiver H tail =>
      simp only [expand, PartyGate.length_transfer, PartyGate.sum_norm_coeff_transfer,
        Fintype.card_fin, messageDimensions, List.prod_cons, List.prod_nil, mul_one,
        and_self]
  | comp M N ihM ihN =>
      simp only [expand, PartyGate.length_comp, PartyGate.sum_norm_comp,
        messageDimensions, List.prod_append, Nat.cast_mul, ihM.1, ihM.2, ihN.1, ihN.2,
        and_self]

/-- At most `m` messages of dimension at most `D ≥ 1` contribute at most
`D ^ m` branches and the same bound on the absolute coefficient sum. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
theorem expansion_size_le {a b : Layout P} (M : MessageMonomial a b)
    (D : ℝ) (m : ℕ) (hD : 1 ≤ D)
    (hd : ∀ d ∈ M.messageDimensions, (d : ℝ) ≤ D)
    (hm : M.messageDimensions.length ≤ m) :
    (M.expand.length : ℝ) ≤ D ^ m ∧ (M.expand.map fun t ↦ ‖t.1‖).sum ≤ D ^ m := by
  have hp : (M.messageDimensions.prod : ℝ) ≤ D ^ m := by
    rw [Nat.cast_list_prod]
    exact (List.prod_map_le_pow_length₀ (f := Nat.castRingHom ℝ)
      (fun d _ ↦ Nat.cast_nonneg d) hd).trans
      (pow_le_pow_right₀ hD hm)
  exact ⟨(congrArg (Nat.cast : ℕ → ℝ) M.expansion_size.1).trans_le hp,
    M.expansion_size.2.trans_le hp⟩

/-- A bounded number of polynomial-dimensional messages increases both the
actual monomial count and coefficient sum by only a polynomial factor. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149. -/
theorem expansion_size_le_of_power_bounds {a b : Layout P} (M : MessageMonomial a b)
    (L C_D : ℝ) (v m : ℕ) (hL : 1 ≤ L) (hC : 1 ≤ C_D)
    (hd : ∀ d ∈ M.messageDimensions, (d : ℝ) ≤ C_D * L ^ v)
    (hm : M.messageDimensions.length ≤ m) :
    (M.expand.length : ℝ) ≤ C_D ^ m * L ^ (v * m) ∧
      (M.expand.map fun t ↦ ‖t.1‖).sum ≤ C_D ^ m * L ^ (v * m) := by
  have h := M.expansion_size_le (C_D * L ^ v) m
    (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hL)) hd hm
  simpa only [mul_pow, ← pow_mul] using h

end MessageMonomial
end TNLean.PEPS.PairEffect
