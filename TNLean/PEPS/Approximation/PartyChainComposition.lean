/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyLayout

/-!
# Composition of the existing distributed monomials

Compose the actual source words and pair effects without changing their order.
This permits local basis expansions of messages to be inserted among arbitrary
allowed monomial segments. Pair-effect counts add, and every resulting monomial
remains allowed when the original segments are allowed.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.PartyChain
open ContinuousLinearMap
variable {P : Type} {a b c : Layout P}

/-- Prepend a source-only word to a monomial, retaining its pair effects. -/
def prependWord (w : Word a b) (M : PartyChain b c) : PartyChain a c := by
  cases M with
  | final v => exact .final (.comp w v)
  | effect hpq α β tail v η rest => exact .effect hpq α β tail (.comp w v) η rest

/-- Prepending applies the original word before the original monomial. -/
theorem eval_prependWord (w : Word a b) (M : PartyChain b c) :
    (prependWord w M).toEffectChain.eval = M.toEffectChain.eval ∘L w.eval := by
  cases M <;> simp only [prependWord, toEffectChain, EffectChain.eval, Word.eval_comp,
    comp_assoc]

/-- An allowed word may precede an allowed monomial. -/
theorem isAllowed_prependWord (w : Word a b) (M : PartyChain b c)
    (hw : w.IsAllowed) (hM : M.IsAllowed) : (prependWord w M).IsAllowed := by
  cases M with
  | final v => exact ⟨hw, hM⟩
  | effect _ _ _ _ _ _ _ => exact ⟨⟨hw, hM.1⟩, hM.2⟩

/-- Prepending a source-only word introduces no pair effects. -/
theorem effectCount_prependWord (w : Word a b) (M : PartyChain b c) :
    (prependWord w M).toEffectChain.effectCount = M.toEffectChain.effectCount := by
  cases M <;> rfl

/-- Compose two actual monomials on their common intermediate register list. -/
def comp (M : PartyChain a b) (N : PartyChain b c) : PartyChain a c := by
  induction M with
  | final w => exact prependWord w N
  | effect hpq α β tail w η rest ih => exact .effect hpq α β tail w η (ih N)

/-- The composed monomial evaluates to the chronological product. -/
theorem eval_comp (M : PartyChain a b) (N : PartyChain b c) :
    (comp M N).toEffectChain.eval = N.toEffectChain.eval ∘L M.toEffectChain.eval := by
  induction M with
  | final w => exact eval_prependWord w N
  | effect hpq α β tail w η rest ih =>
      change (comp rest N).toEffectChain.eval ∘L _ =
        N.toEffectChain.eval ∘L (rest.toEffectChain.eval ∘L _)
      rw [ih N, comp_assoc]

/-- Composition preserves allowedness of all local factors and normalized effects. -/
theorem isAllowed_comp (M : PartyChain a b) (N : PartyChain b c)
    (hM : M.IsAllowed) (hN : N.IsAllowed) : (comp M N).IsAllowed := by
  induction M with
  | final w => exact isAllowed_prependWord w N hM hN
  | effect _ _ _ _ _ _ _ ih => exact ⟨hM.1, hM.2.1, ih N hM.2.2 hN⟩

/-- Pair effects in a concatenated monomial are counted with their original multiplicities. -/
theorem effectCount_comp (M : PartyChain a b) (N : PartyChain b c) :
    (comp M N).toEffectChain.effectCount =
      M.toEffectChain.effectCount + N.toEffectChain.effectCount := by
  induction M with
  | final w => simpa only [comp, toEffectChain, EffectChain.effectCount, zero_add]
      using effectCount_prependWord w N
  | effect hpq α β tail w η rest ih =>
      change (comp rest N).toEffectChain.effectCount + 1 =
        (rest.toEffectChain.effectCount + 1) + N.toEffectChain.effectCount
      rw [ih N]
      omega

end TNLean.PEPS.PairEffect.PartyChain
