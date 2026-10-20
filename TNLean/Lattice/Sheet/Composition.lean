/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.FrontRegisters

/-!
# Composing a monomial with words

A monomial of the distributed-circuit calculus (`PairEffect.PartyChain`) may be preceded or
followed by a word (`PairEffect.Word`) without changing its shape: the word is absorbed into the
first or the last private step. The bounded changes of the polynomial-PEPS manuscript are built
this way, a birth or a death being a grouping word, a monomial on the grouped registers and an
ungrouping word. This file records the composition and its effect on the allowedness, the
parties used and the numbers of pair sources and pair effects.

## Main definitions

* `PairEffect.PartyChain.precomp`, `PairEffect.PartyChain.postcomp`: a monomial composed with
  words.

## Main results

* `PairEffect.PartyChain.eval_precomp`, `PairEffect.PartyChain.eval_postcomp`: the operators.
* `PairEffect.PartyChain.precomp_props`, `PairEffect.PartyChain.postcomp_props`: allowedness,
  parties and counts.

## References

* Polynomial-PEPS manuscript (September 24, 2026), bounded changes, `05-frames.tex`,
  lines 99–105; allowed monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open ContinuousLinearMap

/-! ### Composing a monomial with words -/

namespace TNLean.PEPS.PairEffect.PartyChain

variable {P : Type}

/-- A monomial preceded by a word. -/
def precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) : PartyChain ℓX ℓY → PartyChain ℓ₀ ℓY
  | final w' => final (.comp w w')
  | effect hpq α β ℓS w' η rest => effect hpq α β ℓS (.comp w w') η rest

/-- A monomial followed by a word. -/
def postcomp {ℓX ℓY ℓZ : Layout P} : PartyChain ℓX ℓY → Word ℓY ℓZ → PartyChain ℓX ℓZ
  | final w', w => final (.comp w' w)
  | effect hpq α β ℓS w' η rest, w => effect hpq α β ℓS w' η (rest.postcomp w)

theorem eval_precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) :
    (M : PartyChain ℓX ℓY) → (M.precomp w).toEffectChain.eval = M.toEffectChain.eval ∘L w.eval
  | final _ => rfl
  | effect .. => rfl

theorem eval_postcomp {ℓX ℓY ℓZ : Layout P} :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) →
      (M.postcomp w).toEffectChain.eval = w.eval ∘L M.toEffectChain.eval
  | final _, _ => rfl
  | effect _ _ _ _ _ _ rest, w => by
      change (rest.postcomp w).toEffectChain.eval ∘L _ ∘L _ = _
      rw [eval_postcomp rest w]
      rfl

theorem precomp_props {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) (S : Set P) (hw : w.IsAllowed)
    (hS : w.UsesOnly S) : (M : PartyChain ℓX ℓY) → M.IsAllowed → M.UsesOnly S →
      (M.precomp w).IsAllowed ∧ (M.precomp w).UsesOnly S ∧
        (M.precomp w).sourceCount = w.sourceCount + M.sourceCount ∧
        (M.precomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, hM, hMS => ⟨⟨hw, hM⟩, ⟨hS, hMS⟩, rfl, rfl⟩
  | effect .. , hM, hMS => ⟨⟨⟨hw, hM.1⟩, hM.2⟩, ⟨hMS.1, hMS.2.1, ⟨hS, hMS.2.2.1⟩, hMS.2.2.2⟩,
      by simp only [precomp, sourceCount, Word.sourceCount, Nat.add_assoc], rfl⟩

theorem postcomp_props {ℓX ℓY ℓZ : Layout P} (S : Set P) :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) → w.IsAllowed → w.UsesOnly S → M.IsAllowed →
      M.UsesOnly S → (M.postcomp w).IsAllowed ∧ (M.postcomp w).UsesOnly S ∧
        (M.postcomp w).sourceCount = M.sourceCount + w.sourceCount ∧
        (M.postcomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, _, hw, hS, hM, hMS => ⟨⟨hM, hw⟩, ⟨hMS, hS⟩, rfl, rfl⟩
  | effect _ _ _ _ _ _ rest, w, hw, hS, hM, hMS => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := postcomp_props S rest w hw hS hM.2.2 hMS.2.2.2
      refine ⟨⟨hM.1, hM.2.1, h₁⟩, ⟨hMS.1, hMS.2.1, hMS.2.2.1, h₂⟩, ?_, ?_⟩
      · simp only [postcomp, sourceCount, h₃, Nat.add_assoc]
      · change (rest.postcomp w).toEffectChain.effectCount + 1 = _
        rw [h₄]

end TNLean.PEPS.PairEffect.PartyChain
