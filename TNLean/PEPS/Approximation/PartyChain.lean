/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-!
# Allowed monomials on a party layout

This file places the monomials of `TNLean.PEPS.PairEffect` on parties.  An allowed monomial
(`PartyChain`) consists of source-only words separated by pair effects: an effect contracts a
register `ℂ^α` of a party `p` and a register `ℂ^β` of another party `q` with a normalized bra.
Its operator is the `EffectChain` of `TNLean.PEPS.Approximation.PairEffectElimination`
(`PartyChain.toEffectChain`), so the error, count and coefficient bounds proved there apply.
Registers, source-only words and stacks of pair registers are defined in
`TNLean.PEPS.Approximation.PartyWord`.

In the replacement of Lemma 5.1, the stack of an effect occurrence on `(p, q)` consists of `m`
pair registers `ℂ^α ⊗ ℂ^β`, the `ℂ^α` half owned by `p` and the `ℂ^β` half owned by `q`.  The
insertions are source-only words (`stackIso_insWord`), so each term of a replaced monomial is
the operator of a source-only word (`PartyChain.replaceTerm_toEffectChain`), and the ideal
content of the stacks is prepared by pair sources (`PartyChain.stackAppIso_prepStack`).  The
expansion of a whole gate is assembled in `TNLean.PEPS.Approximation.PartyLayout`.

## Main definitions

* `PairEffect.PartyChain` : allowed monomials with pair effects on named parties.
* `PairEffect.PartyChain.replaceWord` : the terms of a replaced monomial as source-only words.
* `PairEffect.PartyChain.stackAppIso` : the identification of the stack layout with the stack
  space of the effect chain.

## Main results

* `PairEffect.PartyChain.replaceTerm_toEffectChain` : each term of a replaced monomial is the
  operator of a source-only word.
* `PairEffect.PartyChain.owner_stackRegs` : the stack registers are owned by the endpoint
  parties of the effects.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

open EuclideanSpace CyclicInsertion ContinuousLinearMap

variable {P : Type}

/-! ### Allowed monomials on a party layout -/

/-- An allowed monomial on a party layout: source-only words separated by pair effects.

* `final w` is the source-only word `w`.
* `effect hpq α β ℓS w η rest` applies the source-only word `w`, which ends with a register
  `ℂ^α` of the party `p` and a register `ℂ^β` of the party `q ≠ p` in front of the registers
  `ℓS`, contracts these two registers with the bra `⟨η|`, and continues with `rest`.

Effects are written on Euclidean registers `ℂ^α` and `ℂ^β` at the front of the layout.  This
is a convention, not a restriction: an effect on finite-dimensional registers `U` of `p` and
`V` of `q` anywhere in the layout takes this form after a local isometric equivalence
`U ≅ ℂ^α` of `p`, one `V ≅ ℂ^β` of `q`, and exchanges of tensor factors, all absorbed into the
preceding source-only word without changing its operator norm or the effect's coefficient.

Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
lines 32–35: compositions of local contractions, preparations of normalized vectors shared
between two participating parties, and contractions by normalized bras shared between two
participating parties. -/
inductive PartyChain : Layout P → Layout P → Type 1
  | final {ℓX ℓY : Layout P} (w : Word ℓX ℓY) : PartyChain ℓX ℓY
  | effect {ℓX ℓY : Layout P} {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [Fintype β]
      (ℓS : Layout P) (w : Word ℓX (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS))
      (η : EuclideanSpace ℂ (α × β)) (rest : PartyChain ℓS ℓY) : PartyChain ℓX ℓY

namespace PartyChain

/-- The monomial as a chain of contractions and pair effects. -/
@[reducible] def toEffectChain :
    {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → EffectChain (Mem ℓX) (Mem ℓY)
  | _, _, final w => .final w.eval
  | _, _, effect (p := p) (q := q) _ α β ℓS w η rest =>
      .effect α β (Mem ℓS) (isoL (pairHeadIso (p := p) (q := q) (α := α) (β := β) ℓS) ∘L w.eval)
        η rest.toEffectChain

/-- A monomial is allowed when its words are allowed and its pair effects are normalized.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Prop
  | _, _, final w => w.IsAllowed
  | _, _, effect _ _ _ _ w η rest => w.IsAllowed ∧ ‖η‖ = 1 ∧ rest.IsAllowed

theorem isAllowed_toEffectChain : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.IsAllowed → M.toEffectChain.IsAllowed
  | _, _, final w, h => w.norm_eval_le_one h
  | _, _, effect _ _ _ _ w _ rest, h =>
      ⟨norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (w.norm_eval_le_one h.1), h.2.1, isAllowed_toEffectChain rest h.2.2⟩

/-- The endpoint parties of the pair effects, in order. -/
def effectParties : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → List (P × P)
  | _, _, final _ => []
  | _, _, effect (p := p) (q := q) _ _ _ _ _ _ rest => (p, q) :: rest.effectParties

theorem length_effectParties : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    M.effectParties.length = M.toEffectChain.effectCount
  | _, _, final _ => rfl
  | _, _, effect _ _ _ _ _ _ rest => by
      simp only [effectParties, toEffectChain, List.length_cons, length_effectParties rest]

variable (m : ℕ)

/-- The stacks of all effect occurrences, in front of the layout `ℓ`. -/
@[reducible] def stackApp : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Layout P → Layout P
  | _, _, final _, ℓ => ℓ
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest, ℓ => pairsOn p q α β m (stackApp rest ℓ)

/-- The registers of the stacks of all effect occurrences.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 99–102: each
occurrence has its own output stack of `m` pair registers, with the dimensions and endpoint
parties of its vector `η`. -/
def stackRegs : {ℓX ℓY : Layout P} → PartyChain ℓX ℓY → Layout P
  | _, _, final _ => []
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest => pairRegs p q α β m ++ stackRegs rest

theorem stackApp_eq : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    M.stackApp m ℓ = M.stackRegs m ++ ℓ
  | _, _, final _, _ => rfl
  | _, _, effect _ _ _ _ _ _ rest, ℓ => by
      rw [stackApp, stackRegs, pairsOn_eq, stackApp_eq rest ℓ, List.append_assoc]

/-- **Ownership of the stacks.** The stack registers of a monomial are owned by the endpoint
parties of its effects: for each effect on `(p, q)`, `m` pair registers, each consisting of a
register of `p` and a register of `q`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
67–68 and 99–102. -/
theorem owner_stackRegs : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (M.stackRegs m).map Reg.owner =
      M.effectParties.flatMap fun e => (List.replicate m [e.1, e.2]).flatten
  | _, _, final _ => rfl
  | _, _, effect _ _ _ _ _ _ rest => by
      simp only [stackRegs, effectParties, List.map_append, map_owner_pairRegs,
        owner_stackRegs rest, List.flatMap_cons]

/-- The terms of the replaced monomial as source-only words: the effect occurrence number `i`
is replaced by the insertion at position `κ i`, and its stack stays idle afterwards.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 96–106 and
121–123. -/
def replaceWord : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (Fin M.toEffectChain.effectCount → Fin m) → Word ℓX (M.stackApp m ℓY)
  | _, _, final w, _ => w
  | _, _, effect hpq _ _ _ w η rest, κ =>
      .comp w (.comp (insWord hpq η m (κ (0 : Fin (rest.toEffectChain.effectCount + 1))))
        (framePairs m (replaceWord rest (Fin.tail κ))))

theorem isAllowed_replaceWord : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → M.IsAllowed →
    ∀ κ, (M.replaceWord m κ).IsAllowed
  | _, _, final _, h, _ => h
  | _, _, effect hpq _ _ _ _ η rest, h, _ =>
      ⟨h.1, isAllowed_insWord hpq η h.2.1 m _,
        isAllowed_framePairs _ (isAllowed_replaceWord rest h.2.2 _) _⟩

/-- The identification of the stack layout with the stack space of the effect chain. -/
def stackAppIso : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    Mem (M.stackApp m ℓ) ≃ₗᵢ[ℂ] Mem ℓ ⊗[ℂ] M.toEffectChain.stackSpace m
  | _, _, final _, ℓ => (TensorProduct.ridIsometry ℂ (Mem ℓ)).symm
  | _, _, effect (p := p) (q := q) _ α β _ _ _ rest, ℓ =>
      ((stackIso p q α β m (stackApp m rest ℓ)).trans ((stackAppIso rest ℓ).lTensor _)).trans
        (leftCommIso _ _ _)

theorem stackAppIso_final {ℓX ℓY : Layout P} (w : Word ℓX ℓY) (ℓ : Layout P) (x : Mem ℓ) :
    (final w).stackAppIso m ℓ x = x ⊗ₜ (1 : ℂ) :=
  rfl

theorem stackAppIso_effect {ℓX ℓY : Layout P} {p q : P} (hpq : p ≠ q) (α β : Type)
    [Fintype α] [Fintype β] (ℓS : Layout P) (w : Word ℓX (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS))
    (η : EuclideanSpace ℂ (α × β)) (rest : PartyChain ℓS ℓY) (ℓ : Layout P)
    (z : Mem ((effect hpq α β ℓS w η rest).stackApp m ℓ)) :
    (effect hpq α β ℓS w η rest).stackAppIso m ℓ z =
      leftCommL _ _ _ ((rest.stackAppIso m ℓ).lTensor _
        (stackIso p q α β m (rest.stackApp m ℓ) z)) :=
  rfl

/-- **Each term of a replaced monomial is source-only.**  The term of the replaced monomial with
insertion positions `κ` is the operator of the allowed source-only word `replaceWord`, read on
the stack layout.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66 and 96–123. -/
theorem replaceTerm_toEffectChain : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (κ : Fin M.toEffectChain.effectCount → Fin m) →
    M.toEffectChain.replaceTerm m κ = isoL (M.stackAppIso m ℓY) ∘L (M.replaceWord m κ).eval
  | _, _, final _, _ => rfl
  | _, ℓY, effect (p := p) (q := q) hpq α β ℓS w η rest, κ => by
      have ih := replaceTerm_toEffectChain rest (Fin.tail κ)
      have key (u : Mem (⟨p, euc α⟩ :: ⟨q, euc β⟩ :: ℓS)) :
          (rest.toEffectChain.replaceTerm m (Fin.tail κ)).lTensor _
              ((insertAt η (κ (0 : Fin (rest.toEffectChain.effectCount + 1)))).rTensor _
                (pairHeadIso ℓS u)) =
            (rest.stackAppIso m ℓY).lTensor _ (stackIso p q α β m _
              ((framePairs m (rest.replaceWord m (Fin.tail κ))).eval
                ((insWord hpq η m (κ (0 : Fin (rest.toEffectChain.effectCount + 1)))).eval
                  u))) := by
        rw [iso_lTensor_apply, ih, stackIso_framePairs, stackIso_insWord, lTensor_comp_apply]
      refine ContinuousLinearMap.ext fun x => ?_
      exact congrArg (leftCommL _ _ _) (key (w.eval x))

/-- Preparation of the ideal content `η^{⊗ m}` of every stack by pair sources. -/
def prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (ℓ : Layout P) →
    Word ℓ (M.stackApp m ℓ)
  | _, _, final _, ℓ => .id ℓ
  | _, _, effect hpq _ _ _ _ η rest, ℓ => .comp (prepStack rest ℓ) (prepWord hpq η m _)

theorem isAllowed_prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → M.IsAllowed →
    ∀ ℓ, (M.prepStack m ℓ).IsAllowed
  | _, _, final _, _, _ => trivial
  | _, _, effect hpq _ _ _ _ η rest, h, ℓ =>
      ⟨isAllowed_prepStack rest h.2.2 ℓ, isAllowed_prepWord hpq η h.2.1 m _⟩

theorem stackAppIso_prepStack : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    (ℓ : Layout P) → (x : Mem ℓ) →
    M.stackAppIso m ℓ ((M.prepStack m ℓ).eval x) = x ⊗ₜ M.toEffectChain.stackVector m
  | _, _, final _, _, _ => rfl
  | _, _, effect hpq α β ℓS w η rest, ℓ, x => by
      simp only [prepStack, Word.eval_comp, comp_apply]
      rw [stackAppIso_effect, iso_lTensor_apply, stackIso_prepWord, lTensor_tmul]
      simp only [isoL_apply]
      rw [stackAppIso_prepStack rest ℓ x, leftCommL_tmul]
      rfl

/-- A word on the layout `ℓ` framed by all stacks. -/
def frameStack {ℓ ℓ' : Layout P} : {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) →
    Word ℓ ℓ' → Word (M.stackApp m ℓ) (M.stackApp m ℓ')
  | _, _, final _, W => W
  | _, _, effect _ _ _ _ _ _ rest, W => framePairs m (frameStack rest W)

theorem isAllowed_frameStack {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') (hW : W.IsAllowed) :
    {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (M.frameStack m W).IsAllowed
  | _, _, final _ => hW
  | _, _, effect _ _ _ _ _ _ rest => isAllowed_framePairs _ (isAllowed_frameStack W hW rest) _

theorem stackAppIso_frameStack {ℓ ℓ' : Layout P} (W : Word ℓ ℓ') :
    {ℓX ℓY : Layout P} → (M : PartyChain ℓX ℓY) → (z : Mem (M.stackApp m ℓ)) →
    M.stackAppIso m ℓ' ((M.frameStack m W).eval z) = W.eval.rTensor _ (M.stackAppIso m ℓ z)
  | _, _, final _, _ => rfl
  | _, _, effect (p := p) (q := q) hpq α β ℓS w η rest, z => by
      have ih : isoL (rest.stackAppIso m ℓ') ∘L (rest.frameStack m W).eval =
          W.eval.rTensor _ ∘L isoL (rest.stackAppIso m ℓ) :=
        ContinuousLinearMap.ext fun t => stackAppIso_frameStack W rest t
      have key : (isoL (rest.stackAppIso m ℓ')).lTensor _
            (stackIso p q α β m _ ((framePairs m (rest.frameStack m W)).eval z)) =
          (W.eval.rTensor _).lTensor _
            ((isoL (rest.stackAppIso m ℓ)).lTensor _ (stackIso p q α β m _ z)) := by
        rw [stackIso_framePairs, lTensor_comp_apply, ih, lTensor_comp, comp_apply]
      rw [stackAppIso_effect, iso_lTensor_apply, stackAppIso_effect, iso_lTensor_apply]
      exact (congrArg (leftCommL _ _ _) key).trans (leftCommL_lTensor_rTensor _ _)

end PartyChain

end TNLean.PEPS.PairEffect
