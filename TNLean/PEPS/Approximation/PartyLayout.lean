/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyWord

/-!
# Pair-effect elimination on a party layout

This file places the monomials of `TNLean.PEPS.PairEffect` on parties and proves the
statements of Lemma 5.1 `lem:effects` about parties: the replaced gate has an expansion
using only local contractions and normalized pair sources, and its additional registers are
owned by the endpoint parties of the eliminated effects.  Registers, source-only words and
stacks of pair registers are defined in `TNLean.PEPS.Approximation.PartyWord`.

An allowed monomial (`PartyChain`) consists of source-only words separated by pair effects:
an effect contracts a register `ℂ^α` of a party `p` and a register `ℂ^β` of another party
`q` with a normalized bra.  Its operator is the `EffectChain` of
`TNLean.PEPS.Approximation.PairEffectElimination` (`PartyChain.toEffectChain`), so the error,
count and coefficient bounds proved there apply.

In the replacement, the stack of an effect occurrence on `(p, q)` consists of `m` pair
registers `ℂ^α ⊗ ℂ^β`, the `ℂ^α` half owned by `p` and the `ℂ^β` half owned by `q`.  The
insertions are source-only words (`stackIso_insWord`).  This identifies the terms of the
expansion of the replaced gate with source-only words (`termList_toGate`), the common garbage
vector with a product of pair sources (`gateIso_prepGate`), and the additional registers with
the stacks (`gateOut_eq`).

**Scope restriction (combining sources):** the last clause of Lemma 5.1, that all sources on
the same pair of parties in the expansion may be combined into one normalized pair source
(`04-compression.tex`, lines 68–70), is formalized only for two pair sources prepared one
after the other (`eval_combineSources`), which is the tensor-product identity the source
gives as its proof (lines 125–127).  Moving the sources of a word past the operations on
other registers, so that all sources on one pair of parties become adjacent, is not
formalized; `partyPairEffectElimination` does not state this clause.  Documented in
`docs/paper-gaps/polypeps_pair_effects_party_layout.tex`.  Elimination: prove that every
allowed source-only word equals the preparation of all its sources followed by a word without
sources, then merge the sources pair by pair with `eval_combineSources`.

## Main definitions

* `PairEffect.PartyChain` : allowed monomials with pair effects on named parties.
* `PairEffect.PartyChain.replaceWord` : the terms of a replaced monomial as source-only words.
* `PairEffect.wordList` : the expansion of the replaced gate into source-only words.
* `PairEffect.gateOut`, `PairEffect.gateIso` : the output layout of the replaced gate and its
  identification with the output space of `PairEffect.replaceGate`.

## Main results

* `PairEffect.PartyChain.replaceTerm_toEffectChain` : each term of a replaced monomial is the
  operator of a source-only word.
* `PairEffect.termList_toGate` : the expansion of the replaced gate, term by term.
* `PairEffect.gateIso_prepGate` : the common garbage vector `Γ_m` is prepared by pair
  sources.
* `PairEffect.gateOut_eq`, `PairEffect.PartyChain.owner_stackRegs` : the additional registers
  and their owners.
* `PairEffect.eval_combineSources` : two adjacent sources on one pair of parties combine into
  one.
* `PairEffect.partyPairEffectElimination` : Lemma 5.1 `lem:effects`, except the clause on
  combining sources.

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
  | _, _, effect _ α β ℓS w η rest =>
      .effect α β (Mem ℓS) (isoL (pairHeadIso ℓS) ∘L w.eval) η rest.toEffectChain

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
  | _, _, effect hpq α β ℓS w η rest, κ => by
      have ih := replaceTerm_toEffectChain rest (Fin.tail κ)
      simp only [toEffectChain, EffectChain.replaceTerm]
      rw [ih]
      ext1 x
      simp only [replaceWord, Word.eval_comp, comp_apply, isoL_apply]
      rw [stackAppIso_effect, iso_lTensor_apply, stackIso_framePairs, stackIso_insWord,
        lTensor_comp_apply]

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
  | _, _, effect hpq α β ℓS w η rest, z => by
      have ih : isoL (rest.stackAppIso m ℓ') ∘L (rest.frameStack m W).eval =
          W.eval.rTensor _ ∘L isoL (rest.stackAppIso m ℓ) :=
        ContinuousLinearMap.ext fun t => stackAppIso_frameStack W rest t
      rw [stackAppIso_effect, iso_lTensor_apply, stackAppIso_effect, iso_lTensor_apply]
      simp only [frameStack]
      rw [stackIso_framePairs, lTensor_comp_apply, ih, lTensor_comp, comp_apply,
        leftCommL_lTensor_rTensor]

end PartyChain

/-! ### Gate expansions on a party layout -/

/-- A gate expansion `G = ∑_ξ c_ξ M_ξ` into monomials on a party layout.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
lines 55–57. -/
abbrev PartyGate (ℓX ℓY : Layout P) : Type 1 := List (ℂ × PartyChain ℓX ℓY)

variable {ℓX ℓY : Layout P} (m : ℕ)

/-- The gate expansion of effect chains of a gate expansion on a party layout. -/
@[reducible] def toGate : PartyGate ℓX ℓY → GateExpansion (Mem ℓX) (Mem ℓY)
  | [] => []
  | p :: L => (p.1, p.2.toEffectChain) :: toGate L

theorem length_toGate : (L : PartyGate ℓX ℓY) → (toGate L).length = L.length
  | [] => rfl
  | _ :: L => by simp only [toGate, List.length_cons, length_toGate L]

theorem map_norm_toGate : (L : PartyGate ℓX ℓY) →
    (toGate L).map (fun p => ‖p.1‖) = L.map fun p => ‖p.1‖
  | [] => rfl
  | _ :: L => by simp only [toGate, List.map_cons, map_norm_toGate L]

theorem mem_toGate {L : PartyGate ℓX ℓY} {p : ℂ × EffectChain (Mem ℓX) (Mem ℓY)}
    (hp : p ∈ toGate L) : ∃ p' ∈ L, p = (p'.1, p'.2.toEffectChain) := by
  induction L with
  | nil => simp [toGate] at hp
  | cons a L ih =>
      simp only [toGate, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨a, List.mem_cons_self, rfl⟩
      · obtain ⟨p', hp', rfl⟩ := ih hp
        exact ⟨p', List.mem_cons_of_mem _ hp', rfl⟩

/-- The output layout of the replaced gate: the stacks of all effect occurrences of all
monomials in front of the output layout of the gate. -/
@[reducible] def gateOut : PartyGate ℓX ℓY → Layout P
  | [] => ℓY
  | p :: L => p.2.stackApp m (gateOut L)

/-- The identification of the output layout of the replaced gate with the output space
`Y ⊗ inventory` of `replaceGate`. -/
def gateIso : (L : PartyGate ℓX ℓY) → Mem (gateOut m L) ≃ₗᵢ[ℂ] Mem ℓY ⊗[ℂ] inventory m (toGate L)
  | [] => (TensorProduct.ridIsometry ℂ (Mem ℓY)).symm
  | p :: L => (p.2.stackAppIso m (gateOut m L)).trans
      (((gateIso L).rTensor _).trans ((TensorProduct.assocIsometry ℂ _ _ _).trans
        ((TensorProduct.commIsometry ℂ _ _).lTensor _)))

theorem gateIso_nil (x : Mem ℓY) : gateIso m ([] : PartyGate ℓX ℓY) x = x ⊗ₜ (1 : ℂ) :=
  rfl

theorem gateIso_cons (p : ℂ × PartyChain ℓX ℓY) (L : PartyGate ℓX ℓY)
    (z : Mem (gateOut m (p :: L))) :
    gateIso m (p :: L) z =
      (TensorProduct.commIsometry ℂ (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)).lTensor (Mem ℓY)
        (TensorProduct.assocIsometry ℂ (Mem ℓY) (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)
          ((gateIso m L).rTensor (p.2.toEffectChain.stackSpace m)
            (p.2.stackAppIso m (gateOut m L) z))) :=
  rfl

theorem gateIso_cons_clm (p : ℂ × PartyChain ℓX ℓY) (L : PartyGate ℓX ℓY) :
    isoL (gateIso m (p :: L)) =
      isoL ((TensorProduct.commIsometry ℂ (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)).lTensor (Mem ℓY)) ∘L
        isoL (TensorProduct.assocIsometry ℂ (Mem ℓY) (inventory m (toGate L))
          (p.2.toEffectChain.stackSpace m)) ∘L
        isoL ((gateIso m L).rTensor (p.2.toEffectChain.stackSpace m)) ∘L
        isoL (p.2.stackAppIso m (gateOut m L)) :=
  rfl

/-- Preparation of the common garbage vector `Γ_m` by pair sources. -/
def prepGate : (L : PartyGate ℓX ℓY) → Word ℓY (gateOut m L)
  | [] => .id ℓY
  | p :: L => .comp (prepGate L) (p.2.prepStack m (gateOut m L))

theorem isAllowed_prepGate : (L : PartyGate ℓX ℓY) → (∀ p ∈ L, p.2.IsAllowed) →
    (prepGate m L).IsAllowed
  | [], _ => trivial
  | p :: L, h => ⟨isAllowed_prepGate L fun q hq => h q (List.mem_cons_of_mem _ hq),
      p.2.isAllowed_prepStack m (h p List.mem_cons_self) _⟩

/-- **The garbage vector is prepared by pair sources.** The word `prepGate` prepares, by
normalized pair sources on the endpoint parties, the common garbage vector `Γ_m` appended in
every branch.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 103–112. -/
theorem gateIso_prepGate : (L : PartyGate ℓX ℓY) → (x : Mem ℓY) →
    gateIso m L ((prepGate m L).eval x) = x ⊗ₜ inventoryVector m (toGate L)
  | [], x => rfl
  | p :: L, x => by
      simp only [prepGate, Word.eval_comp, comp_apply]
      rw [gateIso_cons, PartyChain.stackAppIso_prepStack, iso_rTensor_apply, rTensor_tmul]
      simp only [isoL_apply]
      rw [gateIso_prepGate L x]
      simp only [TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, iso_lTensor_apply,
        lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
      rfl

/-- The expansion of the replaced gate into weighted source-only words: the term of a
monomial `c M` with `n` effects and insertion positions `κ` has coefficient `c / m^n`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–67 and 103–125. -/
def wordList : (L : PartyGate ℓX ℓY) → List (ℂ × Word ℓX (gateOut m L))
  | [] => []
  | p :: L =>
      (Finset.univ.toList.map fun κ => (p.1 * ((m : ℂ) ^ p.2.toEffectChain.effectCount)⁻¹,
        Word.comp (p.2.replaceWord m κ) (p.2.frameStack m (prepGate m L)))) ++
      (wordList L).map fun q => (q.1, Word.comp q.2 (p.2.prepStack m (gateOut m L)))

/-- **Each term of the replaced gate is source-only.** The expansion `termList` of the replaced
gate is, term by term, the expansion into the source-only words `wordList`, read on the output
layout `gateOut` through `gateIso`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66 and 103–125. -/
theorem termList_toGate : (L : PartyGate ℓX ℓY) →
    termList m (toGate L) = (wordList m L).map fun q => (q.1, isoL (gateIso m L) ∘L q.2.eval)
  | [] => rfl
  | p :: L => by
      simp only [toGate, termList, wordList, List.map_append, List.map_map]
      congr 1
      · refine List.map_congr_left fun κ _ => Prod.ext rfl ?_
        dsimp only [Function.comp_apply]
        rw [PartyChain.replaceTerm_toEffectChain, gateIso_cons_clm]
        ext1 x
        simp only [Word.eval_comp, comp_apply, isoL_apply]
        rw [PartyChain.stackAppIso_frameStack, iso_rTensor_apply,
          rTensor_comp_apply, show isoL (gateIso m L) ∘L (prepGate m L).eval =
            appendRight (inventoryVector m (toGate L)) from
          ContinuousLinearMap.ext fun y => gateIso_prepGate m L y]
        induction (p.2.stackAppIso m ℓY ((p.2.replaceWord m κ).eval x)) using
          TensorProduct.inductionOn with
        | tmul y s =>
            simp only [rTensor_tmul, appendRight_apply, assocL_tmul,
              TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, iso_lTensor_apply,
              lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
        | add a b ha hb => simp only [map_add, ha, hb]
      · rw [termList_toGate L, List.map_map]
        refine List.map_congr_left fun q _ => Prod.ext rfl ?_
        dsimp only [Function.comp_apply]
        rw [gateIso_cons_clm]
        ext1 x
        simp only [Word.eval_comp, comp_apply, isoL_apply]
        rw [PartyChain.stackAppIso_prepStack, iso_rTensor_apply, rTensor_tmul]
        simp only [isoL_apply, appendLeft_apply]
        induction (gateIso m L (q.2.eval x)) using TensorProduct.inductionOn with
        | tmul y s =>
            simp only [leftCommL_tmul, TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul,
              iso_lTensor_apply, lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply,
              TensorProduct.comm_tmul]
        | add a b ha hb =>
            simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]

theorem isAllowed_wordList : (L : PartyGate ℓX ℓY) → (∀ p ∈ L, p.2.IsAllowed) →
    ∀ q ∈ wordList m L, q.2.IsAllowed
  | [], _ => by simp [wordList]
  | p :: L, h => by
      have hp := h p List.mem_cons_self
      have hL : ∀ q ∈ L, q.2.IsAllowed := fun q hq => h q (List.mem_cons_of_mem _ hq)
      intro q hq
      simp only [wordList, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨κ, _, rfl⟩ | ⟨q', hq', rfl⟩
      · exact ⟨p.2.isAllowed_replaceWord m hp κ,
          PartyChain.isAllowed_frameStack m _ (isAllowed_prepGate m L hL) p.2⟩
      · exact ⟨isAllowed_wordList L hL q' hq', p.2.isAllowed_prepStack m hp _⟩

/-- **Every term of the replaced gate is source-only.** Each term of the expansion `termList`
of the replaced gate, read on the output layout `gateOut`, is a composition of local
contractions and normalized pair sources.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
65–66. -/
theorem isSourceOnly_termList (L : PartyGate ℓX ℓY) (hL : ∀ p ∈ L, p.2.IsAllowed) :
    ∀ q ∈ termList m (toGate L), IsSourceOnly (isoL (gateIso m L).symm ∘L q.2) := by
  intro q hq
  rw [termList_toGate, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  refine ⟨w.2, isAllowed_wordList m L hL w hw, ?_⟩
  ext1 x
  simp only [comp_apply, isoL_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The additional registers of the replaced gate: the stacks of all effect occurrences. -/
theorem gateOut_eq : (L : PartyGate ℓX ℓY) →
    gateOut m L = (L.flatMap fun p => p.2.stackRegs m) ++ ℓY
  | [] => rfl
  | p :: L => by
      simp only [gateOut, PartyChain.stackApp_eq, gateOut_eq L, List.flatMap_cons,
        List.append_assoc]

/-! ### Combining pair sources -/

/-- The regrouping `(U ⊗ V) ⊗ (U' ⊗ V') ≅ (U ⊗ U') ⊗ (V ⊗ V')` of two pair vectors on the same
pair of parties. -/
def pairRegroup (U V U' V' : HSpace) :
    (U ⊗[ℂ] V) ⊗[ℂ] (U' ⊗[ℂ] V') ≃ₗᵢ[ℂ] (U ⊗[ℂ] U') ⊗[ℂ] (V ⊗[ℂ] V') :=
  (TensorProduct.assocIsometry ℂ U V (U' ⊗[ℂ] V')).trans <|
    ((((TensorProduct.assocIsometry ℂ V U' V').symm.trans
      (((TensorProduct.commIsometry ℂ V U').rTensor V').trans
        (TensorProduct.assocIsometry ℂ U' V V'))).lTensor U).trans
      (TensorProduct.assocIsometry ℂ U U' (V ⊗[ℂ] V')).symm)

theorem pairRegroup_tmul (U V U' V' : HSpace) (u : U) (v : V) (u' : U') (v' : V') :
    pairRegroup U V U' V' ((u ⊗ₜ v) ⊗ₜ (u' ⊗ₜ v')) = (u ⊗ₜ u') ⊗ₜ (v ⊗ₜ v') := by
  simp only [pairRegroup, LinearIsometryEquiv.trans_apply, iso_lTensor_apply, iso_rTensor_apply,
    TensorProduct.assocIsometry_apply, TensorProduct.assocIsometry_symm_apply,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, lTensor_tmul, rTensor_tmul,
    isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]

/-- Merging two registers of one party into one register. -/
def mergeIso (p : P) (U U' : HSpace) :
    Mem [⟨p, U⟩, ⟨p, U'⟩] ≃ₗᵢ[ℂ] Mem [⟨p, HSpace.of (U ⊗[ℂ] U')⟩] :=
  (TensorProduct.assocIsometry ℂ U U' ℂ).symm

/-- Two pair sources on the same pair of parties, followed by merging the two registers of each
party. -/
def combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    Word ℓ (⟨p, HSpace.of (U ⊗[ℂ] U')⟩ :: ⟨q, HSpace.of (V ⊗[ℂ] V')⟩ :: ℓ) :=
  .comp (.source hpq U' V' η' ℓ) <| .comp (.source hpq U V η _) <|
    .comp (.frame _ (.swap _ _ _)) <|
    .comp (.localMap p (ℓ₁ := [⟨p, U⟩, ⟨p, U'⟩]) (ℓ₂ := [⟨p, HSpace.of (U ⊗[ℂ] U')⟩])
      (by simp) (by simp) (isoL (mergeIso p U U')) (⟨q, V⟩ :: ⟨q, V'⟩ :: ℓ)) <|
    .frame _ (.localMap q (ℓ₁ := [⟨q, V⟩, ⟨q, V'⟩]) (ℓ₂ := [⟨q, HSpace.of (V ⊗[ℂ] V')⟩])
      (by simp) (by simp) (isoL (mergeIso q V V')) ℓ)

theorem isAllowed_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) {η : U ⊗[ℂ] V}
    {η' : U' ⊗[ℂ] V'} (hη : ‖η‖ = 1) (hη' : ‖η'‖ = 1) (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).IsAllowed :=
  ⟨hη', hη, trivial, LinearIsometry.norm_toContinuousLinearMap_le _,
    LinearIsometry.norm_toContinuousLinearMap_le _⟩

/-- **Combining pair sources.** Two pair sources `η` and `η'` on the same pair of parties,
followed by merging the two registers of each party, are the single pair source of the
regrouped vector `η ⊗ η'`, whose norm is `‖η‖ ‖η'‖`.

This is the tensor-product identity behind the last clause of Lemma 5.1; combining sources
that are not adjacent is not formalized (see the scope restriction in the module docstring).

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`, lines
68–70 and 125–127. -/
theorem eval_combineSources {p q : P} (hpq : p ≠ q) (U V U' V' : HSpace) (η : U ⊗[ℂ] V)
    (η' : U' ⊗[ℂ] V') (ℓ : Layout P) :
    (combineSources hpq U V U' V' η η' ℓ).eval =
        (Word.source hpq _ _ (pairRegroup U V U' V' (η ⊗ₜ η')) ℓ).eval ∧
      ‖pairRegroup U V U' V' (η ⊗ₜ η')‖ = ‖η‖ * ‖η'‖ := by
  refine ⟨?_, by rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul]⟩
  ext1 x
  induction η using TensorProduct.inductionOn with
  | add a b ha hb =>
      simp only [combineSources, Word.eval, comp_apply, appendLeft_apply] at ha hb ⊢
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul u v =>
      induction η' using TensorProduct.inductionOn with
      | add a b ha hb =>
          simp only [combineSources, Word.eval, comp_apply, appendLeft_apply] at ha hb ⊢
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]
      | tmul u' v' =>
          simp [combineSources, Word.eval, appendIso, mergeIso, pairRegroup_tmul,
            TensorProduct.assoc_symm_tmul, TensorProduct.lid_symm_apply,
            LinearIsometryEquiv.symm_lTensor]

/-! ### Lemma 5.1 on a party layout -/

/-- **Elimination of normalized pair effects** (Lemma 5.1 `lem:effects`).  Let
`G = ∑_ξ c_ξ M_ξ` be a gate expansion into `K` allowed monomials on a party layout, each with at
most `r` pair effects, and let `m ≥ 1`.  Then, with the replaced gate `G'_m = replaceGate` and
the common garbage vector `Γ_m = inventoryVector`:

* `Γ_m` is normalized and is prepared by the allowed source-only word `prepGate`;
* `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`;
* read on the output layout `gateOut` through `gateIso`, `G'_m` is the weighted sum of the
  allowed source-only words of `wordList`: local contractions and normalized pair sources;
  equivalently, every term of the expansion `termList` is source-only;
* there are at most `K m^r` such words, with absolute coefficient sum `∑_ξ |c_ξ|`;
* the output layout consists of the stacks of all effect occurrences followed by the output
  layout of `G`, and the stacks of a monomial are owned by the endpoint parties of its effects.

The source's participating parties are read as the parties named by the monomials: every
additional register is owned by an endpoint party of an effect of some monomial.  The clause
that all sources on one pair of parties may be combined into one is not stated here; only the
combination of two adjacent sources is formalized (`eval_combineSources`, see the scope
restriction in the module docstring).  The hypothesis that `G` is a contraction is not needed.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
`04-compression.tex`, lines 53–127. -/
theorem partyPairEffectElimination {m r : ℕ} (hm : m ≠ 0) (L : PartyGate ℓX ℓY)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.toEffectChain.effectCount ≤ r) :
    ‖inventoryVector m (toGate L)‖ = 1 ∧
    (∀ x, gateIso m L ((prepGate m L).eval x) = x ⊗ₜ inventoryVector m (toGate L)) ∧
    (prepGate m L).IsAllowed ∧
    ‖replaceGate m (toGate L) - appendRight (inventoryVector m (toGate L)) ∘L gate (toGate L)‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ∧
    replaceGate m (toGate L) =
      ((wordList m L).map fun q => q.1 • (isoL (gateIso m L) ∘L q.2.eval)).sum ∧
    (∀ q ∈ wordList m L, q.2.IsAllowed) ∧
    (∀ q ∈ termList m (toGate L), IsSourceOnly (isoL (gateIso m L).symm ∘L q.2)) ∧
    (wordList m L).length ≤ L.length * m ^ r ∧
    ((wordList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum ∧
    gateOut m L = (L.flatMap fun p => p.2.stackRegs m) ++ ℓY ∧
    ∀ p ∈ L, (p.2.stackRegs m).map Reg.owner =
      p.2.effectParties.flatMap fun e => (List.replicate m [e.1, e.2]).flatten := by
  have hG : ∀ p ∈ toGate L, p.2.IsAllowed ∧ p.2.effectCount ≤ r := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := mem_toGate hp
    exact ⟨p'.2.isAllowed_toEffectChain (hL p' hp').1, (hL p' hp').2⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := pairEffectElimination hm (toGate L) hG
  have hA : ∀ p ∈ L, p.2.IsAllowed := fun p hp => (hL p hp).1
  rw [termList_toGate] at h3 h4 h5
  rw [List.map_map] at h3 h5
  rw [List.length_map, length_toGate] at h4
  rw [map_norm_toGate] at h2 h5
  refine ⟨h1, gateIso_prepGate m L, isAllowed_prepGate m L hA, h2, ?_,
    isAllowed_wordList m L hA, isSourceOnly_termList m L hA, h4, ?_, gateOut_eq m L,
    fun p _ => p.2.owner_stackRegs m⟩
  · rw [h3]
    rfl
  · rw [← h5]
    rfl

end TNLean.PEPS.PairEffect
