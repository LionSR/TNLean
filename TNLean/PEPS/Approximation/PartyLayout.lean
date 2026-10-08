/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceCombination
import TNLean.PEPS.Approximation.PartyChain

/-!
# Pair-effect elimination on a party layout

This file proves the statements of Lemma 5.1 `lem:effects` about parties for gate
expansions into monomials placed on parties: the replaced gate has an expansion using only
local contractions and normalized pair sources, and its additional registers are owned by the
endpoint parties of the eliminated effects.  Registers, source-only words and stacks of pair
registers are defined in `TNLean.PEPS.Approximation.PartyWord`; allowed monomials on parties
(`PartyChain`), their replaced terms and their stacks in
`TNLean.PEPS.Approximation.PartyChain`; the combination of two adjacent pair sources in
`TNLean.PEPS.Approximation.PairSourceCombination`.

In the replacement, the stack of an effect occurrence on `(p, q)` consists of `m` pair
registers `ℂ^α ⊗ ℂ^β`, the `ℂ^α` half owned by `p` and the `ℂ^β` half owned by `q`.  The
insertions are source-only words (`stackIso_insWord`).  This identifies the terms of the
expansion of the replaced gate with source-only words (`termList_toGate`), the common garbage
vector with a product of pair sources (`gateIso_prepGate`), and the additional registers with
the stacks (`gateOut_eq`).

The combination of arbitrary sources on one unordered pair, including sources separated
by local operations, is proved in `TNLean.PEPS.Approximation.PairEffectSourcePreparation`.
That module proves `partyPairEffectElimination_with_grouped_sources`, which retains all
conclusions here and includes the last clause of Lemma 5.1. The earlier restriction and
its resolution are recorded in `docs/paper-gaps/polypeps_pair_effects_party_layout.tex`.

## Main definitions

* `PairEffect.wordList` : the expansion of the replaced gate into source-only words.
* `PairEffect.gateOut`, `PairEffect.gateIso` : the output layout of the replaced gate and its
  identification with the output space of `PairEffect.replaceGate`.

## Main results

* `PairEffect.termList_toGate` : the expansion of the replaced gate, term by term.
* `PairEffect.gateIso_prepGate` : the common garbage vector `Γ_m` is prepared by pair
  sources.
* `PairEffect.gateOut_eq` : the additional registers are the stacks of all effect
  occurrences.
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

/-- Appending a vector on the right of the first factor, read through the regrouping of
`gateIso_cons`. -/
private theorem assocL_tmul_eq_regroup {E S G : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (z : E ⊗[ℂ] S) (g : G) :
    assocL E S G (z ⊗ₜ g) = (TensorProduct.commIsometry ℂ G S).lTensor E
      (TensorProduct.assocIsometry ℂ E G S ((appendRight g).rTensor S z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul y s =>
      simp only [rTensor_tmul, appendRight_apply, assocL_tmul,
        TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, iso_lTensor_apply,
        lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply, TensorProduct.comm_tmul]
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]

/-- Prepending a vector in front of the pair, read through the regrouping of `gateIso_cons`. -/
private theorem leftCommL_tmul_eq_regroup {E S G : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (y : E ⊗[ℂ] G) (s : S) :
    leftCommL S E G (s ⊗ₜ y) = (TensorProduct.commIsometry ℂ G S).lTensor E
      (TensorProduct.assocIsometry ℂ E G S (y ⊗ₜ s)) := by
  induction y using TensorProduct.inductionOn with
  | tmul e g =>
      simp only [leftCommL_tmul, TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul,
        iso_lTensor_apply, lTensor_tmul, isoL_apply, TensorProduct.commIsometry_apply,
        TensorProduct.comm_tmul]
  | add a b ha hb => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ha, hb]

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
        refine ContinuousLinearMap.ext fun x => ?_
        have hprep : isoL (gateIso m L) ∘L (prepGate m L).eval =
            appendRight (inventoryVector m (toGate L)) :=
          ContinuousLinearMap.ext fun y => gateIso_prepGate m L y
        have key : (gateIso m L).rTensor _ (p.2.stackAppIso m (gateOut m L)
              ((p.2.frameStack m (prepGate m L)).eval ((p.2.replaceWord m κ).eval x))) =
            (appendRight (inventoryVector m (toGate L))).rTensor _
              ((isoL (p.2.stackAppIso m ℓY) ∘L (p.2.replaceWord m κ).eval) x) := by
          rw [PartyChain.stackAppIso_frameStack, iso_rTensor_apply, rTensor_comp_apply, hprep]
          rfl
        refine (congrArg (fun v => assocL _ _ _ (v ⊗ₜ inventoryVector m (toGate L)))
          (DFunLike.congr_fun (p.2.replaceTerm_toEffectChain m κ) x)).trans ?_
        refine (assocL_tmul_eq_regroup _ _).trans ?_
        exact congrArg (fun v => (TensorProduct.commIsometry ℂ _ _).lTensor _
          (TensorProduct.assocIsometry ℂ _ _ _ v)) key.symm
      · rw [termList_toGate L, List.map_map]
        refine List.map_congr_left fun q _ => Prod.ext rfl ?_
        refine ContinuousLinearMap.ext fun x => ?_
        have key : (gateIso m L).rTensor _ (p.2.stackAppIso m (gateOut m L)
              ((p.2.prepStack m (gateOut m L)).eval (q.2.eval x))) =
            gateIso m L (q.2.eval x) ⊗ₜ p.2.toEffectChain.stackVector m := by
          rw [PartyChain.stackAppIso_prepStack, iso_rTensor_apply, rTensor_tmul, isoL_apply]
        refine (leftCommL_tmul_eq_regroup _ _).trans ?_
        exact congrArg (fun v => (TensorProduct.commIsometry ℂ _ _).lTensor _
          (TensorProduct.assocIsometry ℂ _ _ _ v)) key.symm

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
