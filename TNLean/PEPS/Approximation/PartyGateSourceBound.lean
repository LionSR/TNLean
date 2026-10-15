/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalCircuitSourceBound
import TNLean.PEPS.Approximation.PartyGateOriginalCircuit

/-!
# Pair sources of a sum of monomials read as one gate

A sum `∑_ξ c_ξ M_ξ` of allowed monomials that use only the parties of a finite set `S` is one
gate of these parties (`PartyGate.exists_originalCircuit`). Its gate expansion consists of the
parts of the monomials `M_ξ` on the registers of `S`, relabelled by the parties of `S`. Restricting
to the selected parties keeps every pair source of a monomial using only these parties, and
relabelling owners turns a pair source into a local preparation at most; hence each monomial of
the gate has at most as many pair sources as the corresponding `M_ξ`
(`PartyGate.exists_originalCircuit_isSourceBounded`).

## Main results

* `PairEffect.Word.sourceCount_selectedPart`, `PairEffect.PartyChain.sourceCount_selectedPart`.
* `PairEffect.Word.sourceCount_mapOwner_le`, `PairEffect.PartyChain.sourceCount_mapOwner_le`.
* `PairEffect.isSourceBounded_gateCircuit`.
* `PairEffect.PartyGate.exists_originalCircuit_isSourceBounded`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147; allowed monomials, lines 21–43; the factorization
  `eq:compression-source-gate`, lines 233–251; the gates of Proposition 7.1, `06-geometry.tex`,
  lines 574–583.
-/

noncomputable section

open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-! ### Pair sources under restriction and relabelling -/

namespace Word

/-- The number of pair sources of a word is the length of its source inventory. -/
theorem sourceCount_eq_length_sources {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    w.sourceCount = w.sources.length := by
  induction w with
  | id => rfl
  | comp w w' ih ih' =>
      simp only [sourceCount, sources, List.length_append, ih, ih', Nat.add_comm]
  | localMap => rfl
  | source => rfl
  | swap => rfl
  | frame r w ih => exact ih

@[simp] theorem sourceCount_castLayouts {ℓ ℓ' a b : Layout P} (w : Word ℓ ℓ')
    (h : ℓ = a) (h' : ℓ' = b) : (w.castLayouts h h').sourceCount = w.sourceCount := by
  cases h
  cases h'
  rfl

/-- The selected part of a word keeps all of its pair sources. -/
@[simp] theorem sourceCount_selectedPart (f : P → Bool) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hS : ∀ s ∈ w.sources, f s.left = true ∧ f s.right = true) :
    (w.selectedPart f hS).sourceCount = w.sourceCount := by
  simp only [sourceCount_eq_length_sources, selectedPart, sources, sources_castInput,
    sources_restrict, sources_prepare, List.nil_append]

/-- Relabelling owners does not create pair sources. -/
theorem sourceCount_mapOwner_le {Q : Type} (g : P → Q) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (w.mapOwner g).sourceCount ≤ w.sourceCount := by
  rw [sourceCount_eq_length_sources, sourceCount_eq_length_sources, sources_mapOwner]
  exact List.length_filterMap_le _ _

end Word

namespace PartyChain

/-- The selected part of a monomial using only selected parties keeps all of its pair
sources. -/
@[simp] theorem sourceCount_selectedPart (f : P → Bool) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : M.UsesOnly {p | f p = true}) :
    (M.selectedPart f h).sourceCount = M.sourceCount := by
  induction M with
  | final w => exact w.sourceCount_selectedPart f _
  | effect hpq α β ℓS w η rest ih =>
      simp only [selectedPart, sourceCount, Word.sourceCount_castLayouts,
        Word.sourceCount_selectedPart, ih]

/-- Relabelling owners does not create pair sources. -/
theorem sourceCount_mapOwner_le {Q : Type} (g : P → Q) {ℓX ℓY : Layout P}
    (M : PartyChain ℓX ℓY) (h : ∀ e ∈ M.effectParties, g e.1 ≠ g e.2) :
    (M.mapOwner g h).sourceCount ≤ M.sourceCount := by
  induction M with
  | final w => exact w.sourceCount_mapOwner_le g
  | effect hpq α β ℓS w η rest ih =>
      exact Nat.add_le_add (w.sourceCount_mapOwner_le g) (ih _)

end PartyChain

/-! ### The gate of a sum of monomials -/

variable [DecidableEq P]

theorem sourceCount_retractedGate_le (S : Finset P) (d : S) {ℓ ℓ' : Layout P}
    (G : PartyGate ℓ ℓ') (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true}) {r : ℕ}
    (hr : ∀ m ∈ G, m.2.sourceCount ≤ r) :
    ∀ m ∈ retractedGate S d G hU, m.2.sourceCount ≤ r := by
  intro m hm
  obtain ⟨m₁, hm₁, rfl⟩ := mem_mapOwnerGate hm
  obtain ⟨m₀, hm₀, rfl⟩ := mem_selectedGate hm₁
  exact (PartyChain.sourceCount_mapOwner_le _ _ _).trans
    ((PartyChain.sourceCount_selectedPart _ _ _).trans_le (hr m₀ hm₀))

theorem isSourceBounded_coreGateCircuit (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P} (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) (T : Layout P) {r : ℕ}
    (hr : ∀ m ∈ G, m.2.sourceCount ≤ r) :
    (coreGateCircuit S hS₀ G hA hU hN T).IsSourceBounded r := by
  unfold coreGateCircuit
  split
  · trivial
  · exact OriginalCircuit.isSourceBounded_castLayouts _ _ _
      (sourceCount_retractedGate_le S _ G hU hr)

/-- The gate of a sum of monomials using only the parties of `S` has at most as many pair
sources in each monomial as the monomials of the sum.
Polynomial-PEPS manuscript, `04-compression.tex`, lines 143–147 and 233–251. -/
theorem isSourceBounded_gateCircuit (S : Finset P) (hS₀ : S.Nonempty) {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed)
    (hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true})
    (hN : ‖gate (toGate (selectedGate _ G hU))‖ ≤ 1) {r : ℕ}
    (hr : ∀ m ∈ G, m.2.sourceCount ≤ r) : (gateCircuit S hS₀ h G hA hU hN).IsSourceBounded r :=
  ⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero
      (Word.nonprivateCount_toOriginalCircuit_of_isReordering
        (Layout.isReordering_partitionWord _ ℓ)) r,
    OriginalCircuit.isSourceBounded_castLayouts _ _ _
      (isSourceBounded_coreGateCircuit S hS₀ G hA hU hN _ hr),
    OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero
      (Word.nonprivateCount_toOriginalCircuit_of_isReordering
        (Layout.isReordering_unpartitionWord _ ℓ')) r⟩

/-- **A sum of monomials on a list of parties as one gate, with its pair sources.** The
conclusion of `PartyGate.exists_originalCircuit`, together with the pair-source bound: every
monomial of the gate has at most `r` pair sources when every monomial of the sum does.

Polynomial-PEPS manuscript, `04-compression.tex`, lines 21–43 and 143–147, and
`06-geometry.tex`, lines 574–583. -/
theorem PartyGate.exists_originalCircuit_isSourceBounded (S : Finset P) (hS₀ : S.Nonempty)
    {ℓ ℓ' : Layout P}
    (h : Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ = Layout.restrict (fun p ↦ !decide (p ∈ S)) ℓ')
    (G : PartyGate ℓ ℓ') (hA : ∀ m ∈ G, m.2.IsAllowed) (hF : ∀ m ∈ G, m.2.FixesOutside S h)
    (hN : ‖gate (toGate G)‖ ≤ 1) (hne : Nontrivial (Mem ℓ)) :
    ∃ c : OriginalCircuit ℓ ℓ', c.eval = gate (toGate G) ∧ c.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(c.participants g) : Set P) ⊆ ↑S) ∧
      (∀ (r : ℕ) (s : ℝ), (∀ m ∈ G, m.2.toEffectChain.effectCount ≤ r) →
        (G.map fun m => ‖m.1‖).sum ≤ s → c.IsExpansionBounded r s) ∧
      c.IsMonomialBounded G.length ∧
      ∀ r : ℕ, (∀ m ∈ G, m.2.sourceCount ≤ r) → c.IsSourceBounded r := by
  have hU : ∀ m ∈ G, m.2.UsesOnly {p | decide (p ∈ S) = true} := fun m hm => (hF m hm).1
  have hFx : ∀ m (hm : m ∈ G),
      (m.2.complementPart (fun p ↦ decide (p ∈ S)) (hU m hm)).eval =
        isoL (Layout.memCongr h) := fun m hm => (hF m hm).2
  have hN' := norm_gate_selectedGate_le S h G hU hFx hN hne
  have hP := Layout.isReordering_partitionWord (fun p ↦ decide (p ∈ S)) ℓ
  have hQ := Layout.isReordering_unpartitionWord (fun p ↦ decide (p ∈ S)) ℓ'
  refine ⟨gateCircuit S hS₀ h G hA hU hN', eval_gateCircuit S hS₀ h G hA hU hFx hN', ?_, ?_,
    ?_, ?_, fun r hr => isSourceBounded_gateCircuit S hS₀ h G hA hU hN' hr⟩
  · simp only [gateCircuit, OriginalCircuit.nonprivateCount,
      Word.nonprivateCount_toOriginalCircuit_of_isReordering hP,
      Word.nonprivateCount_toOriginalCircuit_of_isReordering hQ,
      OriginalCircuit.nonprivateCount_castLayouts, zero_add, add_zero]
    exact nonprivateCount_coreGateCircuit_le S hS₀ G hA hU hN' _
  · intro g
    rcases g with g | g | g
    · exact Word.participants_toOriginalCircuit_subset _ _ (hP.usesOnly _) g
    · exact OriginalCircuit.participants_castLayouts_subset _ _ _
        (participants_coreGateCircuit_subset S hS₀ G hA hU hN' _) g
    · exact Word.participants_toOriginalCircuit_subset _ _ (hQ.usesOnly _) g
  · intro r s hr hs
    exact ⟨Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
        hP.sourceCount_eq r s,
      OriginalCircuit.isExpansionBounded_castLayouts _ _ _
        (isExpansionBounded_coreGateCircuit S hS₀ G hA hU hN' _ hr hs),
      Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
        hQ.sourceCount_eq r s⟩
  · exact ⟨Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
        hP.sourceCount_eq _,
      OriginalCircuit.isMonomialBounded_castLayouts _ _ _
        (isMonomialBounded_coreGateCircuit S hS₀ G hA hU hN' _),
      Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
        hQ.sourceCount_eq _⟩

end TNLean.PEPS.PairEffect
