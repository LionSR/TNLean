/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePairIndex
import TNLean.Lattice.PartyCircuit.SourceCircuitLocations
import TNLean.PEPS.Approximation.NonemptyGateLabels
import TNLean.PEPS.Approximation.DistributedOperatorContraction

/-!
# Original source positions and distributed sample links

A source position is a gate occurrence together with one recorded pair slot.
The slots enumerate the unordered pairs of distinct participants exactly once.
Thus the original positions are precisely the sample positions of the
nonempty-participant gate occurrences. This identification concerns only the
indices; the original left and right endpoint spaces remain unchanged.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245,
342–364 and 565–588.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceCircuit

open Classical in
private def participantPairEquiv {C P : Type} [Fintype C] (owner : C ↪ P) :
    {z : Sym2 C // ¬z.IsDiag} ≃
      {z : Sym2 P // z ∈ Approximation.pairSampleLabels
        (Finset.univ.map owner)} := by
  let f : {z : Sym2 C // ¬z.IsDiag} →
      {z : Sym2 P // z ∈ Approximation.pairSampleLabels
        (Finset.univ.map owner)} := fun z ↦ ⟨Sym2.map owner z.1, by
    apply (Approximation.mem_pairSampleLabels _ _).mpr
    refine ⟨?_, fun h ↦ z.2 ((Sym2.isDiag_map owner.injective).mp h)⟩
    intro p hp
    obtain ⟨c, _, rfl⟩ := Sym2.mem_map.mp hp
    exact Finset.mem_map_of_mem owner (Finset.mem_univ c)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (Sym2.map.injective owner.injective (congrArg Subtype.val h))
  · intro z
    rcases z with ⟨z, hz⟩
    obtain ⟨p, q⟩ := z
    obtain ⟨hp, hq, hpq⟩ :=
      (Approximation.mk_mem_pairSampleLabels _ _ _).mp hz
    obtain ⟨c, _, hc⟩ := Finset.mem_map.mp hp
    obtain ⟨d, _, hd⟩ := Finset.mem_map.mp hq
    refine ⟨⟨Sym2.mk c d, ?_⟩, ?_⟩
    · rw [Sym2.mk_isDiag_iff]
      intro h
      apply hpq
      rw [← hc, ← hd, h]
    · apply Subtype.ext
      change Sym2.mk (owner c) (owner d) = Sym2.mk p q
      rw [hc, hd]

private theorem participantPairEquiv_apply {C P : Type} [Fintype C]
    (owner : C ↪ P) (z : {z : Sym2 C // ¬z.IsDiag}) :
    (participantPairEquiv owner z).1 = Sym2.map owner z.1 := rfl

variable {P : Type}

open Classical in
/-- Each original gate slot is exactly one sample pair of its actual
participants. No monomial labels or source vectors are chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245,
342–364 and 568–571. -/
def sourcePairEquiv : {a b : Layout P} → (w : SourceCircuit a b) →
    (g : w.gateLocations) → Fin (w.slotCount g) ≃
      {z : Sym2 P // z ∈ Approximation.pairSampleLabels (w.participants g)}
  | _, _, .id _, g => nomatch g
  | _, _, .comp w v, g => by
      change gateLocations w ⊕ gateLocations v at g
      cases g with
      | inl g => exact sourcePairEquiv w g
      | inr g => exact sourcePairEquiv v g
  | _, _, .localMap .., g => nomatch g
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G _, _ =>
      (SourceInventory.pairIndexEquiv G.slots G.pair_nodup G.pair_complete).trans
        (participantPairEquiv owner)
  | _, _, .swap .., g => nomatch g
  | _, _, .frame _ w, g => sourcePairEquiv w g

/-- The pair index has the original two endpoint owners, independently of
any choice of orientation for an unordered pair.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–364
and 568–571. -/
theorem sourcePairEquiv_apply {a b : Layout P} (w : SourceCircuit a b)
    (e : w.sourceLocations) :
    (sourcePairEquiv w e.1 e.2).1 = Sym2.mk (w.endpoints e).1 (w.endpoints e).2 := by
  classical
  induction w with
  | id => exact False.elim (Empty.elim e.1 : False)
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ⟨g, i⟩
      | inr g => exact ihv ⟨g, i⟩
  | localMap => exact False.elim (Empty.elim e.1 : False)
  | @gate C ι _ _ owner a b c G tail =>
      rcases e with ⟨g, i⟩
      cases g
      change Fin G.slots.length at i
      change ((participantPairEquiv owner)
        (SourceInventory.pairIndexEquiv G.slots G.pair_nodup G.pair_complete i)).val =
          Sym2.mk (owner (G.slots.get i).left) (owner (G.slots.get i).right)
      rw [participantPairEquiv_apply, SourceInventory.pairIndexEquiv_apply]
      simp only [PairSource.partyPair, Sym2.map_mk]
  | swap => exact False.elim (Empty.elim e.1 : False)
  | frame r w ih => exact ih e

open Classical in
/-- Original source occurrences and the distributed sample positions agree.
An empty or singleton-participant gate contributes no pair position.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–571
and 581–588. -/
def sourceSampleEquiv {a b : Layout P} (w : SourceCircuit a b) :
    w.sourceLocations ≃ Approximation.DistributedOperatorContraction.Sample
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) where
  toFun e :=
    ⟨⟨⟨e.1, ⟨(w.endpoints e).1, (w.endpoints_mem_participants e).1⟩⟩,
        Finset.mem_univ _⟩, sourcePairEquiv w e.1 e.2⟩
  invFun s := ⟨s.1.1.1, (sourcePairEquiv w s.1.1.1).symm s.2⟩
  left_inv e := by
    rcases e with ⟨g, i⟩
    exact Sigma.ext rfl (heq_of_eq (Equiv.symm_apply_apply (sourcePairEquiv w g) i))
  right_inv s := by
    rcases s with ⟨⟨⟨g, hg⟩, hactive⟩, z⟩
    exact Sigma.ext rfl (heq_of_eq (Equiv.apply_symm_apply (sourcePairEquiv w g) z))

end TNLean.PEPS.PairEffect.SourceCircuit
