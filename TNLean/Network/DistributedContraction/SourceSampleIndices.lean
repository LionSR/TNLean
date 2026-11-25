/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Choices
import QICLean.Circuit.Party.Source.PairIndex
import TNLean.Network.DistributedContraction.DistributedOperatorContraction

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

namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network

variable {P : Type} [DecidableEq P]

/-- The unordered pairs of distinct parties of a cell are the sample pairs of that cell. -/
private def cellPairEquiv (D : Finset P) :
    {z : Sym2 ↥D // ¬z.IsDiag} ≃ {z : Sym2 P // z ∈ pairSampleLabels D} := by
  let f : {z : Sym2 ↥D // ¬z.IsDiag} → {z : Sym2 P // z ∈ pairSampleLabels D} :=
    fun z ↦ ⟨Sym2.map Subtype.val z.1, by
      apply (mem_pairSampleLabels _ _).mpr
      refine ⟨?_, fun h ↦ z.2 ((Sym2.isDiag_map Subtype.val_injective).mp h)⟩
      intro p hp
      obtain ⟨c, _, rfl⟩ := Sym2.mem_map.mp hp
      exact c.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
  · intro z
    rcases z with ⟨z, hz⟩
    obtain ⟨p, q⟩ := z
    obtain ⟨hp, hq, hpq⟩ := (mk_mem_pairSampleLabels _ _ _).mp hz
    refine ⟨⟨Sym2.mk ⟨p, hp⟩ ⟨q, hq⟩, ?_⟩, rfl⟩
    rw [Sym2.mk_isDiag_iff]
    exact fun h ↦ hpq (congrArg Subtype.val h)

private theorem cellPairEquiv_apply (D : Finset P) (z : {z : Sym2 ↥D // ¬z.IsDiag}) :
    (cellPairEquiv D z).1 = Sym2.map Subtype.val z.1 := rfl

/-- Each original gate slot is exactly one sample pair of its actual
participants. No monomial labels or source vectors are chosen.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245,
342–364 and 568–571. -/
def sourcePairEquiv : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (g : w.gateLocations) → Fin (w.slotCount g) ≃
      {z : Sym2 P // z ∈ pairSampleLabels (w.participants g)}
  | _, _, PartyCircuit.done _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.gate D _ g => fun _ ↦
    (SourceInventory.pairIndexEquiv g.gate.slots g.gate.pair_nodup g.gate.pair_complete).trans
      (cellPairEquiv D)
  | _, _, PartyCircuit.localOp _ _ _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.localOps _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.comp c c' => fun
    | Sum.inl g => sourcePairEquiv c g
    | Sum.inr g => sourcePairEquiv c' g

/-- The pair index has the original two endpoint owners, independently of
any choice of orientation for an unordered pair.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–364
and 568–571. -/
theorem sourcePairEquiv_apply : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) →
      (sourcePairEquiv w e.1 e.2).1 = Sym2.mk (w.endpoints e).1 (w.endpoints e).2
  | _, _, PartyCircuit.done _, e => Empty.elim e.1
  | _, _, PartyCircuit.gate D _ g, e => by
    obtain ⟨o, i⟩ := e
    change (cellPairEquiv D (SourceInventory.pairIndexEquiv g.gate.slots g.gate.pair_nodup
      g.gate.pair_complete i)).1 =
        Sym2.mk (g.gate.slots.get i).left.1 (g.gate.slots.get i).right.1
    rw [cellPairEquiv_apply]
    erw [SourceInventory.pairIndexEquiv_apply]
    simp only [PairSource.partyPair, Sym2.map_mk]
  | _, _, PartyCircuit.localOp _ _ _, e => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, e => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', e => match e with
    | ⟨Sum.inl g, i⟩ => sourcePairEquiv_apply c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => sourcePairEquiv_apply c' ⟨g, i⟩

open Classical in
/-- Original source occurrences and the distributed sample positions agree.
An empty or singleton-participant gate contributes no pair position.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–571
and 581–588. -/
def sourceSampleEquiv {X Y : P → Type} (w : SourceCircuit X Y) :
    w.sourceLocations ≃ DistributedOperatorContraction.Sample
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

end QuantumCircuit.Party.SourceCircuit
