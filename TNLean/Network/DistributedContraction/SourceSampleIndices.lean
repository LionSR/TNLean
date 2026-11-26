/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Choices
import QICLean.Circuit.Party.Source.PairIndex
import TNLean.Network.DistributedContraction.DistributedOperatorContraction
import QICLean.Circuit.Party.Compression.PartialExpansion.Sources
import TNLean.Network.DistributedContraction.IncidentGateLabels
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Original source positions and distributed sample links

A source position is a gate occurrence together with one recorded pair slot.
The slots enumerate the unordered pairs of distinct participants exactly once.
Thus the original positions are precisely the sample positions of the
nonempty-participant gate occurrences. This identification concerns only the
indices; the original left and right endpoint spaces remain unchanged.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245,
342–364 and 565–588.

It also contains the following results.

* `QuantumCircuit.Party.SourceCircuit.mem_sourceSampleEquiv_iff`,
  `QuantumCircuit.Party.SourceCircuit.partialSlotSampleEquiv`: local sample indices in the original
  source order.
* `QuantumCircuit.Party.SourceCircuit.length_allSourceSlots_eq_sum_pairSampleLabels`,
  `QuantumCircuit.Party.SourceCircuit.inv_sampleSize_pow_allSourceSlots_eq_prod`: the number of
  original pair samples and their averaging factor.
-/

section SourceSampleIndices

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

end

end SourceSampleIndices

section LocalSourceSampleIndices

/-!
## Local sample indices in the original source order

The selected source-slot indices at one party are exactly the sample positions
incident to that party. This correspondence retains the original occurrence
and the original ordering of selected source slots. Consequently, a local
sample assignment requires values only at these positions, including when
an unrelated source has an empty sample alphabet.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
342–417 and 568–579.
-/

noncomputable section
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P]

open Classical in
/-- Incidence of a sample pair is exactly incidence of its original two
source endpoints. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 342–364 and 568–579. -/
theorem mem_sourceSampleEquiv_iff {X Y : P → Type} (w : SourceCircuit X Y)
    (p : P) (e : w.sourceLocations) :
    p ∈ (sourceSampleEquiv w e).2.1.toFinset ↔
      (w.endpoints e).1 = p ∨ (w.endpoints e).2 = p := by
  change p ∈ (sourcePairEquiv w e.1 e.2).1.toFinset ↔
    (w.endpoints e).1 = p ∨ (w.endpoints e).2 = p
  rw [sourcePairEquiv_apply]
  simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton, eq_comm]

open Classical in
/-- The ordered singleton source slots are precisely the local sample indices
of the distributed contraction. No sample value at another source position
is chosen. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 383–417 and 568–579. -/
def partialSlotSampleEquiv {X Y : P → Type} (w : SourceCircuit X Y) (p : P) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    Fin (partialSlots A w).length ≃ DistributedOperatorContraction.SampleAt
      (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p := by
  intro A
  refine (partialSlotEquiv A w).trans ((sourceSampleEquiv w).subtypeEquiv ?_)
  intro e
  rw [mem_sourceSampleEquiv_iff]
  dsimp only [A]
  simp_rw [partySelector_affectedOwner_all_apply]
  simp only [partySelector_eq_true_iff]

end QuantumCircuit.Party.SourceCircuit

end

end LocalSourceSampleIndices

section SourceSampleCount

/-! # The number of original pair samples and their averaging factor

Each original source occurrence contributes one shared sample index. These
indices are counted by summing the numbers of unordered participant pairs
at the original nonempty gate occurrences. Repeated uses of a gate remain
distinct occurrences. The operations with empty participant sets contribute
only to the separate exterior scalar.

The reciprocal sample power is consequently the product of the reciprocal
powers for these occurrences. No cancellation is used, and both zero sample
size and an empty family of gates are permitted.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–417
and 568–588.
-/

noncomputable section
namespace QuantumCircuit.Party.SourceCircuit
open TNLean.Network
variable {P : Type} [DecidableEq P]

open Classical in
/-- Count sample positions on an abstract finite gate family before inserting
its original circuit occurrences. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 568–588. -/
private theorem card_sample_univ_eq_sum_pairSampleLabels {G : Type} [Fintype G]
    (participants : G → Finset P) :
    Fintype.card (DistributedOperatorContraction.Sample
      (Finset.univ : Finset G) participants) =
      ∑ g : G, (pairSampleLabels (participants g)).card := by
  unfold DistributedOperatorContraction.Sample
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach Finset.univ (fun g : G ↦ (pairSampleLabels (participants g)).card)

open Classical in
/-- The original ordered source slots are counted by the pair samples at each
original nonempty gate occurrence. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–417 and 568–588. -/
theorem length_allSourceSlots_eq_sum_pairSampleLabels {X Y : P → Type}
    (w : SourceCircuit X Y) :
    (partialSlots (fun _ : P ↦ true) w).length =
      ∑ g : w.nonemptyGateLocations, (pairSampleLabels (w.participants g.1)).card := by
  have hCard := Fintype.card_congr ((allSourceSlotEquiv w).trans (sourceSampleEquiv w))
  rw [Fintype.card_fin] at hCard
  exact hCard.trans (card_sample_univ_eq_sum_pairSampleLabels
    (G := w.nonemptyGateLocations) (fun g ↦ w.participants g.1))

open Classical in
/-- The common sample averaging factor is the product of the averaging factors
at the original nonempty gate occurrences. This includes zero sample size.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 568–588. -/
theorem inv_sampleSize_pow_allSourceSlots_eq_prod {X Y : P → Type}
    (w : SourceCircuit X Y) (k : ℕ) :
    (k : ℂ)⁻¹ ^ (partialSlots (fun _ : P ↦ true) w).length =
      ∏ g : w.nonemptyGateLocations,
        (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card := by
  rw [length_allSourceSlots_eq_sum_pairSampleLabels]
  exact (Finset.prod_pow_eq_pow_sum Finset.univ
    (fun g : w.nonemptyGateLocations ↦ (pairSampleLabels (w.participants g.1)).card)
    (k : ℂ)⁻¹).symm

end QuantumCircuit.Party.SourceCircuit

end

end SourceSampleCount
