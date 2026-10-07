/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedLifetime
import Mathlib.Data.Sym.Card

/-!
# Links for distributed density compression

Each nonprivate gate shares its common ket/bra label on a star and shares a
sample index along each unordered pair of distinct participants. The link
identifiers retain both their gate occurrence and their kind, so parallel links
from different gates or of different kinds remain distinct.

The construction proves original-gate co-participation of both endpoints and a
uniform incidence bound from gate arity and whole-lifetime participation.
It does not contract the local tensors or bound virtual dimensions; these are
separate parts of the density-compression theorem. Private memory dimensions
and source Schmidt ranks do not enter these finite incidence results.

## Main definitions and statements

- `pairSampleLabels`: unordered pairs of distinct gate participants.
- `gateLinkLabels`: star-link and sample-link labels at one gate.
- `distributedLinks`: the actual finite gate-tagged link family.
- `distributedLinkParties_subset`: both ends belong to the original owner gate.
- `card_incidentDistributedLinks_le`: bounded link incidence from lifetime participation.

## References

- OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2 (`thm:compression`), proof's network
  construction, `04-compression.tex:565–588`.
  [Pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L565).

These proofs are newly written from the paper's mathematical argument. No OpenAI
Lean code is copied or adapted.
-/

/-!
Original proof provenance.
Source: September 24, 2026.
Paper file: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex
Labels: thm:compression;
independently formalized; no upstream Lean proof text reused.
Mathematical source commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a.

Provenance-ID: 8769-lifetime-pair-sample-labels
Downstream declaration: TNLean.PEPS.Approximation.pairSampleLabels
Provenance-ID: 8769-lifetime-gate-link-labels
Downstream declaration: TNLean.PEPS.Approximation.gateLinkLabels
Provenance-ID: 8769-lifetime-gate-link-parties
Downstream declaration: TNLean.PEPS.Approximation.gateLinkParties
Provenance-ID: 8769-lifetime-links-at-gate
Downstream declaration: TNLean.PEPS.Approximation.linksAtGate
Provenance-ID: 8769-lifetime-distributed-links
Downstream declaration: TNLean.PEPS.Approximation.distributedLinks
Provenance-ID: 8769-lifetime-distributed-link-parties
Downstream declaration: TNLean.PEPS.Approximation.distributedLinkParties
Provenance-ID: 8769-lifetime-incident-distributed-links
Downstream declaration: TNLean.PEPS.Approximation.incidentDistributedLinks
Provenance-ID: 8769-lifetime-incident-gate-link-labels
Downstream declaration: TNLean.PEPS.Approximation.incidentGateLinkLabels
Provenance-ID: 8769-lifetime-incident-links-at-gate
Downstream declaration: TNLean.PEPS.Approximation.incidentLinksAtGate
Provenance-ID: 8769-lifetime-mem-pair-sample-labels
Downstream declaration: TNLean.PEPS.Approximation.mem_pairSampleLabels
Provenance-ID: 8769-lifetime-mk-mem-pair-sample-labels
Downstream declaration: TNLean.PEPS.Approximation.mk_mem_pairSampleLabels
Provenance-ID: 8769-lifetime-card-pair-sample-labels
Downstream declaration: TNLean.PEPS.Approximation.card_pairSampleLabels
Provenance-ID: 8769-lifetime-filter-pair-sample-labels-eq-map
Downstream declaration: TNLean.PEPS.Approximation.filter_pairSampleLabels_eq_map
Provenance-ID: 8769-lifetime-card-filter-pair-sample-labels
Downstream declaration: TNLean.PEPS.Approximation.card_filter_pairSampleLabels
Provenance-ID: 8769-lifetime-card-gate-link-labels
Downstream declaration: TNLean.PEPS.Approximation.card_gateLinkLabels
Provenance-ID: 8769-lifetime-card-gate-link-labels-le
Downstream declaration: TNLean.PEPS.Approximation.card_gateLinkLabels_le
Provenance-ID: 8769-lifetime-card-incident-gate-link-labels-le
Downstream declaration: TNLean.PEPS.Approximation.card_incidentGateLinkLabels_le
Provenance-ID: 8769-lifetime-gate-link-parties-subset
Downstream declaration: TNLean.PEPS.Approximation.gateLinkParties_subset
Provenance-ID: 8769-lifetime-card-gate-link-parties
Downstream declaration: TNLean.PEPS.Approximation.card_gateLinkParties
Provenance-ID: 8769-lifetime-card-links-at-gate
Downstream declaration: TNLean.PEPS.Approximation.card_linksAtGate
Provenance-ID: 8769-lifetime-mem-links-at-gate
Downstream declaration: TNLean.PEPS.Approximation.mem_linksAtGate
Provenance-ID: 8769-lifetime-card-incident-links-at-gate
Downstream declaration: TNLean.PEPS.Approximation.card_incidentLinksAtGate
Provenance-ID: 8769-lifetime-mem-distributed-links
Downstream declaration: TNLean.PEPS.Approximation.mem_distributedLinks
Provenance-ID: 8769-lifetime-distributed-link-parties-subset
Downstream declaration: TNLean.PEPS.Approximation.distributedLinkParties_subset
Provenance-ID: 8769-lifetime-card-distributed-link-parties
Downstream declaration: TNLean.PEPS.Approximation.card_distributedLinkParties
Provenance-ID: 8769-lifetime-exists-common-gate-of-mem-distributed-link-parties
Downstream declaration: TNLean.PEPS.Approximation.exists_common_gate_of_mem_distributedLinkParties
Provenance-ID: 8769-lifetime-incident-distributed-links-subset
Downstream declaration: TNLean.PEPS.Approximation.incidentDistributedLinks_subset
Provenance-ID: 8769-lifetime-card-incident-distributed-links-le
Downstream declaration: TNLean.PEPS.Approximation.card_incidentDistributedLinks_le
-/

namespace TNLean.PEPS.Approximation

variable {Party Gate : Type*} [DecidableEq Party] [DecidableEq Gate]

/-- One shared sample label for each unordered pair of distinct gate participants.
Theorem 5.2, `04-compression.tex:568–585`. The label represents the sample position,
rather than a choice of monomial branch. -/
def pairSampleLabels (parties : Finset Party) : Finset (Sym2 Party) :=
  parties.sym2.filter (fun pair ↦ ¬pair.IsDiag)

/-- The labels for a star rooted at `root` and for pair samples, kept disjoint by
their summand. Theorem 5.2, `04-compression.tex:565–585`. -/
def gateLinkLabels (parties : Finset Party) (root : Party) : Finset (Party ⊕ Sym2 Party) :=
  (parties.erase root).disjSum (pairSampleLabels parties)

/-- The party endpoints of a gate-local star or sample link.
Theorem 5.2, `04-compression.tex:565–588`. -/
def gateLinkParties (root : Party) : Party ⊕ Sym2 Party → Finset Party
  | Sum.inl p => { root, p }
  | Sum.inr pair => pair.toFinset

/-- Gate-occurrence-tagged links at one gate. Tags retain parallel links belonging
to different gate occurrences. Theorem 5.2, `04-compression.tex:565–588`. -/
def linksAtGate (participants : Gate → Finset Party) (root : Gate → Party)
    (g : Gate) : Finset (Gate × (Party ⊕ Sym2 Party)) :=
  (gateLinkLabels (participants g) (root g)).map (Function.Embedding.sectR g _)

/-- All star and pair-sample links in the complete nonprivate gate list.
Theorem 5.2, `04-compression.tex:565–588`. -/
def distributedLinks (gates : Finset Gate) (participants : Gate → Finset Party)
    (root : Gate → Party) : Finset (Gate × (Party ⊕ Sym2 Party)) :=
  gates.biUnion (linksAtGate participants root)

/-- Endpoints of a gate-tagged link. Its first component identifies the original
gate occurrence. Theorem 5.2, `04-compression.tex:565–588`. -/
def distributedLinkParties (root : Gate → Party)
    (link : Gate × (Party ⊕ Sym2 Party)) : Finset Party :=
  gateLinkParties (root link.1) link.2

/-- All virtual links meeting a party, counting parallel links separately.
Theorem 5.2, `04-compression.tex:581–588`. -/
def incidentDistributedLinks (gates : Finset Gate) (participants : Gate → Finset Party)
    (root : Gate → Party) (p : Party) : Finset (Gate × (Party ⊕ Sym2 Party)) :=
  (distributedLinks gates participants root).filter (fun link ↦
    p ∈ distributedLinkParties root link)

/-- Gate-local link labels incident to `p`. Theorem 5.2, `04-compression.tex:581–588`. -/
def incidentGateLinkLabels (parties : Finset Party) (root p : Party) :
    Finset (Party ⊕ Sym2 Party) :=
  (gateLinkLabels parties root).filter (fun label ↦ p ∈ gateLinkParties root label)

/-- Gate-tagged links incident to `p` at one gate occurrence.
Theorem 5.2, `04-compression.tex:581–588`. -/
def incidentLinksAtGate (participants : Gate → Finset Party) (root : Gate → Party)
    (p : Party) (g : Gate) : Finset (Gate × (Party ⊕ Sym2 Party)) :=
  (linksAtGate participants root g).filter (fun link ↦ p ∈ distributedLinkParties root link)

/-- Pair-sample links have two distinct participant endpoints.
Theorem 5.2, `04-compression.tex:568–585`. -/
@[simp] theorem mem_pairSampleLabels (parties : Finset Party) (pair : Sym2 Party) :
    pair ∈ pairSampleLabels parties ↔ (∀ p ∈ pair, p ∈ parties) ∧ ¬pair.IsDiag := by
  simp [pairSampleLabels, Finset.mem_sym2_iff]

/-- An unordered pair is a sample position precisely when its two distinct
endpoints participate in the gate. Theorem 5.2, `04-compression.tex:568–585`. -/
@[simp] theorem mk_mem_pairSampleLabels (parties : Finset Party) (p q : Party) :
    Sym2.mk p q ∈ pairSampleLabels parties ↔ p ∈ parties ∧ q ∈ parties ∧ p ≠ q := by
  simp [pairSampleLabels, Sym2.mk_isDiag_iff, and_assoc]

/-- There are exactly `choose parties.card 2` pair-sample links at a gate.
Theorem 5.2, `04-compression.tex:581–585`. -/
theorem card_pairSampleLabels (parties : Finset Party) :
    (pairSampleLabels parties).card = parties.card.choose 2 := by
  rw [pairSampleLabels, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag,
    Sym2.card_image_offDiag]

/-- Sample positions meeting a participating party are in bijection with the
other gate participants. Theorem 5.2, `04-compression.tex:568–588`. -/
theorem filter_pairSampleLabels_eq_map (parties : Finset Party) (p : Party)
    (hp : p ∈ parties) :
    (pairSampleLabels parties).filter (fun pair ↦ p ∈ pair.toFinset) =
      (parties.erase p).map (Sym2.mkEmbedding p) := by
  ext pair
  constructor
  · intro hpair
    obtain ⟨hlabel, hmem⟩ := Finset.mem_filter.mp hpair
    obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hmem)
    obtain ⟨_, hq, hne⟩ := (mk_mem_pairSampleLabels _ _ _).mp hlabel
    exact Finset.mem_map.mpr ⟨q, Finset.mem_erase.mpr ⟨hne.symm, hq⟩, rfl⟩
  · intro hpair
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hpair
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
    apply Finset.mem_filter.mpr
    exact ⟨(mk_mem_pairSampleLabels _ _ _).mpr ⟨hp, hq, hne.symm⟩,
      Sym2.mem_toFinset.mpr (Sym2.mem_iff.mpr (Or.inl rfl))⟩

/-- Exactly one sample link per other gate participant meets a participating
party. Theorem 5.2, `04-compression.tex:568–588`. -/
theorem card_filter_pairSampleLabels (parties : Finset Party) (p : Party)
    (hp : p ∈ parties) :
    ((pairSampleLabels parties).filter (fun pair ↦ p ∈ pair.toFinset)).card =
      parties.card - 1 := by
  rw [filter_pairSampleLabels_eq_map parties p hp, Finset.card_map,
    Finset.card_erase_of_mem hp]

/-- A star at a participating root has exactly `parties.card - 1` links, and pair
samples add `choose parties.card 2`. Theorem 5.2, `04-compression.tex:565–585`. -/
theorem card_gateLinkLabels (parties : Finset Party) (root : Party) (hroot : root ∈ parties) :
    (gateLinkLabels parties root).card = parties.card - 1 + parties.card.choose 2 := by
  rw [gateLinkLabels, Finset.card_disjSum, Finset.card_erase_of_mem hroot,
    card_pairSampleLabels]

/-- Bounded gate arity bounds the number of its star and pair-sample links.
Theorem 5.2, `04-compression.tex:581–585`. -/
theorem card_gateLinkLabels_le (parties : Finset Party) (root : Party) (b : ℕ)
    (hroot : root ∈ parties) (harity : parties.card ≤ b) :
    (gateLinkLabels parties root).card ≤ b - 1 + b.choose 2 := by
  rw [card_gateLinkLabels parties root hroot]
  exact Nat.add_le_add (Nat.sub_le_sub_right harity 1) (Nat.choose_le_choose 2 harity)

/-- At most `2 * (parties.card - 1)` gate links meet a participating party: at
most one whole star and one sample link for each other participant.
Theorem 5.2, `04-compression.tex:565–588`. -/
theorem card_incidentGateLinkLabels_le (parties : Finset Party) (root p : Party)
    (hroot : root ∈ parties) (hp : p ∈ parties) :
    (incidentGateLinkLabels parties root p).card ≤ 2 * (parties.card - 1) := by
  have hsplit : incidentGateLinkLabels parties root p =
      ((parties.erase root).filter (fun q ↦ p ∈ ({root, q} : Finset Party))).disjSum
        ((pairSampleLabels parties).filter (fun pair ↦ p ∈ pair.toFinset)) := by
    ext label
    rw [incidentGateLinkLabels, Finset.mem_filter]
    cases label <;> simp only [gateLinkLabels, gateLinkParties,
      Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_filter]
  rw [hsplit, Finset.card_disjSum, card_filter_pairSampleLabels parties p hp,
    Nat.two_mul]
  exact Nat.add_le_add_right
    ((Finset.card_filter_le _ _).trans_eq (Finset.card_erase_of_mem hroot)) _

/-- Every endpoint of a constructed gate-local link participates in that gate.
Theorem 5.2, `04-compression.tex:565–588`. -/
theorem gateLinkParties_subset (parties : Finset Party) (root : Party)
    (hroot : root ∈ parties) {label : Party ⊕ Sym2 Party}
    (hlabel : label ∈ gateLinkLabels parties root) :
    gateLinkParties root label ⊆ parties := by
  cases label with
  | inl q =>
      have hq : q ∈ parties := (Finset.mem_erase.mp
        (Finset.inl_mem_disjSum.mp hlabel)).2
      intro p hp
      simp only [gateLinkParties, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hroot
      · exact hq
  | inr pair =>
      have hp := (mem_pairSampleLabels parties pair).mp
        (Finset.inr_mem_disjSum.mp hlabel)
      intro p hmem
      exact hp.1 p (Sym2.mem_toFinset.mp hmem)

/-- Every constructed gate-local link joins two distinct parties.
Theorem 5.2, `04-compression.tex:565–588`. -/
theorem card_gateLinkParties (parties : Finset Party) (root : Party)
    {label : Party ⊕ Sym2 Party} (hlabel : label ∈ gateLinkLabels parties root) :
    (gateLinkParties root label).card = 2 := by
  cases label with
  | inl q =>
      have hq := Finset.mem_erase.mp (Finset.inl_mem_disjSum.mp hlabel)
      exact Finset.card_pair_eq_two_iff.mpr hq.1.symm
  | inr pair =>
      have hp := (mem_pairSampleLabels parties pair).mp
        (Finset.inr_mem_disjSum.mp hlabel)
      exact Sym2.card_toFinset_of_not_isDiag pair hp.2

omit [DecidableEq Gate] in
/-- Gate tagging preserves each gate's number of links.
Theorem 5.2, `04-compression.tex:565–588`. -/
theorem card_linksAtGate (participants : Gate → Finset Party) (root : Gate → Party) (g : Gate) :
    (linksAtGate participants root g).card = (gateLinkLabels (participants g) (root g)).card := by
  simp [linksAtGate]

omit [DecidableEq Gate] in
/-- A constructed link belongs to its tagged gate, with a valid local label.
Theorem 5.2, `04-compression.tex:565–588`. -/
@[simp] theorem mem_linksAtGate (participants : Gate → Finset Party) (root : Gate → Party)
    (g : Gate) (link : Gate × (Party ⊕ Sym2 Party)) :
    link ∈ linksAtGate participants root g ↔
      link.1 = g ∧ link.2 ∈ gateLinkLabels (participants g) (root g) := by
  rcases link with ⟨h, label⟩
  simp only [linksAtGate, Finset.mem_map, Function.Embedding.sectR_apply]
  constructor
  · rintro ⟨label', hlabel, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨rfl, hlabel⟩
  · rintro ⟨rfl, hlabel⟩
    exact ⟨label, hlabel, rfl⟩

omit [DecidableEq Gate] in
/-- Gate tagging preserves the number of links incident to a party.
Theorem 5.2, `04-compression.tex:581–588`. -/
theorem card_incidentLinksAtGate (participants : Gate → Finset Party) (root : Gate → Party)
    (p : Party) (g : Gate) :
    (incidentLinksAtGate participants root p g).card =
      (incidentGateLinkLabels (participants g) (root g) p).card := by
  rw [incidentLinksAtGate, linksAtGate, Finset.filter_map, Finset.card_map]
  rfl

/-- A distributed link's tag witnesses membership in the original gate list.
Theorem 5.2, `04-compression.tex:565–588`. -/
@[simp] theorem mem_distributedLinks (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party)
    (link : Gate × (Party ⊕ Sym2 Party)) :
    link ∈ distributedLinks gates participants root ↔
      link.1 ∈ gates ∧ link.2 ∈ gateLinkLabels (participants link.1) (root link.1) := by
  simp [distributedLinks, mem_linksAtGate]

/-- Both endpoints of every constructed link are co-participants in its original
gate. Locality is derived from the link construction, rather than postulated as
a field. Theorem 5.2, `04-compression.tex:581–588`. -/
theorem distributedLinkParties_subset (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    {link : Gate × (Party ⊕ Sym2 Party)} (hlink : link ∈ distributedLinks gates participants root) :
    distributedLinkParties root link ⊆ participants link.1 := by
  obtain ⟨hg, hlabel⟩ := (mem_distributedLinks _ _ _ _).mp hlink
  exact gateLinkParties_subset _ _ (hroot _ hg) hlabel

/-- Every link has precisely two distinct endpoints, even when other links join
the same pair. Theorem 5.2, `04-compression.tex:565–588`. -/
theorem card_distributedLinkParties (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party)
    {link : Gate × (Party ⊕ Sym2 Party)} (hlink : link ∈ distributedLinks gates participants root) :
    (distributedLinkParties root link).card = 2 := by
  exact card_gateLinkParties _ _ ((mem_distributedLinks _ _ _ _).mp hlink).2

/-- The tagged original gate witnesses co-participation of a link's endpoints.
Theorem 5.2, `04-compression.tex:581–588`. -/
theorem exists_common_gate_of_mem_distributedLinkParties (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    {link : Gate × (Party ⊕ Sym2 Party)} (hlink : link ∈ distributedLinks gates participants root)
    {p q : Party} (hp : p ∈ distributedLinkParties root link)
    (hq : q ∈ distributedLinkParties root link) :
    ∃ g ∈ gates, p ∈ participants g ∧ q ∈ participants g := by
  have hsub := distributedLinkParties_subset gates participants root hroot hlink
  exact ⟨link.1, ((mem_distributedLinks _ _ _ _).mp hlink).1, hsub hp, hsub hq⟩

/-- Links meeting a party come from the full lifetime list of its participating
gates. Theorem 5.2, `04-compression.tex:581–588`. -/
theorem incidentDistributedLinks_subset (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party)
    (hroot : ∀ g ∈ gates, root g ∈ participants g) (p : Party) :
    incidentDistributedLinks gates participants root p ⊆
      (incidentGates gates participants p).biUnion (incidentLinksAtGate participants root p) := by
  intro link hlink
  obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hlink
  obtain ⟨hg, hlabel⟩ := (mem_distributedLinks _ _ _ _).mp hl
  apply Finset.mem_biUnion.mpr
  exact ⟨link.1, (mem_incidentGates _ _ _ _).mpr
    ⟨hg, distributedLinkParties_subset gates participants root hroot hl hp⟩,
    Finset.mem_filter.mpr ⟨(mem_linksAtGate _ _ _ _).mpr ⟨rfl, hlabel⟩, hp⟩⟩

/-- Gate arity at most `b` and whole-lifetime participation at most `b` give
bounded virtual-link incidence. Parallel links are counted separately. The
constant is obtained by counting each party's star and sample links separately.
Theorem 5.2, `04-compression.tex:581–588`. -/
theorem card_incidentDistributedLinks_le (gates : Finset Gate)
    (participants : Gate → Finset Party) (root : Gate → Party) (b : ℕ)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (harity : ∀ g ∈ gates, (participants g).card ≤ b) (p : Party)
    (hlifetime : (incidentGates gates participants p).card ≤ b) :
    (incidentDistributedLinks gates participants root p).card ≤
      2 * b * (b - 1) := by
  calc
    _ ≤ ((incidentGates gates participants p).biUnion
        (incidentLinksAtGate participants root p)).card :=
      Finset.card_le_card (incidentDistributedLinks_subset gates participants root hroot p)
    _ ≤ (incidentGates gates participants p).card * (2 * (b - 1)) := by
      apply Finset.card_biUnion_le_card_mul
      intro g hg
      have hgg := (mem_incidentGates _ _ _ _).mp hg
      rw [card_incidentLinksAtGate]
      exact (card_incidentGateLinkLabels_le _ _ _ (hroot g hgg.1) hgg.2).trans
        (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right (harity g hgg.1) 1))
    _ ≤ b * (2 * (b - 1)) := Nat.mul_le_mul_right _ hlifetime
    _ = 2 * b * (b - 1) := by ac_rfl

end TNLean.PEPS.Approximation
