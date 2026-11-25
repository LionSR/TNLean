/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.GateIncidence
import QICLean.Algebra.Kronecker.PiKronecker
import Mathlib.Data.Sym.Card
import TNLean.Network.DependentBond.DependentDiagonalContraction

/-!
# Exact operator contraction on distributed star and sample links

## The links

Each nonprivate gate shares its common ket/bra label on a star and shares a
sample index along each unordered pair of distinct participants. The link
identifiers retain both their gate occurrence and their kind, so parallel links
from different gates or of different kinds remain distinct. Both endpoints of a
link take part in its gate, and the number of links meeting a party is bounded
by the gate arity and the number of gates in which the party takes part. Private
memory dimensions and source Schmidt ranks do not enter these finite incidence
results.

## The contraction

Gate labels are shared on the star links; each pair-sample link carries one
sample index. Explicit local equality tensors synchronize the gate labels, and
each scalar coefficient is inserted once at the gate's participating root. Their
contraction is the literal weighted sum of the supplied party-local rectangular
matrices over global gate labels and sample indices.

The gate label may be the complete ket/bra pair `(ξ, ζ)`. Private memories and
garbage coordinates belong inside the supplied local matrices; they are not
virtual link alphabets. Identifying those matrices with an actual chronological
circuit and proving polynomial label bounds remain separate obligations.

## Main definitions and statements

- `TNLean.Network.pairSampleLabels`: unordered pairs of distinct gate participants.
- `TNLean.Network.gateLinkLabels`: star-link and sample-link labels at one gate.
- `TNLean.Network.distributedLinks`: the actual finite gate-tagged link family.
- `TNLean.Network.distributedLinkParties_subset`: both ends belong to the original gate.
- `TNLean.Network.card_incidentDistributedLinks_le_of_arity_lifetime`: link incidence from
  separate bounds on gate arity and lifetime participation.
- `TNLean.Network.card_incidentDistributedLinks_le`: bounded link incidence from lifetime
  participation.
- `TNLean.Network.DistributedOperatorContraction.contractedOperator`: the contraction of the
  local tensors, and its expansion as a weighted sum of party products.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states* (September 24, 2026), Theorem 5.2 (`thm:compression`), the network
construction in `04-compression.tex:565–588`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
[Pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L565).
These proofs are independently written; no upstream Lean proof text is reused.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.Network

open GateIncidence

section Links

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
    (distributedLinkParties root link).card = 2 :=
  card_gateLinkParties _ _ ((mem_distributedLinks _ _ _ _).mp hlink).2

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

/-- A separate bound on the number of participants and on each party's
number of gate occurrences bounds the actual tagged links. Parallel star
and sample links are counted separately.
Theorem 5.2, `04-compression.tex:565–588`. -/
theorem card_incidentDistributedLinks_le_of_arity_lifetime
    (gates : Finset Gate) (participants : Gate → Finset Party)
    (root : Gate → Party) (arity lifetime : ℕ)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (harity : ∀ g ∈ gates, (participants g).card ≤ arity) (p : Party)
    (hlifetime : (incidentGates gates participants p).card ≤ lifetime) :
    (incidentDistributedLinks gates participants root p).card ≤
      2 * lifetime * (arity - 1) := by
  calc
    _ ≤ ((incidentGates gates participants p).biUnion
        (incidentLinksAtGate participants root p)).card :=
      Finset.card_le_card (incidentDistributedLinks_subset gates participants root hroot p)
    _ ≤ (incidentGates gates participants p).card * (2 * (arity - 1)) := by
      apply Finset.card_biUnion_le_card_mul
      intro g hg
      have hgg := (mem_incidentGates _ _ _ _).mp hg
      rw [card_incidentLinksAtGate]
      exact (card_incidentGateLinkLabels_le _ _ _ (hroot g hgg.1) hgg.2).trans
        (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right (harity g hgg.1) 1))
    _ ≤ lifetime * (2 * (arity - 1)) := Nat.mul_le_mul_right _ hlifetime
    _ = 2 * lifetime * (arity - 1) := by ac_rfl

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
      2 * b * (b - 1) :=
  card_incidentDistributedLinks_le_of_arity_lifetime gates participants root b b
    hroot harity p hlifetime

end Links

namespace DistributedOperatorContraction

open DependentBondNetwork

variable {Party Gate : Type*} [DecidableEq Party] [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset Party) (root : Gate → Party)

/-- The active gate occurrences, retaining repeated uses of the same operation.
Theorem 5.2, `04-compression.tex:565–568`. -/
abbrev ActiveGate := {g // g ∈ gates}

/-- The actual star/sample link family, with its gate occurrence and kind tags.
Theorem 5.2, `04-compression.tex:565–588`. -/
abbrev Link := {e // e ∈ distributedLinks gates participants root}

/-- Gates whose local branch label is visible at party `p`.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev GateAt (p : Party) := {g : ActiveGate gates // p ∈ participants g.1}

/-- A sample position for each unordered pair of distinct gate participants.
Theorem 5.2, `04-compression.tex:568–571`. -/
abbrev Sample := Σ g : ActiveGate gates,
  {pair // pair ∈ pairSampleLabels (participants g.1)}

/-- Sample positions incident to a party, without selecting any gate branch.
Theorem 5.2, `04-compression.tex:568–579`. -/
abbrev SampleAt (p : Party) := {s : Sample gates participants // p ∈ s.2.1.toFinset}

/-- The star link from an active gate's root to one other participant.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starLink (g : ActiveGate gates) (q : {p // p ∈ (participants g.1).erase (root g.1)}) :
    Link gates participants root :=
  ⟨(g.1, Sum.inl q.1), by
    simp only [mem_distributedLinks, gateLinkLabels, Finset.inl_mem_disjSum]
    exact ⟨g.2, q.2⟩⟩

/-- The tagged sample link of one pair position.
Theorem 5.2, `04-compression.tex:568–571`. -/
def sampleLink (s : Sample gates participants) : Link gates participants root :=
  ⟨(s.1.1, Sum.inr s.2.1), by
    simp only [mem_distributedLinks, gateLinkLabels, Finset.inr_mem_disjSum]
    exact ⟨s.1.2, s.2.2⟩⟩

/-- The first endpoint, orienting unordered sample pairs by a quotient representative.
Theorem 5.2, `04-compression.tex:565–579`; orientation is bookkeeping only. -/
def src (e : Link gates participants root) : Party :=
  match e.1.2 with
  | Sum.inl _ => root e.1.1
  | Sum.inr pair => pair.out.1

/-- The second endpoint of a star or sample link.
Theorem 5.2, `04-compression.tex:565–579`. -/
def tgt (e : Link gates participants root) : Party :=
  match e.1.2 with
  | Sum.inl q => q
  | Sum.inr pair => pair.out.2

/-- The oriented endpoints are exactly the already constructed party set.
Theorem 5.2, `04-compression.tex:581–588`. -/
theorem endpoints_eq (e : Link gates participants root) :
    {src gates participants root e, tgt gates participants root e} =
      distributedLinkParties root e.1 := by
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl q => rfl
  | inr pair =>
    change {pair.out.1, pair.out.2} = pair.toFinset
    conv_rhs => rw [← pair.out_eq]
    exact Sym2.toFinset_mk_eq.symm

/-- Local link incidences read each actual link once.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev LinkAt (p : Party) :=
  {e : Link gates participants root // p ∈ distributedLinkParties root e.1}

/-- A star carries one complete gate label, a sample link one index in `Fin k`.
Theorem 5.2, `04-compression.tex:565–571`. -/
def alphabet (Label : Gate → Type) (k : ℕ) (e : Link gates participants root) : Type _ :=
  match e.1.2 with
  | Sum.inl _ => Label e.1.1
  | Sum.inr _ => Fin k

variable (hroot : ∀ g ∈ gates, root g ∈ participants g)

/-- Either endpoint of a star is a participant of its owner gate.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starGateAt (p : Party) (g : ActiveGate gates)
    (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p) : GateAt gates participants p :=
  ⟨g, hp.elim (fun h => h ▸ hroot g.1 g.2)
    (fun h => h ▸ (Finset.mem_erase.mp q.2).2)⟩

/-- The participating root's local occurrence of its gate label.
Theorem 5.2, `04-compression.tex:565–573`. -/
def rootGateAt (g : ActiveGate gates) : GateAt gates participants (root g.1) :=
  ⟨g, hroot g.1 g.2⟩

/-- A star read at either endpoint as a local virtual incidence.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starLinkAt (p : Party) (g : ActiveGate gates)
    (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p) : LinkAt gates participants root p :=
  ⟨starLink gates participants root g q, by
    change p ∈ {root g.1, q.1}
    simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using hp⟩

/-- A sample position read through its actual local sample link.
Theorem 5.2, `04-compression.tex:568–571`. -/
def sampleLinkAt (p : Party) (s : SampleAt gates participants p) :
    LinkAt gates participants root p :=
  ⟨sampleLink gates participants root s.1, s.2⟩

variable (Label : Gate → Type) (k : ℕ)

/-- The local gate-label assignment, including the full ket/bra pair in density applications.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev GateLabelsAt (p : Party) := (g : GateAt gates participants p) → Label g.1.1

/-- A local virtual assignment with no private-memory or garbage indices.
Theorem 5.2, `04-compression.tex:571–579`. -/
abbrev LinkLabelsAt (p : Party) :=
  (e : LinkAt gates participants root p) → alphabet gates participants root Label k e.1

/-- Gate-label equality at every incident star edge. No sample or physical condition is imposed.
Theorem 5.2, `04-compression.tex:565–568`. -/
def StarConsistent (p : Party) (η : LinkLabelsAt gates participants root Label k p)
    (ξ : GateLabelsAt gates participants Label p) : Prop :=
  ∀ (g : ActiveGate gates) (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p),
    η (starLinkAt gates participants root p g q hp) =
      ξ (starGateAt gates participants root hroot p g q hp)

/-- The independent sample indices visible at one party.
Theorem 5.2, `04-compression.tex:568–579`. -/
def localSamples (p : Party) (η : LinkLabelsAt gates participants root Label k p) :
    SampleAt gates participants p → Fin k :=
  fun s => η (sampleLinkAt gates participants root p s)

/-- Scalar gate coefficients inserted only at their participating root.
A singleton gate has no star but its label is still summed at this root.
Theorem 5.2, `04-compression.tex:572–573`. -/
def rootCoefficient (c : (g : Gate) → Label g → ℂ) (p : Party)
    (ξ : GateLabelsAt gates participants Label p) : ℂ :=
  ∏ g : {g : ActiveGate gates // root g.1 = p},
    c g.1.1 (ξ ⟨g.1, by simpa only [g.2] using hroot g.1.1 g.1.2⟩)

variable {Out In : Party → Type*}

section LocalTensor
variable [Fintype Party] [∀ g, Fintype (Label g)]

open Classical in
/-- The actual local operator tensor: sum the party's gate labels, enforce star equalities,
insert root-owned coefficients, and evaluate the supplied locally contracted matrix.
Any per-slot averaging factor belongs in `c` once, rather than at both endpoints.
Theorem 5.2, `04-compression.tex:565–579`. -/
def localTensor (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (p : Party) (η : LinkLabelsAt gates participants root Label k p)
    (xy : Out p × In p) : ℂ :=
  ∑ ξ : GateLabelsAt gates participants Label p,
    if StarConsistent gates participants root hroot Label k p η ξ then
      rootCoefficient gates participants root hroot Label c p ξ *
        T p ξ (localSamples gates participants root Label k p η) xy.1 xy.2
    else 0

end LocalTensor

/-- Finite virtual alphabets are determined solely by branch labels and sample indices.
Theorem 5.2, `04-compression.tex:565–571`. -/
instance alphabetFintype [∀ g, Fintype (Label g)] (e : Link gates participants root) :
    Fintype (alphabet gates participants root Label k e) := by
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label <;> dsimp [alphabet] <;> infer_instance

/-- One global branch label per active gate occurrence.
Theorem 5.2, `04-compression.tex:565–568`. -/
abbrev GateLabels := (g : ActiveGate gates) → Label g.1

/-- One global virtual label per actual star/sample link.
Theorem 5.2, `04-compression.tex:565–571`. -/
abbrev LinkLabels := (e : Link gates participants root) →
  alphabet gates participants root Label k e

/-- Restrict global gate labels to the occurrences involving party `p`.
Theorem 5.2, `04-compression.tex:565–579`. -/
def restrictGates (ξ : GateLabels gates Label) (p : Party) :
    GateLabelsAt gates participants Label p := fun g => ξ g.1

/-- Restrict global link labels to those incident to a party.
Theorem 5.2, `04-compression.tex:565–579`. -/
def restrictLinks (η : LinkLabels gates participants root Label k) (p : Party) :
    LinkLabelsAt gates participants root Label k p := fun e => η e.1

/-- Restrict a global sample assignment to the sample positions at a party.
Theorem 5.2, `04-compression.tex:568–579`. -/
def restrictSamples (j : Sample gates participants → Fin k) (p : Party) :
    SampleAt gates participants p → Fin k := fun s => j s.1

/-- Replicate each gate's common label on its star and each sample on its tagged pair link.
Theorem 5.2, `04-compression.tex:565–571`. -/
def sharedLinkLabels (ξ : GateLabels gates Label) (j : Sample gates participants → Fin k) :
    LinkLabels gates participants root Label k := by
  rintro ⟨⟨g, label⟩, he⟩
  have h := (mem_distributedLinks gates participants root _).mp he
  cases label with
  | inl q => exact ξ ⟨g, h.1⟩
  | inr pair =>
    exact j ⟨⟨g, h.1⟩, ⟨pair, Finset.inr_mem_disjSum.mp h.2⟩⟩

/-- A replicated gate assignment satisfies every local star equality.
Theorem 5.2, `04-compression.tex:565–568`. -/
theorem sharedLinkLabels_consistent (ξ : GateLabels gates Label)
    (j : Sample gates participants → Fin k) (p : Party) :
    StarConsistent gates participants root hroot Label k p
      (restrictLinks gates participants root Label k
        (sharedLinkLabels gates participants root Label k ξ j) p)
      (restrictGates gates participants Label ξ p) := by
  intro g q hp
  rfl

/-- Consistent virtual assignments and all party-local gate labels.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev ConsistentConfig :=
  {x : LinkLabels gates participants root Label k ×
    ((p : Party) → GateLabelsAt gates participants Label p) //
    ∀ p, StarConsistent gates participants root hroot Label k p
      (restrictLinks gates participants root Label k x.1 p) (x.2 p)}

/-- The common gate assignment recovered at the participating roots.
Theorem 5.2, `04-compression.tex:565–568`. -/
def gateLabelsOfConfig (x : ConsistentConfig gates participants root hroot Label k) :
    GateLabels gates Label :=
  fun g => x.1.2 (root g.1) (rootGateAt gates participants root hroot g)

/-- Recover one sample value from each actual pair link.
Theorem 5.2, `04-compression.tex:568–571`. -/
def samplesOfConfig (x : ConsistentConfig gates participants root hroot Label k) :
    Sample gates participants → Fin k :=
  fun s => x.1.1 (sampleLink gates participants root s)

/-- A star forces each participant's gate label to equal the participating root's label.
Theorem 5.2, `04-compression.tex:565–568`. -/
theorem gateLabel_eq_root (x : ConsistentConfig gates participants root hroot Label k)
    (p : Party) (g : GateAt gates participants p) :
    x.1.2 p g = gateLabelsOfConfig gates participants root hroot Label k x g.1 := by
  rcases g with ⟨g, hg⟩
  by_cases hp : root g.1 = p
  · subst p
    rfl
  · let q : {p // p ∈ (participants g.1).erase (root g.1)} :=
      ⟨p, Finset.mem_erase.mpr ⟨Ne.symm hp, hg⟩⟩
    exact (x.2 p g q (Or.inr rfl)).symm.trans
      (x.2 (root g.1) g q (Or.inl rfl))

/-- The recovered global labels reconstruct every actual virtual label.
Theorem 5.2, `04-compression.tex:565–571`. -/
theorem sharedLinkLabels_recover (x : ConsistentConfig gates participants root hroot Label k) :
    sharedLinkLabels gates participants root Label k
      (gateLabelsOfConfig gates participants root hroot Label k x)
      (samplesOfConfig gates participants root hroot Label k x) = x.1.1 := by
  funext e
  rcases e with ⟨⟨g, label⟩, he⟩
  have h := (mem_distributedLinks gates participants root _).mp he
  cases label with
  | inl q =>
    exact (x.2 (root g) ⟨g, h.1⟩
      ⟨q, Finset.inl_mem_disjSum.mp h.2⟩ (Or.inl rfl)).symm
  | inr pair => rfl

/-- Consistent local labels are exactly global gate labels and independent sample choices.
This bijection also covers empty labels, empty link families and singleton gates.
Theorem 5.2, `04-compression.tex:565–579`. -/
def consistentConfigEquiv :
    (GateLabels gates Label × (Sample gates participants → Fin k)) ≃
      ConsistentConfig gates participants root hroot Label k where
  toFun x := ⟨(sharedLinkLabels gates participants root Label k x.1 x.2,
    restrictGates gates participants Label x.1),
    sharedLinkLabels_consistent gates participants root hroot Label k x.1 x.2⟩
  invFun x := (gateLabelsOfConfig gates participants root hroot Label k x,
    samplesOfConfig gates participants root hroot Label k x)
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact sharedLinkLabels_recover gates participants root hroot Label k x
    · funext p g
      exact (gateLabel_eq_root gates participants root hroot Label k x p g).symm

/-- Select the endpoint label at a party from an independent-endpoint configuration.
Theorem 5.2, `04-compression.tex:565–579`. -/
def endpointLabels (p : Party)
    (η : LocalConfig (src gates participants root) (tgt gates participants root)
      (alphabet gates participants root Label k) p) :
    LinkLabelsAt gates participants root Label k p :=
  fun e => if h : src gates participants root e.1 = p then
    η ⟨(e.1, false), by simp [endpointVertex, h]⟩
  else
    η ⟨(e.1, true), by
      have hp := e.2
      rw [← endpoints_eq gates participants root e.1] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact (hp.resolve_left (Ne.symm h)).symm⟩

/-- Reading diagonal endpoint labels is restriction of the same global virtual assignment.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem endpointLabels_diagonal (η : LinkLabels gates participants root Label k) (p : Party) :
    endpointLabels gates participants root Label k p
      (endpointSiteEquiv (src gates participants root) (tgt gates participants root)
        (alphabet gates participants root Label k)
        (diagonalEndpointConfig (alphabet gates participants root Label k) η) p) =
      restrictLinks gates participants root Label k η p := by
  funext e
  simp only [endpointLabels]
  split_ifs <;> rfl

/-- Shared global link labels expose exactly the party's incident sample assignment.
Theorem 5.2, `04-compression.tex:568–579`. -/
theorem localSamples_sharedLinkLabels (ξ : GateLabels gates Label)
    (j : Sample gates participants → Fin k) (p : Party) :
    localSamples gates participants root Label k p
      (restrictLinks gates participants root Label k
        (sharedLinkLabels gates participants root Label k ξ j) p) =
      restrictSamples gates participants k j p := rfl

section Contraction

variable [Fintype Party] [∀ g, Fintype (Label g)]

omit [DecidableEq Gate] [∀ g, Fintype (Label g)] in
/-- Every gate coefficient occurs once in the product of the local root-owned factors.
Theorem 5.2, `04-compression.tex:572–573`. -/
theorem prod_rootCoefficient (c : (g : Gate) → Label g → ℂ) (ξ : GateLabels gates Label) :
    (∏ p, rootCoefficient gates participants root hroot Label c p
      (restrictGates gates participants Label ξ p)) =
      ∏ g : ActiveGate gates, c g.1 (ξ g) := by
  exact Fintype.prod_fiberwise (fun g : ActiveGate gates => root g.1)
    (fun g => c g.1 (ξ g))

/-- The local operator tensor read on the two endpoint incidences of the existing network.
All sums over private coordinates have already been supplied in the local matrices.
Theorem 5.2, `04-compression.tex:573–579`. -/
def endpointTensor (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (p : Party) (η : LocalConfig (src gates participants root) (tgt gates participants root)
      (alphabet gates participants root Label k) p) (xy : Out p × In p) : ℂ :=
  localTensor gates participants root hroot Label k c T p
    (endpointLabels gates participants root Label k p η) xy

open Classical in
/-- The actual rectangular operator contracted from the constructed star/sample tensors.
Theorem 5.2, `04-compression.tex:565–579`. -/
def contractedOperator (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ) :
    Matrix ((p : Party) → Out p) ((p : Party) → In p) ℂ :=
  fun x y => network (src gates participants root) (tgt gates participants root)
    (alphabet gates participants root Label k)
    (endpointTensor gates participants root hroot Label k c T) (fun _ => 1)
    (fun p => (x p, y p))

/-- Identity bonds reduce the constructed operator to one label per actual star/sample link.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem contractedOperator_eq_linkSum (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (x : (p : Party) → Out p) (y : (p : Party) → In p) :
    contractedOperator gates participants root hroot Label k c T x y =
      ∑ η : LinkLabels gates participants root Label k,
        ∏ p, localTensor gates participants root hroot Label k c T p
          (restrictLinks gates participants root Label k η p) (x p, y p) := by
  classical
  unfold contractedOperator network bondWeight
  rw [sum_identityWeight_mul]
  apply Finset.sum_congr rfl
  intro η _
  simp only [endpointTensor, endpointLabels_diagonal]

/-- Exact star/sample operator evaluation: one common gate branch and one sample index per
position. The equality is derived from the constructed tensors, not assumed as circuit data.
It includes singleton gates, empty alphabets, empty links and `k = 0`.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem contractedOperator_eq_branchSampleSum (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (x : (p : Party) → Out p) (y : (p : Party) → In p) :
    contractedOperator gates participants root hroot Label k c T x y =
      ∑ ξ : GateLabels gates Label, (∏ g : ActiveGate gates, c g.1 (ξ g)) *
        ∑ j : Sample gates participants → Fin k,
          ∏ p, T p (restrictGates gates participants Label ξ p)
            (restrictSamples gates participants k j p) (x p) (y p) := by
  classical
  rw [contractedOperator_eq_linkSum]
  unfold localTensor
  simp_rw [Fintype.prod_sum, Fintype.prod_ite_zero]
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun z =>
    ∀ p, StarConsistent gates participants root hroot Label k p
      (restrictLinks gates participants root Label k z.1 p) (z.2 p)) _ (by simp)]
  rw [← (consistentConfigEquiv gates participants root hroot Label k).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (∏ p, rootCoefficient gates participants root hroot Label c p
    (restrictGates gates participants Label ξ p) *
    T p (restrictGates gates participants Label ξ p)
      (localSamples gates participants root Label k p
        (restrictLinks gates participants root Label k
          (sharedLinkLabels gates participants root Label k ξ j) p)) (x p) (y p)) = _
  simp only [localSamples_sharedLinkLabels, Finset.prod_mul_distrib, prod_rootCoefficient]

/-- Matrix form of exact evaluation, using the existing dependent rectangular product matrix.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem contractedOperator_eq_sum_productMatrix (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ) :
    contractedOperator gates participants root hroot Label k c T =
      ∑ ξ : GateLabels gates Label, (∏ g : ActiveGate gates, c g.1 (ξ g)) •
        ∑ j : Sample gates participants → Fin k,
          Matrix.piKronecker (fun p =>
            T p (restrictGates gates participants Label ξ p)
              (restrictSamples gates participants k j p)) := by
  apply Matrix.ext
  intro x y
  rw [contractedOperator_eq_branchSampleSum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.piKronecker_apply]

end Contraction

section Dimensions
variable [∀ g, Fintype (Label g)]

/-- Exact alphabet dimensions: the gate's branch count on a star and `k` on a sample link.
Private-memory and source-support dimensions do not occur in this formula.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem card_alphabet (e : Link gates participants root) :
    Fintype.card (alphabet gates participants root Label k e) =
      match e.1.2 with
      | Sum.inl _ => Fintype.card (Label e.1.1)
      | Sum.inr _ => k := by
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl q => rfl
  | inr pair => exact Fintype.card_fin k

/-- A supplied bound on the actual branch alphabets bounds every constructed virtual link.
Uniform polynomial branch bounds for a circuit family remain an external obligation.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem card_alphabet_le (M : ℕ) (hM : ∀ g ∈ gates, Fintype.card (Label g) ≤ M)
    (e : Link gates participants root) :
    Fintype.card (alphabet gates participants root Label k e) ≤ max M k := by
  rw [card_alphabet]
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label with
  | inl q =>
    exact (hM g ((mem_distributedLinks gates participants root _).mp he).1).trans
      (le_max_left M k)
  | inr pair => exact le_max_right M k

end Dimensions

section DensityPair
variable (Ket Bra : Gate → Type)

/-- The common density-branch scalar, with bra conjugation and one gate-owned weight.
The weight may contain that gate's per-slot averaging factors, each included once.
Theorem 5.2, `04-compression.tex:565–573`. -/
def densityPairCoefficient (a : (g : Gate) → Ket g → ℂ) (b : (g : Gate) → Bra g → ℂ)
    (w : Gate → ℂ) (g : Gate) (ξζ : Ket g × Bra g) : ℂ :=
  w g * a g ξζ.1 * star (b g ξζ.2)

variable [Fintype Party] [∀ g, Fintype (Ket g)] [∀ g, Fintype (Bra g)]

/-- The density specialization shares the entire ordered ket/bra pair on each star.
The actual network represents the literal branch/sample product-matrix sum, with bra
coefficients conjugated and each gate's scalar weight appearing once at its root.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem contractedOperator_densityPair_eq (a : (g : Gate) → Ket g → ℂ)
    (b : (g : Gate) → Bra g → ℂ) (w : Gate → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants (fun g => Ket g × Bra g) p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ) :
    contractedOperator gates participants root hroot (fun g => Ket g × Bra g) k
      (densityPairCoefficient Ket Bra a b w) T =
      ∑ ξζ : GateLabels gates (fun g => Ket g × Bra g),
        (∏ g : ActiveGate gates, w g.1 * a g.1 (ξζ g).1 * star (b g.1 (ξζ g).2)) •
          ∑ j : Sample gates participants → Fin k,
            Matrix.piKronecker (fun p =>
              T p (restrictGates gates participants (fun g => Ket g × Bra g) ξζ p)
                (restrictSamples gates participants k j p)) :=
  contractedOperator_eq_sum_productMatrix gates participants root hroot
    (fun g => Ket g × Bra g) k (densityPairCoefficient Ket Bra a b w) T

end DensityPair

end DistributedOperatorContraction

end TNLean.Network
