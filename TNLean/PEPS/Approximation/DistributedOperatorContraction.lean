/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedLinks
import TNLean.PEPS.DependentDiagonalContraction
import TNLean.PEPS.DependentPhysicalProductRangeSupport

/-!
# Exact operator contraction on distributed star and sample links

Gate labels are shared on the actual gate-occurrence-tagged star links of
`DistributedLinks`; each pair-sample link carries one sample index. Explicit
local equality tensors synchronize the gate labels, and each scalar coefficient
is inserted once at the gate's participating root. Their contraction is the
literal weighted sum of the supplied party-local rectangular matrices over
global gate labels and sample indices.

The gate label may be the complete ket/bra pair `(ξ, ζ)`. Private memories and
garbage coordinates belong inside the supplied local matrices; they are not
virtual link alphabets. Identifying those matrices with an actual chronological
circuit and proving polynomial label bounds remain separate obligations.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states* (September 24, 2026), Theorem 5.2 (`thm:compression`), the network
construction in `04-compression.tex:565–579`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These proofs are independently
written; no upstream Lean proof text is reused.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation.DistributedOperatorContraction

open DependentBondNetwork

variable {Party Gate : Type*} [DecidableEq Party] [DecidableEq Gate]
variable (gates : Finset Gate) (participants : Gate → Finset Party) (root : Gate → Party)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.ActiveGate
Provenance-ID: p09-tn-operator-activegate
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The active gate occurrences, retaining repeated uses of the same operation.
Theorem 5.2, `04-compression.tex:565–568`. -/
abbrev ActiveGate := {g // g ∈ gates}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.Link
Provenance-ID: p09-tn-operator-link
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The actual star/sample link family, with its gate occurrence and kind tags.
Theorem 5.2, `04-compression.tex:565–588`. -/
abbrev Link := {e // e ∈ distributedLinks gates participants root}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.GateAt
Provenance-ID: p09-tn-operator-gateat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Gates whose local branch label is visible at party `p`.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev GateAt (p : Party) := {g : ActiveGate gates // p ∈ participants g.1}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.Sample
Provenance-ID: p09-tn-operator-sample
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- A sample position for each unordered pair of distinct gate participants.
Theorem 5.2, `04-compression.tex:568–571`. -/
abbrev Sample := Σ g : ActiveGate gates,
  {pair // pair ∈ pairSampleLabels (participants g.1)}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.SampleAt
Provenance-ID: p09-tn-operator-sampleat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Sample positions incident to a party, without selecting any gate branch.
Theorem 5.2, `04-compression.tex:568–579`. -/
abbrev SampleAt (p : Party) := {s : Sample gates participants // p ∈ s.2.1.toFinset}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.starLink
Provenance-ID: p09-tn-operator-starlink
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The star link from an active gate's root to one other participant.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starLink (g : ActiveGate gates) (q : {p // p ∈ (participants g.1).erase (root g.1)}) :
    Link gates participants root :=
  ⟨(g.1, Sum.inl q.1), by
    simp only [mem_distributedLinks, gateLinkLabels, Finset.inl_mem_disjSum]
    exact ⟨g.2, q.2⟩⟩

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.sampleLink
Provenance-ID: p09-tn-operator-samplelink
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The tagged sample link of one pair position.
Theorem 5.2, `04-compression.tex:568–571`. -/
def sampleLink (s : Sample gates participants) : Link gates participants root :=
  ⟨(s.1.1, Sum.inr s.2.1), by
    simp only [mem_distributedLinks, gateLinkLabels, Finset.inr_mem_disjSum]
    exact ⟨s.1.2, s.2.2⟩⟩

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.src
Provenance-ID: p09-tn-operator-src
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The first endpoint, orienting unordered sample pairs by a quotient representative.
Theorem 5.2, `04-compression.tex:565–579`; orientation is bookkeeping only. -/
def src (e : Link gates participants root) : Party :=
  match e.1.2 with
  | Sum.inl _ => root e.1.1
  | Sum.inr pair => pair.out.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.tgt
Provenance-ID: p09-tn-operator-tgt
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The second endpoint of a star or sample link.
Theorem 5.2, `04-compression.tex:565–579`. -/
def tgt (e : Link gates participants root) : Party :=
  match e.1.2 with
  | Sum.inl q => q
  | Sum.inr pair => pair.out.2

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.endpoints_eq
Provenance-ID: p09-tn-operator-endpoints_eq
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.LinkAt
Provenance-ID: p09-tn-operator-linkat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Local link incidences read each actual link once.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev LinkAt (p : Party) :=
  {e : Link gates participants root // p ∈ distributedLinkParties root e.1}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.alphabet
Provenance-ID: p09-tn-operator-alphabet
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- A star carries one complete gate label, a sample link one index in `Fin k`.
Theorem 5.2, `04-compression.tex:565–571`. -/
def alphabet (Label : Gate → Type) (k : ℕ) (e : Link gates participants root) : Type _ :=
  match e.1.2 with
  | Sum.inl _ => Label e.1.1
  | Sum.inr _ => Fin k

variable (hroot : ∀ g ∈ gates, root g ∈ participants g)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.starGateAt
Provenance-ID: p09-tn-operator-stargateat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Either endpoint of a star is a participant of its owner gate.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starGateAt (p : Party) (g : ActiveGate gates)
    (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p) : GateAt gates participants p :=
  ⟨g, hp.elim (fun h => h ▸ hroot g.1 g.2)
    (fun h => h ▸ (Finset.mem_erase.mp q.2).2)⟩

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.rootGateAt
Provenance-ID: p09-tn-operator-rootgateat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The participating root's local occurrence of its gate label.
Theorem 5.2, `04-compression.tex:565–573`. -/
def rootGateAt (g : ActiveGate gates) : GateAt gates participants (root g.1) :=
  ⟨g, hroot g.1 g.2⟩

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.starLinkAt
Provenance-ID: p09-tn-operator-starlinkat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- A star read at either endpoint as a local virtual incidence.
Theorem 5.2, `04-compression.tex:565–568`. -/
def starLinkAt (p : Party) (g : ActiveGate gates)
    (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p) : LinkAt gates participants root p :=
  ⟨starLink gates participants root g q, by
    change p ∈ {root g.1, q.1}
    simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using hp⟩

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.sampleLinkAt
Provenance-ID: p09-tn-operator-samplelinkat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- A sample position read through its actual local sample link.
Theorem 5.2, `04-compression.tex:568–571`. -/
def sampleLinkAt (p : Party) (s : SampleAt gates participants p) :
    LinkAt gates participants root p :=
  ⟨sampleLink gates participants root s.1, s.2⟩

variable (Label : Gate → Type) (k : ℕ)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.GateLabelsAt
Provenance-ID: p09-tn-operator-gatelabelsat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The local gate-label assignment, including the full ket/bra pair in density applications.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev GateLabelsAt (p : Party) := (g : GateAt gates participants p) → Label g.1.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.LinkLabelsAt
Provenance-ID: p09-tn-operator-linklabelsat
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- A local virtual assignment with no private-memory or garbage indices.
Theorem 5.2, `04-compression.tex:571–579`. -/
abbrev LinkLabelsAt (p : Party) :=
  (e : LinkAt gates participants root p) → alphabet gates participants root Label k e.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.StarConsistent
Provenance-ID: p09-tn-operator-starconsistent
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Gate-label equality at every incident star edge. No sample or physical condition is imposed.
Theorem 5.2, `04-compression.tex:565–568`. -/
def StarConsistent (p : Party) (η : LinkLabelsAt gates participants root Label k p)
    (ξ : GateLabelsAt gates participants Label p) : Prop :=
  ∀ (g : ActiveGate gates) (q : {p // p ∈ (participants g.1).erase (root g.1)})
    (hp : root g.1 = p ∨ q.1 = p),
    η (starLinkAt gates participants root p g q hp) =
      ξ (starGateAt gates participants root hroot p g q hp)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.localSamples
Provenance-ID: p09-tn-operator-localsamples
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The independent sample indices visible at one party.
Theorem 5.2, `04-compression.tex:568–579`. -/
def localSamples (p : Party) (η : LinkLabelsAt gates participants root Label k p) :
    SampleAt gates participants p → Fin k :=
  fun s => η (sampleLinkAt gates participants root p s)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.rootCoefficient
Provenance-ID: p09-tn-operator-rootcoefficient
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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
/- TNLean.PEPS.Approximation.DistributedOperatorContraction.localTensor
Provenance-ID: p09-tn-operator-localtensor
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.alphabetFintype
Provenance-ID: p09-tn-operator-alphabetfintype
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Finite virtual alphabets are determined solely by branch labels and sample indices.
Theorem 5.2, `04-compression.tex:565–571`. -/
instance alphabetFintype [∀ g, Fintype (Label g)] (e : Link gates participants root) :
    Fintype (alphabet gates participants root Label k e) := by
  rcases e with ⟨⟨g, label⟩, he⟩
  cases label <;> dsimp [alphabet] <;> infer_instance

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.GateLabels
Provenance-ID: p09-tn-operator-gatelabels
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- One global branch label per active gate occurrence.
Theorem 5.2, `04-compression.tex:565–568`. -/
abbrev GateLabels := (g : ActiveGate gates) → Label g.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.LinkLabels
Provenance-ID: p09-tn-operator-linklabels
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- One global virtual label per actual star/sample link.
Theorem 5.2, `04-compression.tex:565–571`. -/
abbrev LinkLabels := (e : Link gates participants root) →
  alphabet gates participants root Label k e

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.restrictGates
Provenance-ID: p09-tn-operator-restrictgates
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Restrict global gate labels to the occurrences involving party `p`.
Theorem 5.2, `04-compression.tex:565–579`. -/
def restrictGates (ξ : GateLabels gates Label) (p : Party) :
    GateLabelsAt gates participants Label p := fun g => ξ g.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.restrictLinks
Provenance-ID: p09-tn-operator-restrictlinks
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Restrict global link labels to those incident to a party.
Theorem 5.2, `04-compression.tex:565–579`. -/
def restrictLinks (η : LinkLabels gates participants root Label k) (p : Party) :
    LinkLabelsAt gates participants root Label k p := fun e => η e.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.restrictSamples
Provenance-ID: p09-tn-operator-restrictsamples
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Restrict a global sample assignment to the sample positions at a party.
Theorem 5.2, `04-compression.tex:568–579`. -/
def restrictSamples (j : Sample gates participants → Fin k) (p : Party) :
    SampleAt gates participants p → Fin k := fun s => j s.1

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.sharedLinkLabels
Provenance-ID: p09-tn-operator-sharedlinklabels
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.sharedLinkLabels_consistent
Provenance-ID: p09-tn-operator-sharedlinklabels_consistent
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.ConsistentConfig
Provenance-ID: p09-tn-operator-consistentconfig
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Consistent virtual assignments and all party-local gate labels.
Theorem 5.2, `04-compression.tex:565–579`. -/
abbrev ConsistentConfig :=
  {x : LinkLabels gates participants root Label k ×
    ((p : Party) → GateLabelsAt gates participants Label p) //
    ∀ p, StarConsistent gates participants root hroot Label k p
      (restrictLinks gates participants root Label k x.1 p) (x.2 p)}

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.gateLabelsOfConfig
Provenance-ID: p09-tn-operator-gatelabelsofconfig
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The common gate assignment recovered at the participating roots.
Theorem 5.2, `04-compression.tex:565–568`. -/
def gateLabelsOfConfig (x : ConsistentConfig gates participants root hroot Label k) :
    GateLabels gates Label :=
  fun g => x.1.2 (root g.1) (rootGateAt gates participants root hroot g)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.samplesOfConfig
Provenance-ID: p09-tn-operator-samplesofconfig
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Recover one sample value from each actual pair link.
Theorem 5.2, `04-compression.tex:568–571`. -/
def samplesOfConfig (x : ConsistentConfig gates participants root hroot Label k) :
    Sample gates participants → Fin k :=
  fun s => x.1.1 (sampleLink gates participants root s)

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.gateLabel_eq_root
Provenance-ID: p09-tn-operator-gatelabel_eq_root
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.sharedLinkLabels_recover
Provenance-ID: p09-tn-operator-sharedlinklabels_recover
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.consistentConfigEquiv
Provenance-ID: p09-tn-operator-consistentconfigequiv
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.endpointLabels
Provenance-ID: p09-tn-operator-endpointlabels
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.endpointLabels_diagonal
Provenance-ID: p09-tn-operator-endpointlabels_diagonal
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.localSamples_sharedLinkLabels
Provenance-ID: p09-tn-operator-localsamples_sharedlinklabels
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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
/- TNLean.PEPS.Approximation.DistributedOperatorContraction.prod_rootCoefficient
Provenance-ID: p09-tn-operator-prod_rootcoefficient
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Every gate coefficient occurs once in the product of the local root-owned factors.
Theorem 5.2, `04-compression.tex:572–573`. -/
theorem prod_rootCoefficient (c : (g : Gate) → Label g → ℂ) (ξ : GateLabels gates Label) :
    (∏ p, rootCoefficient gates participants root hroot Label c p
      (restrictGates gates participants Label ξ p)) =
      ∏ g : ActiveGate gates, c g.1 (ξ g) := by
  exact Fintype.prod_fiberwise (fun g : ActiveGate gates => root g.1)
    (fun g => c g.1 (ξ g))

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.endpointTensor
Provenance-ID: p09-tn-operator-endpointtensor
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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
/- TNLean.PEPS.Approximation.DistributedOperatorContraction.contractedOperator
Provenance-ID: p09-tn-operator-contractedoperator
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.contractedOperator_eq_linkSum
Provenance-ID: p09-tn-operator-contractedoperator_eq_linksum
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.contractedOperator_eq_branchSampleSum
Provenance-ID: p09-tn-operator-contractedoperator_eq_branchsamplesum
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.contractedOperator_eq_sum_productMatrix
Provenance-ID: p09-tn-operator-contractedoperator_eq_sum_productmatrix
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- Matrix form of exact evaluation, using the existing dependent rectangular product matrix.
Theorem 5.2, `04-compression.tex:565–579`. -/
theorem contractedOperator_eq_sum_productMatrix (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ) :
    contractedOperator gates participants root hroot Label k c T =
      ∑ ξ : GateLabels gates Label, (∏ g : ActiveGate gates, c g.1 (ξ g)) •
        ∑ j : Sample gates participants → Fin k,
          dependentPhysicalProductFamilyMatrix (fun p =>
            T p (restrictGates gates participants Label ξ p)
              (restrictSamples gates participants k j p)) := by
  apply Matrix.ext
  intro x y
  rw [contractedOperator_eq_branchSampleSum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    dependentPhysicalProductFamilyMatrix]

end Contraction

section Dimensions
variable [∀ g, Fintype (Label g)]

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.card_alphabet
Provenance-ID: p09-tn-operator-card_alphabet
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.card_alphabet_le
Provenance-ID: p09-tn-operator-card_alphabet_le
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.densityPairCoefficient
Provenance-ID: p09-tn-operator-densitypaircoefficient
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

/-- The common density-branch scalar, with bra conjugation and one gate-owned weight.
The weight may contain that gate's per-slot averaging factors, each included once.
Theorem 5.2, `04-compression.tex:565–573`. -/
def densityPairCoefficient (a : (g : Gate) → Ket g → ℂ) (b : (g : Gate) → Bra g → ℂ)
    (w : Gate → ℂ) (g : Gate) (ξζ : Ket g × Bra g) : ℂ :=
  w g * a g ξζ.1 * star (b g ξζ.2)

variable [Fintype Party] [∀ g, Fintype (Ket g)] [∀ g, Fintype (Bra g)]

/- TNLean.PEPS.Approximation.DistributedOperatorContraction.contractedOperator_densityPair_eq
Provenance-ID: p09-tn-operator-contractedoperator_densitypair_eq
Source: September 24, 2026; thm:compression; no upstream Lean proof text reused. -/

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
            dependentPhysicalProductFamilyMatrix (fun p =>
              T p (restrictGates gates participants (fun g => Ket g × Bra g) ξζ p)
                (restrictSamples gates participants k j p)) :=
  contractedOperator_eq_sum_productMatrix gates participants root hroot
    (fun g => Ket g × Bra g) k (densityPairCoefficient Ket Bra a b w) T

end DensityPair

end TNLean.PEPS.Approximation.DistributedOperatorContraction
