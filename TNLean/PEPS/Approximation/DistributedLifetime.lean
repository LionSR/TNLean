/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lifetime participation in distributed compression

Source positions have two party endpoints. A set of corrected positions therefore
touches at most twice as many parties. If each party belongs to at most `b`
nonprivate gates over its entire lifetime, all gates touching these parties number
at most `2 * b` times the number of corrected positions.

The finite gate set below contains the entire nonprivate gate list, rather than
one time layer. Gate identifiers distinguish occurrences, including repeated
uses of the same operation. The position type carries no monomial labels. These are finite
incidence results; they impose no restriction on private memory dimensions or
source Schmidt ranks and do not assert the density-compression theorem.

## Main definitions and statements

- `correctedParties`: endpoints of a finite set of corrected source positions.
- `incidentGates`: all nonprivate gates in which a party participates.
- `gatesTouching`: all nonprivate gates meeting a specified party set.
- `card_correctedParties_le`: the endpoint bound `2 * S.card`.
- `card_gatesTouching_correctedParties_le`: the lifetime bound `2 * b * S.card`.

## References

- OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2 (`thm:compression`), proof paragraph
  “Expansion by corrected positions”, `04-compression.tex:342–381`, especially
  `eq:compression-subset-expansion` and `eq:compression-choice-cost`.
  [Pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L342).

These proofs are newly written from the paper's mathematical argument. No OpenAI
Lean code is copied or adapted.
-/

/-!
Original proof provenance.
Source: September 24, 2026.
Paper file: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex
Labels: thm:compression, eq:compression-subset-expansion;
independently formalized; no upstream Lean proof text reused.
Mathematical source commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a.

Provenance-ID: 8769-lifetime-source-endpoints
Downstream declaration: TNLean.PEPS.Approximation.sourceEndpoints
Provenance-ID: 8769-lifetime-corrected-parties
Downstream declaration: TNLean.PEPS.Approximation.correctedParties
Provenance-ID: 8769-lifetime-incident-gates
Downstream declaration: TNLean.PEPS.Approximation.incidentGates
Provenance-ID: 8769-lifetime-gates-touching
Downstream declaration: TNLean.PEPS.Approximation.gatesTouching
Provenance-ID: 8769-lifetime-mem-source-endpoints
Downstream declaration: TNLean.PEPS.Approximation.mem_sourceEndpoints
Provenance-ID: 8769-lifetime-mem-corrected-parties
Downstream declaration: TNLean.PEPS.Approximation.mem_correctedParties
Provenance-ID: 8769-lifetime-mem-incident-gates
Downstream declaration: TNLean.PEPS.Approximation.mem_incidentGates
Provenance-ID: 8769-lifetime-mem-gates-touching
Downstream declaration: TNLean.PEPS.Approximation.mem_gatesTouching
Provenance-ID: 8769-lifetime-card-source-endpoints-le
Downstream declaration: TNLean.PEPS.Approximation.card_sourceEndpoints_le
Provenance-ID: 8769-lifetime-card-corrected-parties-le
Downstream declaration: TNLean.PEPS.Approximation.card_correctedParties_le
Provenance-ID: 8769-lifetime-card-gates-touching-le
Downstream declaration: TNLean.PEPS.Approximation.card_gatesTouching_le
Provenance-ID: 8769-lifetime-card-gates-touching-corrected-parties-le
Downstream declaration: TNLean.PEPS.Approximation.card_gatesTouching_correctedParties_le
Provenance-ID: 8769-lifetime-owner-mem-gates-touching-corrected-parties
Downstream declaration: TNLean.PEPS.Approximation.owner_mem_gatesTouching_correctedParties
Provenance-ID: 8769-lifetime-disjoint-participants-of-not-mem-gates-touching
Downstream declaration: TNLean.PEPS.Approximation.disjoint_participants_of_not_mem_gatesTouching
-/

namespace TNLean.PEPS.Approximation

variable {Party Gate Position : Type*} [DecidableEq Party] [DecidableEq Gate]

/-- The two endpoints of a source position; coincident endpoints are counted once.
Theorem 5.2, corrected-position expansion, `04-compression.tex:342–360`. -/
def sourceEndpoints (endpoints : Position → Party × Party) (e : Position) : Finset Party :=
  { (endpoints e).1, (endpoints e).2 }

/-- Parties incident to corrected source positions. `S` indexes positions, without
choosing ket or bra monomial labels. Theorem 5.2, `04-compression.tex:342–360`. -/
def correctedParties (endpoints : Position → Party × Party)
    (S : Finset Position) : Finset Party :=
  S.biUnion (sourceEndpoints endpoints)

/-- The complete lifetime list of nonprivate gates involving `p`.
The finite set `gates` represents the entire nonprivate gate list of Theorem 5.2,
`04-compression.tex:133–151,356–364`. -/
def incidentGates (gates : Finset Gate) (participants : Gate → Finset Party)
    (p : Party) : Finset Gate :=
  gates.filter (fun g ↦ p ∈ participants g)

/-- All nonprivate gates touching `A`, including gates whose own source positions
are uncorrected. Theorem 5.2, `04-compression.tex:356–364`. -/
def gatesTouching (gates : Finset Gate) (participants : Gate → Finset Party)
    (A : Finset Party) : Finset Gate :=
  A.biUnion (incidentGates gates participants)

/-- Endpoint membership in a source position. Theorem 5.2,
`04-compression.tex:356–360`. -/
@[simp] theorem mem_sourceEndpoints (endpoints : Position → Party × Party)
    (e : Position) (p : Party) :
    p ∈ sourceEndpoints endpoints e ↔ p = (endpoints e).1 ∨ p = (endpoints e).2 := by
  simp [sourceEndpoints]

/-- Corrected-party membership depends only on corrected source positions.
Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342–360`. -/
@[simp] theorem mem_correctedParties (endpoints : Position → Party × Party)
    (S : Finset Position) (p : Party) :
    p ∈ correctedParties endpoints S ↔
      ∃ e ∈ S, p = (endpoints e).1 ∨ p = (endpoints e).2 := by
  simp [correctedParties]

omit [DecidableEq Gate] in
/-- Lifetime gate membership. Theorem 5.2, `04-compression.tex:133–151,356–364`. -/
@[simp] theorem mem_incidentGates (gates : Finset Gate)
    (participants : Gate → Finset Party) (p : Party) (g : Gate) :
    g ∈ incidentGates gates participants p ↔ g ∈ gates ∧ p ∈ participants g := by
  simp [incidentGates]

/-- A gate is affected precisely when some participant belongs to `A`.
Theorem 5.2, `04-compression.tex:356–364`. -/
theorem mem_gatesTouching (gates : Finset Gate) (participants : Gate → Finset Party)
    (A : Finset Party) (g : Gate) :
    g ∈ gatesTouching gates participants A ↔
      g ∈ gates ∧ ∃ p ∈ A, p ∈ participants g := by
  simp only [gatesTouching, Finset.mem_biUnion, mem_incidentGates]
  constructor
  · rintro ⟨p, hp, hg, hpg⟩
    exact ⟨hg, p, hp, hpg⟩
  · rintro ⟨hg, p, hp, hpg⟩
    exact ⟨p, hp, hg, hpg⟩

/-- Each corrected source position has at most two endpoints.
Theorem 5.2, `04-compression.tex:356–360`. -/
theorem card_sourceEndpoints_le (endpoints : Position → Party × Party) (e : Position) :
    (sourceEndpoints endpoints e).card ≤ 2 := by
  simpa [sourceEndpoints] using
    (Finset.card_insert_le (endpoints e).1 { (endpoints e).2 })

/-- The union of endpoints of `S` contains at most `2 * S.card` parties.
Theorem 5.2, `04-compression.tex:356–360`. -/
theorem card_correctedParties_le (endpoints : Position → Party × Party)
    (S : Finset Position) :
    (correctedParties endpoints S).card ≤ 2 * S.card := by
  simpa [correctedParties, Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul S (sourceEndpoints endpoints) 2
      (fun e _ ↦ card_sourceEndpoints_le endpoints e)

/-- Bounded lifetime participation bounds the number of gates meeting any party
set. Theorem 5.2, `04-compression.tex:356–364`. -/
theorem card_gatesTouching_le (gates : Finset Gate) (participants : Gate → Finset Party)
    (A : Finset Party) (b : ℕ)
    (hlifetime : ∀ p ∈ A, (incidentGates gates participants p).card ≤ b) :
    (gatesTouching gates participants A).card ≤ b * A.card := by
  simpa [gatesTouching, Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul A (incidentGates gates participants) b hlifetime

/-- At most `2 * b * S.card` nonprivate gates meet corrected endpoints. The bound
uses every participating gate over the party's entire lifetime.
Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex:356–372`. -/
theorem card_gatesTouching_correctedParties_le (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (S : Finset Position) (b : ℕ)
    (hlifetime : ∀ p ∈ correctedParties endpoints S,
      (incidentGates gates participants p).card ≤ b) :
    (gatesTouching gates participants (correctedParties endpoints S)).card ≤
      2 * b * S.card := by
  calc
    _ ≤ b * (correctedParties endpoints S).card :=
      card_gatesTouching_le gates participants _ b hlifetime
    _ ≤ b * (2 * S.card) := Nat.mul_le_mul_left b (card_correctedParties_le endpoints S)
    _ = 2 * b * S.card := by ac_rfl

/-- A corrected slot's owner is among the affected gates whenever the slot's
endpoints participate in its owner gate. Theorem 5.2, `04-compression.tex:342–364`.
The hypothesis is ordinary source-position incidence, rather than an assumed
affected-gate cardinality bound. -/
theorem owner_mem_gatesTouching_correctedParties (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (owner : Position → Gate) (S : Finset Position) {e : Position} (he : e ∈ S)
    (howner : owner e ∈ gates) (hparticipant : (endpoints e).1 ∈ participants (owner e)) :
    owner e ∈ gatesTouching gates participants (correctedParties endpoints S) := by
  apply (mem_gatesTouching _ _ _ _).2
  exact ⟨howner, (endpoints e).1, (mem_correctedParties _ _ _).2 ⟨e, he, Or.inl rfl⟩,
    hparticipant⟩

/-- A gate outside the affected set contains no corrected endpoint. Thus all
exterior gates can retain their aggregate contractions in the corrected-position
expansion. Theorem 5.2, `04-compression.tex:356–381`. -/
theorem disjoint_participants_of_not_mem_gatesTouching (gates : Finset Gate)
    (participants : Gate → Finset Party) (A : Finset Party) {g : Gate} (hg : g ∈ gates)
    (hnot : g ∉ gatesTouching gates participants A) :
    Disjoint (participants g) A := by
  apply Finset.disjoint_left.2
  intro p hpg hpA
  exact hnot ((mem_gatesTouching _ _ _ _).2 ⟨hg, p, hpA, hpg⟩)

end TNLean.PEPS.Approximation
