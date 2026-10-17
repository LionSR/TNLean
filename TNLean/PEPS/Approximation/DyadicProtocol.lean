/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchSupply
import TNLean.PEPS.Approximation.ApproximateCircuitError
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.DistributedConstruction
import TNLean.PEPS.Approximation.DyadicActiveLabelParties
import TNLean.PEPS.Approximation.DyadicRoutingPEPS
import TNLean.PEPS.Approximation.OriginalCircuitSourceBound
import TNLean.PEPS.Approximation.ProtocolDensityError
import TNLean.PEPS.Approximation.SheetStackEndpoints

/-!
# The consequences of Proposition 7.1 used in §8

Proposition 7.1 (`prop:protocol`) of the polynomial-PEPS manuscript asserts, for all
sufficiently large `L`, a protocol that distributes the ground vector `Ω` through the padded
dyadic hierarchy. Its conclusion has four items (`06-geometry.tex:12–53`): the parties and the
product initialization; the changes, their gates, and the lifetime participation of each
party; the scales and addresses of the parties at a gate; and the reference vectors, with the
final reference `Ω ⊗ Ξ`.

This module records the consequences of Proposition 7.1 that the assembly of §8 consumes, not
the proposition itself. A protocol is modelled as a distributed construction in the sense of
Theorem 5.2 (`thm:compression`) whose chronology is cut into changes, together with a dyadic
attachment of its parties and a reference vector at every stage:

* the parties form a finite type `P` with a `DyadicPlacement`: the scale and the block indices
  of the square to which each party is attached;
* the memory is a register layout at every stage, and the change number `t` is an
  `OriginalCircuit` from the layout at stage `t` to the layout at stage `t + 1`. Its private
  maps are arbitrary contractions of one party, and its nonprivate gates carry their actual
  monomial expansions and participating parties (`04-compression.tex:21–43`);
* the initial layout holds one register for the whole private memory of each party, and the
  initial vector is a product of normalized party vectors;
* the final layout consists of one physical register for each party followed by the private
  registers to be discarded. The physical register of the unit-square party of a genuine site
  has dimension `q`, and that of every other party has dimension one;
* the reference vector of the initial stage is the initial vector.

`DyadicProtocol` holds these data. The bounds consumed by §8 are the predicate
`DyadicProtocol.IsDistributionProtocol`, and the existence of a protocol with these bounds, with
its constants chosen before the size, the Hamiltonian, and the ground vector, is the statement
`LargeSizeDyadicProtocolConsequences`. This module does not prove that statement.

**Scope restriction (consequences of Proposition 7.1):** `IsDistributionProtocol` and
`LargeSizeDyadicProtocolConsequences` are weaker than Proposition 7.1. They omit the following
clause of the source:

* the identity of the main encoded frame among the factors of the reference vectors at the
  stages strictly between the initial stage and the readout (`06-geometry.tex:38–40`); there
  only the factorization into the encoded frames of `Ω` is recorded.

This clause is not used by the density estimate of §8.1, the separation hypothesis of
Lemma 8.2, or the lifetime count. Documented in
`docs/paper-gaps/polypeps_prop71_consequences_interface.tex`. Elimination: build a richer
construction certificate carrying the omitted clause, prove Proposition 7.1 for it, and forget
it into this interface.

The bound on pair sources and messages in each monomial (Theorem 5.2, item 3,
`04-compression.tex:143–147`) is the field `IsDistributionProtocol.sourceBounded`; the gates carry
no messages, which are expanded before a gate is recorded (`04-compression.tex:42–45`). The
accuracy of the expansions at every fixed inverse power of `L` (`06-geometry.tex:29–30`) holds
because each gate of the protocol is the selected contraction: a nonprivate gate `G` is by
definition its recorded expansion `G = ∑ ξ, c ξ • M ξ`, so `‖G - ∑ ξ, c ξ • M ξ‖ = 0 ≤ L⁻ᵃ` for
every `a`. Section 8 uses these selected contractions throughout (`07-assembly.tex:29–34`).

Three consequences are proved for every protocol satisfying the bounds:

* the physical density of the actual final vector is within `C' L⁻¹⁰` of `|Ω⟩⟨Ω|` in trace
  norm (`eq:protocol-density`), by the estimates of §8.1 in
  `TNLean.PEPS.Approximation.ProtocolDensityError`;
* every party network whose links join two parties of a common nonprivate gate meets the
  separation hypothesis `DyadicPlacement.SeparationBounded` of Lemma 8.2;
* if the nonprivate gates are grouped into repaintings and junction resizes of the hierarchy,
  at most `G` to each, and a block party participates only in gates of events that use it, then
  its lifetime participation is at most `64 G` (`card_gates_le_of_uses`). This is how the
  geometric data of `TNLean.PEPS.Approximation.DyadicActiveLabelParties` feed item 2.

## Main definitions

* `TNLean.PEPS.Approximation.DyadicProtocol`: the data of a protocol.
* `TNLean.PEPS.Approximation.DyadicProtocol.trajectory`: the actual vector at every stage.
* `TNLean.PEPS.Approximation.DyadicProtocol.readout`: the physical and private coordinates of
  the final memory, with the physical part indexed by configurations of the square.
* `TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol`: the bounds of
  Proposition 7.1 consumed by §8, for given constants.
* `TNLean.PEPS.Approximation.LargeSizeDyadicProtocolConsequences`: the existence of a protocol
  with these bounds, the part of Proposition 7.1 used in §8.

## Main results

* `DyadicProtocol.IsDistributionProtocol.rectangularTraceNorm_physicalDensity_sub_le`:
  the density estimate `eq:protocol-density`.
* `TNLean.PEPS.Approximation.DyadicProtocol.IsDistributionProtocol.separationBounded`: the
  separation hypothesis of Lemma 8.2 for links between parties of a common gate.
* `TNLean.PEPS.Approximation.DyadicProtocol.participation_le_of_uses`: the lifetime bound for a
  block party from the events of the hierarchy.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex:12–58`, and its proof, `06-geometry.tex:572–681`; Theorem 5.2
  `thm:compression`, `04-compression.tex:137–160`; §8.1, `07-assembly.tex:9–63`; immutable
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are original proofs; no OpenAI
  Lean code is copied or adapted.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Finset TNLean.PEPS.PairEffect

/-- The aligned squares of the padded dyadic hierarchy of `[0, N] ^ 2`, each given by its scale
`j` and its block address `(x, y)`: the square
`[2 ^ j x, 2 ^ j (x + 1)] × [2 ^ j y, 2 ^ j (y + 1)]` lies in `[0, N] ^ 2`. When `N` is a power
of two, the root square is the one with `2 ^ j = N`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:64–65`. -/
def HierarchySquare (N : ℕ) : Type :=
  {S : ℕ × ℕ × ℕ // 2 ^ S.1 * (S.2.1 + 1) ≤ N ∧ 2 ^ S.1 * (S.2.2 + 1) ≤ N}

/-- **The data of a dyadic distribution protocol.** A protocol on the square of side `L` with
local dimension `q`, on the finite party type `P`, consists of the following.

* `placement`: the dyadic square to which each party is attached, by scale and block indices
  (`06-geometry.tex:19–21, 36–37, 633–647`).
* `initialSpace`, `initialVector`: the finite-dimensional private memory of each party and its
  normalized initial vector; the initial state is their product, a pure product across parties
  (`06-geometry.tex:21–23, 658–662`).
* `changes`, `layout`, `step`: the number of changes, the register layout at every stage, and
  the change number `t` as a chronology from the layout at stage `t` to the layout at stage
  `t + 1`. Its nonprivate gates carry their monomial expansions; every gate is a contraction
  (`06-geometry.tex:25–32`, `04-compression.tex:21–43`). The steps with `t ≥ changes` are not
  used.
* `reference`: the designated reference vector at every stage, equal to the initial vector at
  the first stage (`06-geometry.tex:39–42, 662–667`).
* `site`, `physicalDimension`, `physicalOrder`, `privateOutput`: the unit-square party of each
  genuine site, at the address of that site, and the final layout, which consists of one
  physical register per party, of dimension `q` at the unit-square party of a genuine site and
  one elsewhere, followed by the private registers to be discarded
  (`06-geometry.tex:48–51, 669–679`).

The quantitative assertions used by §8 are not part of these data; they are
`DyadicProtocol.IsDistributionProtocol`. The data omit the clauses of Proposition 7.1 listed in
the scope restriction of the module docstring.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`,
`06-geometry.tex:12–53`, with the distributed constructions of Theorem 5.2,
`04-compression.tex:21–43, 137–151`. -/
structure DyadicProtocol (L q : ℕ) (P : Type) [Fintype P] where
  /-- The dyadic square of each party: its scale and block indices. -/
  placement : DyadicPlacement P
  /-- The whole initial private memory of each party. -/
  initialSpace : P → HSpace
  /-- All private memories are finite-dimensional, without a size bound. -/
  finite_initialSpace : ∀ p, FiniteDimensional ℂ (initialSpace p)
  /-- The initial vector of each party. -/
  initialVector : ∀ p, initialSpace p
  /-- The initial party vectors are normalized. -/
  norm_initialVector : ∀ p, ‖initialVector p‖ = 1
  /-- The number of changes of the schedule. -/
  changes : ℕ
  /-- The register layout of the memory at each stage. -/
  layout : ℕ → Layout P
  /-- The initial layout holds one register for the whole memory of each party. -/
  layout_zero : layout 0 = ProductInput.wholePartyLayout initialSpace
  /-- The change number `t`, with its private maps and its nonprivate gates. -/
  step : (t : ℕ) → OriginalCircuit (layout t) (layout (t + 1))
  /-- The designated reference vector at each stage. -/
  reference : (t : ℕ) → Mem (layout t)
  /-- The reference vector of the initial stage is the initial product vector. -/
  reference_zero : reference 0 = Layout.memCongr layout_zero.symm
    (ProductInput.ofAllParties initialSpace initialVector norm_initialVector).vector
  /-- The unit-square party holding the physical output of each genuine site. -/
  site : SquareLatticeVertex L L → P
  /-- Distinct sites have distinct unit-square parties. -/
  site_injective : Function.Injective site
  /-- The party of a site is attached to the unit square at the address of that site. -/
  placement_site : ∀ v, placement.scale (site v) = 0 ∧ placement.blockX (site v) = v.1 ∧
    placement.blockY (site v) = v.2
  /-- The dimension of the physical output of each party. -/
  physicalDimension : P → ℕ
  /-- The physical output of a site has the local dimension `q`. -/
  physicalDimension_site : ∀ v, physicalDimension (site v) = q
  /-- No other party has a physical output. -/
  physicalDimension_eq_one : ∀ p, p ∉ Set.range site → physicalDimension p = 1
  /-- The order of the physical registers in the final memory. -/
  physicalOrder : List P
  /-- Each party has one physical register. -/
  physicalOrder_nodup : physicalOrder.Nodup
  /-- Every party has a physical register. -/
  mem_physicalOrder : ∀ p, p ∈ physicalOrder
  /-- The private registers retained until the final discard. -/
  privateOutput : Layout P
  /-- Each discarded register is finite-dimensional, without a size bound. -/
  finite_privateOutput : ∀ r ∈ privateOutput, FiniteDimensional ℂ r.space
  /-- The final layout: the physical registers, then the private registers. -/
  layout_changes :
    layout changes = familyPhysicalOutputLayout physicalDimension physicalOrder privateOutput
  /-- The party assigned to each square of the padded hierarchy, including the root square.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 1,
  `06-geometry.tex:19–20`, and the hierarchy, `06-geometry.tex:64–67`. -/
  squareParty : HierarchySquare (paddedSide L) → P
  /-- The square whose repainting the change `t` belongs to, as its scale and block address, or
  `none` when the change belongs to no repainting. A party outside the range of `squareParty` is
  an additional party, which belongs to the repainting of a square.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, items 1 and 3,
  `06-geometry.tex:19–22` (“at most a fixed number of additional parties for each repainting of a
  square”) and `06-geometry.tex:35–37` (“additional parties have the scale and address of the
  square to whose repainting they belong”). The construction of the protocol records here the
  square of the scheduled repainting event of each change. -/
  repaintingSquare : ℕ → Option (ℕ × ℕ × ℕ)
  /-- The encoded frames of each stage: the main encoded frame, followed by the auxiliary encoded
  frames.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, items 1 and 4,
  `06-geometry.tex:21–23` and `06-geometry.tex:38–40`. -/
  frames : ℕ → List (EncodedFrame.Frame (cellCenterPos L) q P)

namespace DyadicProtocol

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- The initial product vector of a protocol.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:21–23, 658–662`. -/
def input : ProductInput (ProductInput.wholePartyLayout D.initialSpace) :=
  ProductInput.ofAllParties D.initialSpace D.initialVector D.norm_initialVector

/-- The actual vector at every stage: the initial product vector, followed by the changes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:29–36`. -/
def trajectory : (t : ℕ) → Mem (D.layout t)
  | 0 => Layout.memCongr D.layout_zero.symm D.input.vector
  | t + 1 => (D.step t).eval (trajectory t)

theorem trajectory_zero : D.trajectory 0 = D.reference 0 := by
  rw [D.reference_zero]; rfl

theorem trajectory_succ (t : ℕ) : D.trajectory (t + 1) = (D.step t).eval (D.trajectory t) :=
  rfl

/-- The initial reference vector has norm one. -/
theorem norm_reference_zero : ‖D.reference 0‖ = 1 := by
  rw [D.reference_zero, LinearIsometryEquiv.norm_map, ProductInput.norm_vector]

/-- Every change is a contraction. -/
theorem norm_step_eval_le (t : ℕ) (v : Mem (D.layout t)) : ‖(D.step t).eval v‖ ≤ ‖v‖ := by
  simpa only [one_mul] using (D.step t).eval.le_of_opNorm_le (OriginalCircuit.norm_eval_le_one _) v

/-- The physical configurations of the parties are the configurations of the square: the
physical output of a site is at its unit-square party, and every other party has a physical
output of dimension one.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:48–51`. -/
def physicalConfigEquiv : ((p : P) → Fin (D.physicalDimension p)) ≃ Configuration L q := by
  classical
  haveI : ∀ p : {p // p ∉ Set.range D.site}, Unique (Fin (D.physicalDimension p)) := fun p ↦ by
    rw [D.physicalDimension_eq_one p p.2]; infer_instance
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range D.site) _).trans
    ((Equiv.prodUnique _ _).trans
      (Equiv.piCongr (Equiv.ofInjective D.site D.site_injective)
        fun v ↦ finCongr (D.physicalDimension_site v).symm).symm)

/-- The coordinates of the final memory: the configuration of the physical outputs on the
square, and an orthonormal coordinate of the private registers.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:43–51`, with the physical
and private registers of Theorem 5.2, `04-compression.tex:148–153`. -/
def readout : Mem (D.layout D.changes) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Configuration L q × Fin (Module.finrank ℂ (Mem D.privateOutput))) := by
  classical
  letI := Layout.finiteDimensional_mem_of_registers D.privateOutput D.finite_privateOutput
  exact (Layout.memCongr D.layout_changes).trans
    ((familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder D.physicalOrder_nodup
      D.mem_physicalOrder D.privateOutput).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (D.physicalConfigEquiv.prodCongr (Equiv.refl _))))

/-- The physical density of the actual final vector: the private registers are traced, and
the vector is not normalized.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `07-assembly.tex:36–49`. -/
def physicalDensity : Matrix (Configuration L q) (Configuration L q) ℂ :=
  Matrix.partialTraceRight (Matrix.euclideanOuterProduct (D.readout (D.trajectory D.changes))
    (D.readout (D.trajectory D.changes)))

/-- The number of nonprivate gates of the whole schedule in which the party `p` participates.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:31–32`, and Theorem 5.2,
item 2, `04-compression.tex:140–142`. -/
def participation (p : P) : ℕ :=
  ∑ t ∈ range D.changes, (D.step t).participationCount p

/-- **The bounds of Proposition 7.1 consumed by §8.** With constants `C`, `b`, `k`, `r`, and
the target vector `Ω`, the protocol satisfies:

1. every party is attached to a square of the padded hierarchy, there are at most `C L²`
   parties, and at most `b` of them are attached to any square;
2. there are at most `C L³` changes; each change has at most `b` nonprivate gates, each with
   at most `b` parties; every nonprivate gate has at most `C L ^ k` monomials, absolute
   coefficient sum at most `C L ^ k`, and at most `r` pair effects and at most `r` pair sources
   in each monomial; every party participates in at most `b` nonprivate gates over the whole
   schedule;
3. two parties of a nonprivate gate have equal or adjacent scales, and addresses at distance at
   most `b` times the side of either square in each coordinate;
4. each change takes its reference vector within `C L⁻²⁰` of the next one, and the final
   reference vector is `Ω ⊗ Ξ` with `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.

These are the consequences of the four items that the assembly of §8 uses, together with the
pair-source bound of Theorem 5.2, item 3. Each nonprivate gate `G` equals its recorded expansion
`∑ ξ, c ξ • M ξ`, so `‖G - ∑ ξ, c ξ • M ξ‖ = 0` and the expansions are accurate at every inverse
power of `L` (`06-geometry.tex:29–30`); the monomials have no messages, since messages are
expanded before a gate is recorded (`04-compression.tex:42–45`). The predicate
is weaker than the conclusion of Proposition 7.1 only in the clause listed in the scope
restriction of the module docstring.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`,
`06-geometry.tex:17–52`; the expansions are those of Theorem 5.2, item 3,
`04-compression.tex:143–147`. -/
structure IsDistributionProtocol (Ω : StateSpace L q) (C : ℝ) (b k r : ℕ) : Prop where
  /-- Item 1: every party is attached to a square of the padded hierarchy. -/
  inGrid : D.placement.InGrid (paddedSide L)
  /-- Item 1: there are `O(L²)` parties. -/
  card_le : (Fintype.card P : ℝ) ≤ C * (L : ℝ) ^ 2
  /-- Item 1: a fixed number of parties for each square. -/
  blockBounded : D.placement.BlockBounded b
  /-- Item 1: a different party is assigned to each square of the padded hierarchy, including
  the root square.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 1,
  `06-geometry.tex:18–20`, and the hierarchy, `06-geometry.tex:64–67`: “A different party is
  assigned to each dyadic square.” -/
  squareParty_injective : Function.Injective D.squareParty
  /-- Item 1: the party of a square of the hierarchy is placed at the scale and address of that
  square. Source: `06-geometry.tex:19–20, 64–67`. -/
  placement_squareParty : ∀ S, (D.placement.scale (D.squareParty S),
    D.placement.blockX (D.squareParty S), D.placement.blockY (D.squareParty S)) = S.1
  /-- Item 3: every additional party, that is every party outside the range of `squareParty`,
  belongs to the repainting of a square `S` of the hierarchy other than the root square: it has
  the scale and address of `S`, and it participates only in changes of the repainting of `S`.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 1,
  `06-geometry.tex:19–22`, and item 3, `06-geometry.tex:35–37`: “additional parties have the
  scale and address of the square to whose repainting they belong”. -/
  additionalParty : ∀ p, p ∉ Set.range D.squareParty → ∃ S : HierarchySquare (paddedSide L),
    2 ^ S.1.1 < paddedSide L ∧
      (D.placement.scale p, D.placement.blockX p, D.placement.blockY p) = S.1 ∧
      ∀ t < D.changes, ∀ g, p ∈ (D.step t).participants g → D.repaintingSquare t = some S.1
  /-- Item 3: a change recorded as belonging to the repainting of `S` belongs to the repainting
  of a square of the hierarchy other than the root square.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:19–22`, and the repainted
  squares, `06-geometry.tex:82–84`. -/
  repaintingSquare_mem : ∀ t, ∀ S, D.repaintingSquare t = some S →
    ∃ S' : HierarchySquare (paddedSide L), S'.1 = S ∧ 2 ^ S.1 < paddedSide L
  /-- Item 3: the changes recorded as belonging to the repainting of a square form one
  contiguous segment of the schedule, the repainting of that square.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:19–22, 35–37`, and the
  schedule of repaintings, `06-geometry.tex:82–87`. -/
  repaintingSquare_segment : ∀ S, ∀ t₁ t t₂, t₁ ≤ t → t ≤ t₂ → D.repaintingSquare t₁ = some S →
    D.repaintingSquare t₂ = some S → D.repaintingSquare t = some S
  /-- Item 3: every party of a change of the repainting of a square `S` of scale `j` has scale
  `j` or an adjacent scale, and its address is within `b` times the side of `S` of the address of
  `S` in each coordinate.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 3,
  `06-geometry.tex:33–37`. -/
  repaintingSquare_near : ∀ t < D.changes, ∀ S, D.repaintingSquare t = some S →
    ∀ g, ∀ p ∈ (D.step t).participants g,
      S.1 ≤ D.placement.scale p + 1 ∧ D.placement.scale p ≤ S.1 + 1 ∧
        Nat.dist (D.placement.anchor p).1 (dyadicAnchor S.1 S.2.1) ≤ b * 2 ^ S.1 ∧
        Nat.dist (D.placement.anchor p).2 (dyadicAnchor S.1 S.2.2) ≤ b * 2 ^ S.1
  /-- Item 1: initialization is a pure product across parties of the copies of `Ω`. The initial
  encoded frames are the main frame followed by the auxiliary frames; each is a copy of `Ω` with
  no hole, held entirely by one party, its designated party; and the whole initial memory of each
  party is the memory of the copies it holds, with initial vector the product of their reference
  vectors. The party holding the first frame holds the main copy.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 1,
  `06-geometry.tex:21–23`: “Initialization is a pure product across parties. One party initially
  holds the main copy of `Ω`; all auxiliary copies are initialized privately at their designated
  parties”; and the initialization in the proof, `06-geometry.tex:658–660`. -/
  initialCopies : D.frames 0 ≠ [] ∧ ∃ holder : EncodedFrame.Frame (cellCenterPos L) q P → P,
    (∀ F ∈ D.frames 0, F.holes = [] ∧ ∀ x, F.owner x = holder F) ∧ ∀ [DecidableEq P],
      (D.initialSpace = fun p =>
          EncodedFrame.framesSpace ((D.frames 0).filter fun F => holder F = p)) ∧
        ∀ [NeZero q], HEq D.initialVector
          fun p => EncodedFrame.framesVec Ω ((D.frames 0).filter fun F => holder F = p)
  /-- Item 2: at most `C L³` changes. -/
  changes_le : (D.changes : ℝ) ≤ C * (L : ℝ) ^ 3
  /-- Item 2: each change has a fixed number of nonprivate gates. -/
  nonprivateCount_le : ∀ t < D.changes, (D.step t).nonprivateCount ≤ b
  /-- Item 2: each nonprivate gate involves a fixed number of parties. -/
  card_participants_le : ∀ t < D.changes, ∀ g, ((D.step t).participants g).card ≤ b
  /-- Item 2: polynomially many monomials in every gate expansion. -/
  monomialBounded : ∀ t < D.changes, (D.step t).IsMonomialBounded ⌊C * (L : ℝ) ^ k⌋₊
  /-- Item 2: polynomially bounded coefficients and a fixed number of pair effects. -/
  expansionBounded : ∀ t < D.changes, (D.step t).IsExpansionBounded r (C * (L : ℝ) ^ k)
  /-- Item 2: bounded lifetime participation of every party. -/
  participation_le : ∀ p, D.participation p ≤ b
  /-- Item 3: parties of a gate have equal or adjacent scales. -/
  scale_le : ∀ t < D.changes, ∀ g, ∀ p ∈ (D.step t).participants g,
    ∀ p' ∈ (D.step t).participants g, D.placement.scale p ≤ D.placement.scale p' + 1
  /-- Item 3: parties of a gate have addresses at distance `O(n)`. -/
  anchor_dist_le : ∀ t < D.changes, ∀ g, ∀ p ∈ (D.step t).participants g,
    ∀ p' ∈ (D.step t).participants g,
      Nat.dist (D.placement.anchor p).1 (D.placement.anchor p').1 ≤
          b * 2 ^ D.placement.scale p ∧
        Nat.dist (D.placement.anchor p).2 (D.placement.anchor p').2 ≤
          b * 2 ^ D.placement.scale p
  /-- Item 4: the reference vector of every intermediate stage is the product of the reference
  vectors `K_F Ω` of the encoded frames of that stage, of the protocol's own `Ω`: the main encoded
  frame and the auxiliary encoded frames. All its factors have norm at most one. Which factor is
  the main frame is recorded at the initial stage, by `initialCopies`, and before the readout, by
  `mainFrame_owner`; at the stages in between, the order of the factors is not recorded. The
  initial stage is the product initialization of `initialCopies`. The last stage is the readout
  of the physical registers and the discarded ones, recorded in `reference_changes`; the readout
  change, which only rearranges registers, has no counterpart in the source, which is why that
  stage is excluded here.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 4,
  `06-geometry.tex:38–40`: “There is a designated reference vector at every stage, formed from
  the main encoded frame and the auxiliary encoded frames. All its factors have norm at most
  one.” -/
  reference_frames : ∀ [NeZero q], ∀ t, 0 < t → t < D.changes →
    (∀ F ∈ D.frames t, ‖F.refVec Ω‖ ≤ 1) ∧
      ∃ h : D.layout t = EncodedFrame.stackRegs (D.frames t) [],
        D.reference t = Layout.memCongr h.symm (EncodedFrame.framesVec Ω (D.frames t))
  /-- Item 4: before the readout, the raw registers of the main encoded frame are held by the
  parties of the genuine sites, so they become the physical outputs.

  Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 4,
  `06-geometry.tex:46–49`, and the end of the proof, `06-geometry.tex:668–681`. -/
  mainFrame_owner : ∃ M Fs, D.frames (D.changes - 1) = M :: Fs ∧ ∀ v, M.owner v = D.site v
  /-- Item 4: each change keeps the reference vector within `C L⁻²⁰`. -/
  reference_step : ∀ t < D.changes,
    ‖(D.step t).eval (D.reference t) - D.reference (t + 1)‖ ≤ C / (L : ℝ) ^ 20
  /-- Item 4: the final reference vector is `Ω ⊗ Ξ`, with `Ξ` nearly normalized. -/
  reference_changes : ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem D.privateOutput))),
    ‖Ξ‖ ≤ 1 ∧ 1 - C / (L : ℝ) ^ 57 ≤ ‖Ξ‖ ∧
      D.readout (D.reference D.changes) = Matrix.euclideanTensorVector Ω Ξ
  /-- Theorem 5.2, item 3: at most `r` pair sources in each monomial of every gate expansion,
  with the constant `r` that bounds the pair effects (`04-compression.tex:143–147`). -/
  sourceBounded : ∀ t < D.changes, (D.step t).IsSourceBounded r

namespace IsDistributionProtocol

variable {D} {Ω : StateSpace L q} {C : ℝ} {b k r : ℕ}

/-- **The protocol density estimate.** For a protocol with the bounds of §8 on a
square of side `L ≥ 1`, the physical density of the actual final vector satisfies
`‖Tr_private |Ψ⟩⟨Ψ| - |Ω⟩⟨Ω|‖₁ ≤ (2 C² + 2 C) L⁻¹⁰`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1, `eq:reference-junk` and
`eq:protocol-density`, `07-assembly.tex:11–49`. -/
theorem rectangularTraceNorm_physicalDensity_sub_le (h : D.IsDistributionProtocol Ω C b k r)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hΩ : ‖Ω‖ = 1) :
    Matrix.rectangularTraceNorm (D.physicalDensity - Matrix.euclideanOuterProduct Ω Ω) ≤
      (2 * (C * C) + 2 * C) / (L : ℝ) ^ 10 := by
  obtain ⟨Ξ, hΞ, hlower, href⟩ := h.reference_changes
  exact (rectangularTraceNorm_protocol_density_sub_le
    (fun t ↦ ((D.step t).eval : Mem (D.layout t) →ₗ[ℂ] Mem (D.layout (t + 1))))
    D.trajectory D.reference hL hC hC h.changes_le
    (fun t _ v ↦ D.norm_step_eval_le t v) D.norm_reference_zero.le D.trajectory_zero
    (fun t _ ↦ D.trajectory_succ t) h.reference_step D.readout.toLinearIsometry Ω Ξ hΩ hΞ
    hlower href).2.2

/-- **Separation of links between parties of a common gate.** If every link of a party network
joins two parties that participate in a common nonprivate gate of the schedule, the network
meets the separation hypothesis of Lemma 8.2 with constant `b`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 3,
`06-geometry.tex:34–37`, and its use in Lemma 8.2, `07-assembly.tex:61–62, 128–132`. -/
theorem separationBounded (h : D.IsDistributionProtocol Ω C b k r) {Λ : Type*}
    (src tgt : Λ → P)
    (hlink : ∀ ℓ, ∃ t < D.changes, ∃ g, src ℓ ∈ (D.step t).participants g ∧
      tgt ℓ ∈ (D.step t).participants g) :
    D.placement.SeparationBounded src tgt b := by
  intro ℓ p hp
  obtain ⟨t, ht, g, hs, htg⟩ := hlink ℓ
  rcases hp with rfl | rfl
  · exact h.anchor_dist_le t ht g _ hs _ htg
  · rw [Nat.dist_comm, Nat.dist_comm (D.placement.anchor (src ℓ)).2]
    exact h.anchor_dist_le t ht g _ htg _ hs

end IsDistributionProtocol

/-! ### Lifetime participation from the events of the hierarchy -/

/-- The nonprivate gates of the whole schedule, indexed by their change. -/
abbrev Gate : Type := Σ t : Fin D.changes, (D.step t).nonprivateLocations

/-- The participation of a party is the number of nonprivate gates of the whole schedule in
which it participates. -/
theorem participation_eq_card [DecidableEq P] (p : P) :
    D.participation p = (univ.filter fun γ : D.Gate ↦ p ∈ (D.step γ.1).participants γ.2).card := by
  rw [participation, ← Fin.sum_univ_eq_sum_range (fun t ↦ (D.step t).participationCount p),
    card_filter, Fintype.sum_sigma]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [OriginalCircuit.participationCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_filter]

/-- **Lifetime participation of a block party.** Let the nonprivate gates of the schedule
belong to the repaintings and junction resizes of the hierarchy of `[0, 2 ^ k] ^ 2`, at most `G`
to each event. If the block party `x = (j, r, s)`, represented by the party `p`, participates
only in gates of events that use `x`, then `p` participates in at most `64 G` nonprivate gates.

The hypothesis on `p` is the conclusion the source draws from the active-label invariant
`eq:geometry-active-labels`; the events and their used parties are those of
`TNLean.PEPS.Approximation.DyadicActiveLabelParties`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1, item 2,
`06-geometry.tex:31–32`, and the lifetime argument, `06-geometry.tex:572–631`. -/
theorem participation_le_of_uses {k : ℕ}
    (ev : D.Gate → DyadicSquare k ⊕ DyadicJunction k) {G : ℕ}
    (hG : ∀ e, (univ.filter fun γ ↦ ev γ = e).card ≤ G) (x : ℕ × ℕ × ℕ) (p : P)
    (hp : ∀ γ : D.Gate, p ∈ (D.step γ.1).participants γ.2 →
      Sum.elim (fun S ↦ S.Uses x) (fun J ↦ J.Uses x) (ev γ)) :
    D.participation p ≤ 64 * G := by
  classical
  rw [participation_eq_card]
  exact card_gates_le_of_uses ev hG x _ hp

end DyadicProtocol

/-- **The consequences of Proposition 7.1 used in §8.** For every `q ≥ 2` and `J, Δ > 0` there
are constants `C`, `b`, `k`, `r` and a threshold `L₀`, chosen before the size, the Hamiltonian,
the energy, and the ground vector, such that every gapped ground vector `Ω` of a square
Hamiltonian of side `L ≥ max 2 L₀` has a dyadic distribution protocol with the bounds of
`DyadicProtocol.IsDistributionProtocol`.

This is a target statement, not a proof. It is the form in which §8 uses Proposition 7.1, and
it is weaker than that proposition: it omits the clauses listed in the scope restriction of the
module docstring, so it is not the source proposition.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`,
`06-geometry.tex:12–53`, in the setting of Theorem 1.1, `00-introduction.tex:36–57`, applied
with patch and information power `60` (`07-assembly.tex:11`). -/
def LargeSizeDyadicProtocolConsequences : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ (C : ℝ) (b k r L₀ : ℕ),
      ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q, h.IsGappedGroundState E₀ Ω Δ →
          ∃ (P : Type) (_ : Fintype P) (D : DyadicProtocol L q P),
            D.IsDistributionProtocol Ω C b k r

end TNLean.PEPS.Approximation
