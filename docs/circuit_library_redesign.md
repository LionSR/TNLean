# Locality kernel and circuit library: redesign and move to QICLean

Status: plan adopted 2026-11-16; step K0 written. This document supersedes the
"Migration policy" section of `circuit_channel_architecture.md`: the directory
`TNLean/Circuit` is being split, redesigned and moved, not kept in place.

## Decision

`TNLean/Circuit` (125 modules, about 25,000 lines, namespace `QuantumCircuit`)
imports nothing from `MPS` and only seven shallow `TNLean/Algebra` modules. It
moves to QICLean, as two separate layers:

- `QICLean/Locality`: operators supported on sets of sites of a finite tensor
  product, their placement, partial traces, product vectors, and Lieb–Robinson
  bounds. This is not circuit theory. It is what most of TNLean uses.
- `QICLean/Circuit`: circuits, built on the locality layer.

No third repository is created. TNLean keeps the modules that use tensor
networks (`MPS/Preparation`, `MPS/MPU`, the area-law developments, and the
parts of `Lattice/PartyCircuit` specific to the PEPS approximation proof).

## What is wrong now

Counts are from an audit of `main` at `3d3507f` (TNLean) and `c62f178`
(QICLean).

### The directory holds two libraries

More than twenty root-level modules of `TNLean/Circuit` (`SiteEmbedding*`,
`SiteExpectation*`, `Supported*`, `EntropySupport`, `ProductVector`,
`ExpectationBounds`, ...) and all of `Circuit/LiebRobinson` mention no layer,
gate or depth. They import `Circuit/LocalCircuit` only because the definition
of `supportedOperators` sits in that file above `BondLayer`. Outside
`TNLean/Circuit`, 356 modules mention `QuantumCircuit` and 279 open the
namespace; nearly all of them (`Lattice`, `MPS/AreaLaw`, `PEPS`) use only
these operator-locality lemmas. The circuit models proper are consumed by
`MPS/Preparation` (ring depth circuits, measurement rounds, teleportation,
gate counts) and `MPS/MPU` (gate counts with a clean workspace), and by nothing
else.

### The locality kernel exists in parallel copies

- Two support predicates. `QuantumCircuit.supportedOperators d S` is a span of
  product operators, with one local dimension `d` and `S : Set ι` (279
  modules). `Entropy.IsSupportedOn X D` in QICLean is a condition on matrix
  entries, with site-dependent dimensions `n : V → ℕ` and `D : Finset V` (311
  TNLean modules, 29 QICLean modules). 61 modules use both. The two bridge
  lemmas in `Circuit/EntropySupport` are each applied in about 50 modules and
  exist only for one local dimension.
- The algebra of `Entropy.IsSupportedOn` (`add`, `neg`, `sub`, `smul`,
  `conjTranspose`, finite sums, `exp`) is proved in TNLean area-law modules
  under the QICLean namespace, not in QICLean. Its product and commutation
  lemmas carry a reference configuration `σ₀` that the statements do not need.
- At least nine constructions place a local matrix as `K ⊗ 1`:
  `QuantumCircuit.embedOp`, `Entropy.localLift`, `TNLean.Lattice.localLift`
  (same name, different definition), `Lattice.siteLift` (the same definition
  again), `MPOTensor.embedLocalOperator`, `PEPS.regionLocalTerm`,
  `dependentRegionOperatorLift`, `Pinned.liftLocal` (a hand copy of
  `embedOp`), and `localInclusion` in `QCA`. Each has its own product,
  adjoint, norm and positivity lemmas.
- Five Hamiltonian structures, three stated with one predicate and two with the
  other.

This contradicts the rule in `project_conventions.md` for Mathlib notions (no
parallel type, no bridge lemmas), which applies equally across the
QICLean–TNLean boundary.

### The circuit models do not share a definition

| Model | Semantics | Depth convention | Sites |
|---|---|---|---|
| `BondLayer`, `circuitOp`, `IsBondCircuitOfDepth` | unitary matrix | exactly `T` layers | any bond family |
| `IsBondCircuitOn` | unitary matrix | exactly `T`, inside a region | any bond family |
| `IsPairProduct`, `IsWindowProduct` | unitary matrix | at most `K` gates | open chain `Fin n` |
| `BondChannelLayer`, `channelCircuitMap` | map on matrices | exactly `T` | any bond family |
| `OnsiteChannel`, `IsLocalChannelProtocol` | map, dimension-changing | exactly `T` | ring only |
| `IsDimensionBoundedLocalChannelProtocol` | the same, bounded dimensions | exactly `T` | ring only |
| `FixedRegisterOperation` words | map, fixed alphabet | sum over the word | ring only |
| `IsPhysicalPortUnitary`, `IsPhysicalPortProtocol` | unitary; map | at most `T` (`mono` constructor) | ring ports, wires `Fin W` |
| `MeasurementProtocol` | set of output vectors | at most `T` | ring only |
| `MeasurementRound` lists | Kraus family by outcome | sum of round depths | ring only |
| `IsAdaptiveChannelProtocol` | map with outcome branches | at most `T`; layers prepended | ring only |
| `PartyCircuit.Word`, `OriginalCircuit`, `EffectCircuit`, `SourceCircuit` | contraction between tensor products of Hilbert spaces | participation counts | parties, no geometry |

Identity, composition, monotonicity in the depth, complete positivity and the
light cone are proved separately for each row, and several are missing (no
identity or append for channel circuits, no monotonicity for the exact-depth
predicates). Bridges are missing between gate count and depth, between unitary
and channel preparation at the level of states, and from measurement rounds to
adaptive conversions of states. Statements whose proofs use no geometry are
ring-only because the definitions hard-code `Layer d N`. The four inductive
types of `Lattice/PartyCircuit` repeat the constructors `id`, `comp`, local
map, `swap`, `frame` and their evaluation, and differ only in the gate
constructor.

The whole channel stack (`Circuit/Channel`, about 40 modules, and
`Measurement/AdaptiveConversion`) has no Lean consumer outside `TNLean/Circuit`;
only blueprint chapter 33 refers to it. It can be restated without touching
other directories.

## Target: the locality layer

Working names; the namespace is fixed when the layer moves (step K4).

- Configurations are `SiteConfig n = (v : V) → Fin (n v)` with site-dependent
  dimensions. One local dimension is the definitional special case
  `ι → Fin d`, so no statement about a chain or lattice changes its types.
- One support notion: the `*`-subalgebra `supportedOperators n D` of the matrix
  algebra, with membership unfolding to the matrix-entry condition. Closure
  under sums, products, adjoints, powers and functional calculus comes from the
  subalgebra, with no reference configuration. The span of product operators
  becomes a theorem about this subalgebra, not a second definition.
- One placement of a regional matrix as `K ⊗ 1`, along a region or along an
  injection of sites; the nine constructions above become this one or
  specializations of it by definition.
- One partial trace onto a region (`siteExpectation`), one product vector, one
  expectation.
- Lieb–Robinson bounds for a family of supported Hermitian terms on a graph,
  moved unchanged.

Whether regions are `Set V` or `Finset V` is settled at step K3. The predicate
is likely to take `Set V` (finite sets coerce, and light cones are sets) while
placements keep `Finset V`.

## Target: the circuit core

Nothing of the core is in a library yet. The definitions below, the Kraus
family and depth of a circuit, composition, and subadditivity of the depth
under composition have been type-checked against QICLean in a scratch file;
the signatures are fixed in step C1.

A *system* assigns a local dimension to each site, `n : S → ℕ`. A *geometry*
is a family of cells `cell : β → Finset S` on which one gate may act (the
bonds of a ring, the edges of a graph, the windows of a chain, the wires owned
by one site). One layer acts by a finite Kraus family on each of a set of
pairwise disjoint cells, and by a Kraus family at every remaining site:

```lean
structure Layer (cell : β → Finset S) (n m : S → ℕ) where
  cells : Finset β
  pairwiseDisjoint : (cells : Set β).PairwiseDisjoint cell
  gate : ∀ b ∈ cells, KrausFamily (RegionConfig n (cell b)) (RegionConfig m (cell b))
  onsite : ∀ s, (∀ b ∈ cells, s ∉ cell b) → KrausFamily (Fin (n s)) (Fin (m s))
```

Its Kraus operators are indexed by a choice of one Kraus index per cell and
per remaining site, and are products of the local entries. A circuit is a
sequence of layers in which later layers may depend on earlier Kraus indices:

```lean
inductive Circuit (cell : β → Finset S) : (S → ℕ) → (S → ℕ) → Type
  | done (n) : Circuit cell n n
  | step (L : Layer cell n m) (next : L.Index → Circuit cell m k) : Circuit cell n k
```

A circuit is data. Its Kraus family, its map on matrices, its depth (layers
that use at least one cell of positive cost), its gate count, a bound on the
intermediate dimensions, and the number of gates meeting a given site are
functions on it, defined once. Every statement "of depth `T`" means
`depth ≤ T`, so monotonicity is free; layers are listed in the order applied.
Identity, composition, trace preservation and the backward light cone are
proved once, for Kraus families.

The present models are restrictions of this one definition:

| Present model | In the core |
|---|---|
| unitary depth circuits | every Kraus family has one unitary member; `n = m` |
| channel circuits | no branching (`next` constant) |
| local channel protocols | no branching; onsite families change the dimension, free of cost |
| bounded-dimension protocols | the same with a bound on every intermediate `n s` |
| fixed-register words | the same with `n` constant in time |
| physical ports | sites are wires; cells are the wires of one site (cost 0) and pairs of neighbouring ports (cost 1) |
| measurement rounds, adaptive protocols | onsite families `|j⟩⟨j|`, with `next` depending on the outcome |
| pair and window products | unitary circuits on the open-chain geometry, measured by gate count |

The theorems relating models stay theorems: compiling a bounded protocol to
physical ports, removing measurements, and trading gate count for depth are
statements about two restrictions of `Circuit`, not about unrelated inductive
predicates.

Isometry trees, the rectangular two-site layers of matrix product unitaries and
the Margolus gates of `QCA` need layers between systems on different site sets
(blocking). They are added as a blocking map between systems after step C4.
`Lattice/PartyCircuit` is treated last: its four inductive types first become
one type parametrized by the gate constructor (step P1), then its registers,
which are finite-dimensional in every use, are compared with the core (step
P2). Whether it then becomes a restriction of `Circuit` or stays a second
calculus with a comparison theorem is decided at P2.

## `TNLean/Lattice`

`TNLean/Lattice` (472 modules, about 78,000 lines) has the same shape as
`TNLean/Circuit`: its transitive imports inside TNLean are itself, 17 modules
of `Algebra` and 20 modules of `Circuit` (the locality modules and two gate
modules), and nothing from `MPS` or `PEPS`. It can leave TNLean once the
locality layer has. It holds three unrelated things:

- Local Hamiltonians and their analysis on finite sets of sites (the root
  directory and `ClusterExpansion`, 127 modules, about 25,000 lines): Gaussian
  filtering and truncation, low-energy bases, regional entropy, the regional
  swap and reset. Half of this theory is already in QICLean (`Analysis`,
  `Entropy`), which `Lattice` imports about 100 times; the split between the
  two repositories follows no mathematical line.
- A calculus of distributed circuits and operator networks on a set of parties
  (`PartyCircuit`, `Compression`, `Sheet`, 342 modules, about 52,000 lines).
  This is not lattice theory, and it is the second circuit library described
  above. `Compression` has 254 modules, 123 of them with at most two
  declarations.
- `TreeBasisCounterexample`.

The structure `Lattice.LocalHamiltonian`, described as shared by the one- and
two-dimensional area laws, is defined on `Λ : Finset (ℤ × ℤ)`. The chain uses
`ChainHamiltonian` and `DomainHamiltonian` in `MPS/AreaLaw`, and the squares
and rectangles of `PEPS` use two more structures. Namespaces vary inside the
directory (`TNLean.Lattice`, `TNLean.Lattice.PartyCircuit`,
`Lattice.PartyCircuit`, and bare `Word`, `EffectCircuit`).

Target: the Hamiltonian part joins the locality layer in QICLean, with one
structure for a family of bounded Hermitian terms with given supports on a
finite set of sites; the chain, the integer domains, the plane, squares and
rectangles are choices of the sites and supports. The party calculus follows
the circuit plan (steps P1, P2): the reusable calculus moves with the circuit
layer, and the modules that exist only for one proof of the PEPS approximation
manuscript stay in TNLean, consolidated, under a name that does not say
"lattice".

## Steps

Each step is one pull request per repository, or a few. A QICLean step is
followed by a TNLean pull request that moves the QICLean pin and deletes what
was replaced; TNLean keeps no copy and no compatibility alias.

Locality:

- **K0** (QICLean). `Entropy/SupportedOperatorAlgebra`: the closure lemmas of
  `IsSupportedOn`, products and commutation without a reference configuration,
  and the `*`-subalgebra `Entropy.supportedOperators`.
- **K1** (TNLean, with the pin). Delete the copies now in QICLean:
  `Entropy.IsSupportedOn.add`, `neg`, `sub` (`MPS/AreaLaw/Hastings/PartCommutators`),
  `smul` (`Hastings/ProjectorFactorizationScaling`), `conjTranspose`
  (`Hastings/PositiveFactorization`), `isSupportedOn_sum`
  (`Lattice/ZeroEntropy`); replace `σ₀` arguments by the new lemmas.
- **K2** (QICLean, then TNLean). Move the index-generic prerequisites:
  `Algebra/FinKronecker`, `ListProduct`, `ComplexSqrt`,
  `IsometryUnitaryExtension`, `UnitaryMulVecInner`, `MatrixHermitianSum`,
  `FinSumPermutation`, `PureStateTraceNorm`; `Circuit/LiebRobinson/Volterra`;
  the gate algebra `Circuit/Gates/TwoLevel`, `Givens` and the ring part of
  `Controlled`; `PartialIsometryDilation` and the amplification modules; the
  first section of `Channel/RegisterEncoding`, merged with
  `initializedBasisMatrix`, which is the same definition.
- **K3** (QICLean, then TNLean). One placement and one support notion:
  `embedOp` for site-dependent dimensions, the span-of-products description as
  a theorem, drop `σ₀` from the remaining lemmas. In TNLean,
  `QuantumCircuit.supportedOperators` becomes the QICLean subalgebra and
  `Circuit/EntropySupport` is deleted with its uses.
- **K4** (QICLean, then TNLean). Move the support, site-expectation and
  Lieb–Robinson modules to `QICLean/Locality` under one namespace; rewrite the
  `open QuantumCircuit` lines of the modules that only use locality.
- **K5** (TNLean). Replace `Lattice.localLift`, `siteLift`, `Pinned.liftLocal`,
  `regionLocalTerm`, `dependentRegionOperatorLift` and `embedLocalOperator` by
  the one placement, one directory per pull request.

Circuits:

- **C1** (QICLean). The core: `Layer`, `Circuit`, Kraus family and map, depth
  and gate count, identity and composition, trace preservation, light cone.
- **C2**. Unitary depth circuits as a restriction; `MPS/Preparation` switches;
  `BondLayer`, `circuitOp`, `IsBondCircuitOfDepth`, `IsBondCircuitOn` and the
  ring abbreviations are deleted.
- **C3**. Channel circuits and protocols as restrictions; `BondChannelLayer`,
  `OnsiteChannel`, `IsLocalChannelProtocol`, the bounded variant and
  `FixedRegisterOperation` are deleted; blueprint chapter 33 moves to the
  QICLean blueprint.
- **C4**. Measurement rounds and adaptive protocols as branching circuits;
  `MeasurementProtocol` and `IsAdaptiveChannelProtocol` are deleted.
- **C5**. Physical ports as the wire geometry; the compilation theorems
  restated between two restrictions.
- **C6**. Gate counts (`IsPairProduct`, `IsWindowProduct`, clean
  implementations) on the open-chain geometry; the bridge from depth to gate
  count.
- **C7**. Teleportation, long-range and register gates, the quantitative gate
  constructions.
- **P1**, **P2**. `Lattice/PartyCircuit` as above.

Lattice (after K4):

- **L1** (TNLean). One Hamiltonian structure on a finite set of sites with
  given supports; `ChainHamiltonian`, `DomainHamiltonian`,
  `Lattice.LocalHamiltonian`, `SquareHamiltonian` and `RectangularHamiltonian`
  become instances of it.
- **L2** (QICLean, then TNLean). Move the Hamiltonian part of `Lattice` (root
  directory and `ClusterExpansion`) beside the locality layer.
- **L3** (TNLean). Merge the single-lemma modules of `Lattice/Compression`
  along the interfaces of its proof; separate the reusable party calculus from
  the proof-specific modules, in step with P1.

C1 is validated by C2–C4: if porting a model needs a change to `Layer` or
`Circuit`, the change is made in the core before the next model is ported.

## Rules during the migration

- No new module in `TNLean/Circuit` that mentions no layer, gate or depth; put
  it in QICLean beside `Entropy.IsSupportedOn`.
- No new circuit predicate. A new model is a restriction of an existing one
  until C1 lands, and of `Circuit` afterwards.
- No new placement of a local matrix and no new support predicate.
