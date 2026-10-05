# Circuit channels and physical-resource compilation

This document describes the interfaces used by the local-channel compiler and the
boundaries that new circuit and preparation results should preserve.

## Three different semantics

The following objects serve different purposes and should not be identified merely
because they can describe the same reduced channel.

1. `IsLocalChannelProtocol` permits changes of local dimension. The bounded variant,
   `IsDimensionBoundedLocalChannelProtocol`, records a common bound at every intermediate
   dimension. Its depth counts native two-site channel layers.
2. `FixedRegisterOperation` is the compiler's fixed-alphabet intermediate representation.
   It separates onsite channel operations from native two-site layers. The compiler
   preserves the number of two-site layers before physical routing is introduced.
3. `IsPhysicalPortUnitary` and `IsPhysicalPortProtocol` describe actual operations on a
   layout with one fixed-dimensional communication port at each site. Memory wires
   have explicit owners. Only gates on the physical ports count toward intersite depth.

A theorem relating these semantics must supply the actual channel identity and its
resource bound. A coordinate equivalence alone is not a free physical gate.

History-dependent measurement trees remain in `Circuit/Measurement/AdaptiveConversion`.
They carry outcome-dependent continuation semantics. Extending this deterministic
channel compiler to that layer requires explicit classical-control and source-block
witnesses; the existing quantum-depth index does not supply them.

## Dependency direction and ownership

The intended direction is:

```
finite-index matrix/channel algebra (QICLean)
    -> register placement, configuration coordinates and environments (Circuit)
site embeddings, supports and wire permutations (Circuit)
    -> spatial layouts, physical ports and routing (Circuit)
register algebra + spatial geometry
    -> local dilations and physical-resource compilation (Circuit)
    -> preparation-specific states, approximations and source theorems (MPS/Preparation)
```

`Circuit` must not import `MPS`. A preparation construction should provide
its state/tensor hypotheses to a reusable circuit theorem, rather than copy routing,
channel composition or partial-trace proofs into the preparation directory.

Generic results about arbitrary finite matrix index types belong in QICLean. In
particular, basis-state environment initialization, Choi-bounded local unitary
dilation, and the interchange of a fresh operation with a deferred partial trace
have no spatial assumptions. They live in `QICLean.Channel.EnvironmentEmbedding`,
`QICLean.Channel.EnvironmentDilation` and
`QICLean.Channel.DeferredEnvironmentTrace`. The established `Matrix.fixedEnvEmbedding`
name is shared with the Markov-dilation client. TNLean imports these interfaces rather
than maintaining another copy of the finite-dimensional channel proofs.

TNLean owns the facts that refer to wires, sites, supports, ports, native protocols,
and counted communication depth. A generic dilation theorem must be placed at an
actual site before it can be used as a zero-depth operation.

## Reusable interfaces

- `registerEncoding` and its completed decoder handle local code subspaces. Decoding
  must be trace preserving on the entire ambient input space, not only on valid codes.
- `registerChannelLift` places a channel independently of its Kraus representation.
  Its composition and Kraus identities are the shared entry point for all placements.
- `registerConfigurationSplit` and complementary-coordinate naturality own the
  selected-register/complement decomposition. Appended-wire and routing-coordinate
  specializations should derive their operator formulas from this interface rather
  than reprove `AgreeOff` calculations.
- `PhysicalPortLayout` records wire ownership and communication ports.
  `PhysicalPortEmbedding` preserves both. Enlarging local memory cannot change the
  physical ports or move an old wire to another site.
- `RegisterEnvironment` owns nonspatial appended-wire initialization and final trace;
  it depends on register placement and QIC channel algebra, not spatial layouts.
- Fresh-environment composition keeps all previous environments as identity factors
  until the final trace. Its identities must allow correlations between the system
  and earlier environments; an intermediate product-state assumption is invalid.

Keep definitions near their algebraic laws and introduce a new module for a coherent
interface or proof layer. Avoid a module per small lemma, numbered sequels, duplicated
predicates, and broad umbrella imports. Public names should describe mathematical
roles rather than the order in which a proof was developed.

## Compiler and preparation extension points

A new native operation first needs a fixed-register realization with an all-operator
intertwining identity. Its physical realization then needs an explicit support or
port certificate and a depth calculation. These two proofs have different assumptions
and should remain separately reusable.

The bounded compiler chooses physical dimension `d` and a bound `B` on every positive
intermediate local dimension, then uses `k = Nat.clog d B`. One entire matching shares
one forward/backward routing, costing `2*k` intersite layers. A depth-`T` native
protocol therefore has bound `2*k*T`. A family-level constant requires fixing `d,B`
before the chain length.

Preparation adapters should state their additional input/output obligations explicitly:
encoded logical input, original physical-port input, designated memory reset, and
conditions on dilation environments are different conclusions. The original-port
compiler supplies the designated data/scratch reset. Source QCcc block decomposition,
within-block control restrictions and pure-output ancilla requirements need their own
witnesses; they do not follow from reduced-channel equality alone.

## Regression expectations

Changes to placement, encoding, layout or compiler interfaces should retain:

- all-operator identities, including off-diagonal matrix units;
- arbitrary external-reference preservation;
- non-power local dimensions and genuine intermediate dimension changes;
- empty environments/registers where the definitions permit them;
- physical-port ownership, unchanged original ports, and disjoint parallel routing;
- capstone audits reporting only standard axioms, with strict Lean/linter checks.

The CI suites are `PhysicalPortSimulation`, `PhysicalProtocolCompilation`,
`PhysicalPortIO` and `PhysicalPortDilation`. QICLean separately tests correlated old
environments and distinct fresh environments in its `EnvironmentDilation` suite. Run focused package-option checks during
development, then the exact published-head root and blueprint checks. A concatenated
source probe is diagnostic assistance, not a substitute for individual module checks.

## Migration policy

Do not rename already-reviewed modules solely to improve the directory tree. Group new
work by the interfaces above, and perform any later path migration as a deliberate
compatibility change: retain import shims where useful, regenerate aggregators, update
blueprint links, and test downstream preparation clients. Namespace/API stability and
small dependency closures matter more than a visually tidy directory listing.
