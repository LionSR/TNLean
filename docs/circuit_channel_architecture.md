# Circuit channels and physical-resource compilation

This document describes the interfaces used by the local-channel compiler and the
boundaries that new circuit and preparation results should preserve.

## Three different semantics

The following objects serve different purposes and should not be identified merely
because they can describe the same reduced channel.

1. `IsLocalChannelProtocol` permits changes of local dimension. QICLean's bounded
   variant, `QuantumCircuit.IsBoundedProtocol`, records a common bound at every
   intermediate dimension. Its depth counts native two-site channel layers.
2. QICLean's `QuantumCircuit.IsBoundedProtocol.exists_encoded` is the compiler's
   fixed-alphabet step: a protocol on the alphabet `Fin q` of the same depth, acting as
   the original protocol on the code.
3. A protocol on QICLean's `QuantumCircuit.Geometry.portRing N W` describes actual
   operations on a ring with `W` wires per site, the port at wire `0`. Only gates on two
   neighbouring ports count toward intersite depth.

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
    -> sites, blocking, encoding, physical ports, routing and dilations (QICLean Circuit)
    -> ring channel protocols and conversions (TNLean Circuit/Channel)
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

The blocking of sites, the encoding into registers, the ring with physical ports, the
routing and the unitary dilation of protocols are QICLean's
(`QICLean/Circuit/Compile/{Block, Encoding, Port, PortProtocol, Dilation,
DilationOutput}`). The TNLean port chain that preceded them has been deleted. A
generic dilation theorem must be placed at an actual site before it can be used as a
zero-depth operation.

## Reusable interfaces

- The basis inclusion `Matrix.initializedBasisMatrix` (QICLean) and its decoder
  `QuantumCircuit.decodeCircuit` handle local code subspaces. Decoding must be trace
  preserving on the entire ambient input space, not only on valid codes.
- `QuantumCircuit.Geometry.portRing` fixes wire ownership and the communication ports.
  Enlarging local memory cannot change the physical ports or move a wire to another
  site.
- `QuantumCircuit.IsUnitaryDilation` attaches finite environments to sites, prepares
  them in a basis vector and traces them out at the end.
- Dilation composition (`QuantumCircuit.IsUnitaryDilation.comp`) keeps all previous
  environments as identity factors
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

The bounded compiler (`QuantumCircuit.IsBoundedProtocol.exists_portRing`) chooses
physical dimension `d` and a bound `B ≤ d ^ k` on every positive intermediate local
dimension. One entire layer shares one forward/backward routing, costing `2*k`
intersite layers. A depth-`T` native protocol therefore has bound `2*k*T`. A
family-level constant requires fixing `d,B` before the chain length.

Preparation adapters should state their additional input/output obligations explicitly:
encoded logical input, original physical-port input, designated memory reset, and
conditions on dilation environments are different conclusions. The compiler keeps the
registers in the data wires at input and output; the transfer to the original ports is
not formalized. Source QCcc block decomposition,
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

QICLean tests correlated old environments and distinct fresh environments in its
`EnvironmentDilation` suite. Run focused package-option checks during
development, then the exact published-head root and blueprint checks. A concatenated
source probe is diagnostic assistance, not a substitute for individual module checks.

## Migration policy

`TNLean/Circuit` and `TNLean/Lattice` are being split along the layers of
[`many_body_circuit_architecture.md`](many_body_circuit_architecture.md),
redesigned around one circuit definition, and moved to QICLean. That document
gives the layers, the order of the steps and the rules for new modules in the
meantime, and replaces the earlier policy of keeping reviewed module paths in
place.
