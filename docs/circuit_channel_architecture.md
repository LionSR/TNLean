# Circuit channels and physical-resource compilation

TNLean no longer contains a channel-circuit layer: local channel protocols, their encodings
into bounded registers, the physical-port compiler and its unitary dilations are QICLean's
(`QICLean/Circuit/Model`, `QICLean/Circuit/Compile`). This document records the QICLean
interfaces that TNLean consumers and the blueprint chapter `ch33_local_quantum_circuits_*`
use, and the boundaries that new circuit and preparation results should preserve.

## Three different semantics

The following objects serve different purposes and should not be identified merely
because they can describe the same reduced channel.

1. `QuantumCircuit.IsProtocol Γ T Φ` (and `IsConversion`) permits changes of local
   dimension. The bounded variant `QuantumCircuit.IsBoundedProtocol Γ B T Φ` records a
   common bound `B` on every basis along the protocol. On `Geometry.ring N` its depth counts
   native two-site layers.
2. `QuantumCircuit.Circuit.exists_seq_encoded` and `IsBoundedProtocol.exists_seq_encoded`
   carry a bounded protocol to a sequence of layers on one fixed alphabet, with all-operator
   intertwining `Φ' ∘ 𝓔_e = 𝓔_f ∘ Φ` and the same number of counted layers.
3. A physical-port protocol is a map with a unitary dilation
   (`QuantumCircuit.IsUnitaryDilation`) on `QuantumCircuit.Geometry.portRing N (2k+1)`:
   one fixed-dimensional port per site, the cells of all wires of a site at cost `0`, and
   only gates on two ports counted.

A theorem relating these semantics must supply the actual channel identity and its
resource bound. A coordinate equivalence alone is not a free physical gate.

History-dependent measurement trees are `QuantumCircuit.IsAdaptiveProtocol`. Extending the
deterministic channel compiler to that layer requires explicit classical-control and
source-block witnesses; the quantum-depth index does not supply them.

## QICLean interfaces

- Codes: `Matrix.basisInclusion`, `KrausFamily.embed`, `KrausFamily.decode` (decoding with a
  basis-vector fallback, trace preserving on the whole ambient space), `KrausFamily.encode`,
  and the sitewise circuits `QuantumCircuit.encodeCircuit` and `decodeCircuit`.
- Layers: `QuantumCircuit.Layer.exists_encoded` encodes a layer on its own cells.
- Physical ports: `QuantumCircuit.portDataEmbedding`, `portWireEmbedding`,
  `Layer.exists_portRing_sites` (operations on whole sites are free),
  `Layer.exists_portRing` (one matching costs `2k`), `IsBoundedProtocol.exists_portRing`,
  `exists_portRing_recode`, `IsBoundedProtocol.exists_portRing_of_code` and
  `IsBoundedProtocol.exists_portRing_unit_product_approx`.
- Dilations: `prepareCircuit`, `traceCircuit`, `IsUnitaryDilation.comp`,
  `Layer.isUnitaryDilation`, `Circuit.isUnitaryDilation`, `IsProtocol.isUnitaryDilation`,
  and the pure-output estimate `Circuit.exists_unit_product_approx`.

The physical-port statements intertwine codes that fix every wire of a site. TNLean once
also stated the compiled channel on an arbitrary state of the port and scratch wires carried
along as a reference; that statement is not carried by QICLean's construction and is not
available.

## Compiler and preparation extension points

The bounded compiler chooses physical dimension `d` and a bound `B ≤ d ^ k` on every
intermediate local dimension; for `d ≥ 2` one may take `k = Nat.clog d B`. One entire
matching shares one forward/backward routing, costing `2*k` intersite layers, so a depth-`T`
native protocol has bound `2*k*T`. A family-level constant requires fixing `d,B` before the
chain length.

Preparation adapters should state their additional input/output obligations explicitly:
encoded logical input, original physical-port input, designated memory reset, and
conditions on dilation environments are different conclusions. The original-port
statement (`exists_portRing_of_code` with the port codes) supplies the designated
data/scratch reset. Source QCcc block decomposition, within-block control restrictions and
pure-output ancilla requirements need their own witnesses; they do not follow from
reduced-channel equality alone.

## Migration policy

`TNLean/Circuit` and the top level of `TNLean/Lattice` have moved to QICLean,
split along the layers of
[`many_body_circuit_architecture.md`](many_body_circuit_architecture.md). The
subdirectories `Lattice/PartyCircuit`, `Lattice/Sheet` and `Lattice/Compression`
remain; that document gives the layers, the order of the remaining steps and the
rules for new modules in the meantime.
