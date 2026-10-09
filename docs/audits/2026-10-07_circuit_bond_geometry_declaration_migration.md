# Circuit layer: migration of ring declarations to bond geometries

The local-circuit layer (`TNLean/Circuit/`) was generalized from the ring of
`N` sites to an arbitrary bond geometry `bond : β → Set ι`. The ring notions
`Layer`, `IsLocalCircuitOfDepth`, `IsPreparedInDepth` and `ChannelLayer`
became `abbrev`s of the general notions at `ringBond`, so every lemma stated
in their old namespaces now lives in the namespace of the general structure.
Dot notation (`L.op`, `h.mul`, `L.toChannelLayer`) resolves through the
`abbrev` unchanged; only fully qualified references change. All non-`Archive`
uses were migrated, and no blueprint `\lean{...}` tag cites a removed name.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `QuantumCircuit.bond` | `QuantumCircuit.ringBond` (`TNLean/Circuit/Geometry.lean`); `bond` is now the name of the geometry parameter |
| `QuantumCircuit.bond_subset_neighbourhood` | `QuantumCircuit.ringBond_subset_neighbourhood`; for a general geometry, `bond_subset_bondNeighbourhood` with `bondNeighbourhood_ringBond` |
| `QuantumCircuit.Layer.{gate_commute, partialOp, op, partialOp_mem_unitary, partialOp_mem_supportedOperators, op_mem_unitary, conj_op_mem_supportedOperators, adjoint, adjoint_partialOp, adjoint_op}` | `QuantumCircuit.BondLayer.*` of the same name (`LocalCircuit.lean`) |
| `QuantumCircuit.Layer.{IsIn, IsIn.mono, op_mem_supportedOperators, disjoint_bonds, empty, empty_op, empty_isIn, single, single_op, single_isIn, union, union_op, union_isIn}` | `QuantumCircuit.BondLayer.*` of the same name (`Composition.lean`) |
| `QuantumCircuit.Layer.{toChannelLayer, toChannelLayer_map}` | `QuantumCircuit.BondLayer.{toChannelLayer, toChannelLayer_map}` (`Channel/Layer.lean`) |
| `QuantumCircuit.IsLocalCircuitOfDepth.{mem_unitary, star, mul}` | `QuantumCircuit.IsBondCircuitOfDepth.{mem_unitary, star, mul}` |
| `QuantumCircuit.IsCircuitOn` and `QuantumCircuit.IsCircuitOn.{mem_unitary, mem_supportedOperators, mono, mono_set, mul, one, single}` | `QuantumCircuit.IsBondCircuitOn` and `QuantumCircuit.IsBondCircuitOn.*` of the same name |
| `QuantumCircuit.IsCircuitOn.isLocalCircuitOfDepth` | `QuantumCircuit.IsBondCircuitOn.isBondCircuitOfDepth` |
| `QuantumCircuit.ChannelLayer.{gateMap, gateMap_commute, gateMap_isKrausCPTP, map, map_isKrausCPTP, gateDual, gateDual_commute, partialDual, partialDual_eq_filter_mul, partialDual_isHeisenbergLocal, partialDual_mem_supportedOperators, dual, trace_map_mul}` | `QuantumCircuit.BondChannelLayer.*` of the same name |
| `Matrix.trace_finKronecker` | `Matrix.trace_rectKronecker` |
| `QuantumCircuit.trace_finKronecker_mul_mul` | `QuantumCircuit.trace_rectKronecker_mul_mul` |

The ring-distance statements (`conj_circuitOp_mem_supportedOperators`,
`expect_mul_eq_of_isPreparedInDepth`, `ChannelLayer.dual_mem_supportedOperators`,
`ChannelLayer.dual_mul`, `channelCircuitDual_mem_supportedOperators`,
`channelCircuitDual_mul`) keep their names and are now derived from the
light-cone statements of a general bond geometry through
`lightCone_ringBond`.
