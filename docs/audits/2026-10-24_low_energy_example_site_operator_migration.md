# Migration of the site operator of the low-energy example

`TNLean/Lattice/LowEnergyCommutatorExample.lean`, the example of non-commuting
low-energy terms in Hastings' Appendix B, defined its own operator `X` at a site
`i` of the chain, `siteOp i X`, together with its linearity and its diagonal
case. That operator has the same entries as `QuantumCircuit.siteOp` of
`TNLean/Circuit/Gates/Controlled.lean`, which already carried
`siteOp_mul` and `siteOp_diagonal`. The local copy is removed, and the example
uses the circuit operator.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `TNLean.Lattice.LowEnergyExample.siteOp` | `QuantumCircuit.siteOp` |
| `TNLean.Lattice.LowEnergyExample.siteOp_apply` | `QuantumCircuit.siteOp_apply` (new, same entrywise form) |
| `TNLean.Lattice.LowEnergyExample.siteOp_add` | `QuantumCircuit.siteOp_add` (new) |
| `TNLean.Lattice.LowEnergyExample.siteOp_neg` | `QuantumCircuit.siteOp_neg` (new) |
| `TNLean.Lattice.LowEnergyExample.siteOp_sub` | `QuantumCircuit.siteOp_sub` (new) |
| `TNLean.Lattice.LowEnergyExample.siteOp_zero` | none needed: it had no use; `QuantumCircuit.siteOp_apply` with `Matrix.zero_apply` gives it |

`TNLean.Lattice.LowEnergyExample.siteOp_spinZ` is kept, now derived from
`QuantumCircuit.siteOp_diagonal` through the new
`TNLean.Lattice.LowEnergyExample.spinZ_eq_diagonal`. No blueprint `\lean{...}`
tag cites any removed name, and no other use exists in `TNLean`, `TNLeanTest`,
`blueprint`, `docs` or `scripts`.
