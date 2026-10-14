# Site-permutation product lemmas stated once

This audit records the public declarations removed when the duplicated
multiplicativity lemmas for site-permutation operators were consolidated in
`TNLean/Circuit/Channel/PortMatching.lean`. It is the audit note required by
`docs/project_conventions.md` §Style. No non-`Archive` declaration on `main` or
on an open pull request used the removed names outside the modules changed
here, no blueprint `\lean{...}` tag cites them, and no compatibility alias is
kept.

## Removed declarations

| Removed | Replacement |
|---|---|
| `MPSPreparation.permOp_mul` | `QuantumCircuit.permOp_mul` |
| `MPSPreparation.permOp_one` | `QuantumCircuit.permOp_one` |
| `MPSPreparation.isPairProduct_permOp_swap` | `QuantumCircuit.isPairProduct_permOp_swap` |

Each replacement has the same statement. The first two follow from the monoid
homomorphism `QuantumCircuit.permOpHom`; the third is moved unchanged from
`TNLean/MPS/Preparation/BlockUnitary.lean`. Modules that open `QuantumCircuit`
resolve the short names to the replacements without further change.

Private copies of the same three facts in
`TNLean/Circuit/QuantitativeSitePermutation.lean` were also removed, and
`QuantumCircuit.permOp_list_prod` is now the image of a list product under
`QuantumCircuit.permOpHom`.
