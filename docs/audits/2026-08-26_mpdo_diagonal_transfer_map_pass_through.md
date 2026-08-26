# MPO diagonal transfer map pass-through retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. The declaration below named a single
existing construction under a second name and had no consumer anywhere outside
its own module docstring.

| Removed | Replacement |
|---|---|
| `MPOTensor.diagonalTransferMap` (`TNLean/MPS/MPDO/VerticalCF.lean`) | `Kraus.transferMap (MPOTensor.diagonalTensor M)`; the removed definition's body was exactly that expression |

## What was checked

A repository-wide search for `diagonalTransferMap` outside `.lake` returned two
hits, both inside `TNLean/MPS/MPDO/VerticalCF.lean`: the definition itself and
its bullet in the module docstring's main-definitions list. There is no
consumer in `TNLean/`, none in `Archive/`, and no blueprint `\lean{...}` tag
naming it, so no transition declaration is warranted.

The removal deletes the definition, its docstring, and the docstring bullet.
The `diagonalTensor` bullet immediately above it is retained: that definition
has consumers.

## Imports

No import becomes unused. `Kraus.transferMap` came from the same module that
still supplies `Kraus.evalWord`, which the file continues to use.
