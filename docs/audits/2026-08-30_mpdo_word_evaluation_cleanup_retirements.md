# MPDO word-evaluation cleanup retirements

This audit records the removal of three zero-consumer public lemmas in PR
#7456 under the repository-local retirement rule of
`docs/project_conventions.md` §Style.  Each lemma was either a one-step
consequence of a surviving result or a pass-through used once at its point of
definition.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.RescalingStableLengthDependentRFP.retainedBlock_isNormal` | `MPOTensor.RescalingStableLengthDependentRFP.retainedBlock_isInjective.isNormal`, used directly in `retainedBlock_isNormalTensor` |
| `MPOTensor.NeighboringTraceObstructionAmbientBlocks.embeddedObstruction_isInjective` | `MPOTensor.isInjective_toMPSTensor_changePhysicalBasis_iff physicalInclusion physicalInclusion_isometry tensor`, applied directly to `tensor_isInjective` if this fact is needed |
| `MPOTensor.NeighboringTraceObstructionAmbientBlocks.terminalBlock_physTraceTransfer_idempotent` | `terminalBlock_physTraceTransfer_eq_one`, followed by `one_mul` if idempotence is needed |

## Clearance

Exact-name searches found no non-`Archive` Lean consumer and no Blueprint
`\lean{...}` tag for any of the three removed names.  The only use of
`retainedBlock_isNormal` was the immediately following construction of the
CPSV normal tensor; that call now uses
`retainedBlock_isInjective.isNormal` directly.  The other two lemmas had no
consumer.

The replacements preserve the same mathematics.  Physical-basis injectivity
transport is the theorem from which `embeddedObstruction_isInjective` was
proved verbatim.  The equality
`terminalBlock_physTraceTransfer_eq_one` is strictly stronger than
idempotence.  No compatibility alias is retained, since TNLean does not
promise a stable public Lean interface and all retirement conditions are
satisfied.

The exact PR head was checked by a root `lake build`, so importers were tested
after the declarations were removed.  The linter-bearing changed-module
builds, Blueprint synchronization, and both declaration checks also passed.
