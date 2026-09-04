# Twisted-dimer predicate renames (issue #7622)

Issue #7622 renamed the two remaining public predicates in the twisted-dimer example to follow
the `Is`-prefix convention. Their definitions and every theorem statement using them are otherwise
unchanged. No compatibility aliases are retained because TNLean does not promise a stable external
Lean API.

## Exact mapping

| Old declaration | New declaration |
|---|---|
| `MPOTensor.TwistedDimer.gate` | `MPOTensor.TwistedDimer.IsBondMatchedPair` |
| `MPOTensor.TwistedDimer.decidableGate` | `MPOTensor.TwistedDimer.decidableIsBondMatchedPair` |
| `MPOTensor.TwistedDimer.sameChannel` | `MPOTensor.TwistedDimer.IsSameChannel` |
| `MPOTensor.TwistedDimer.decidableSameChannel` | `MPOTensor.TwistedDimer.decidableIsSameChannel` |

All non-`Archive` call sites and the affected Blueprint declaration tag were migrated to the new
names. The glossary entry for the twisted-dimer predicate family now records the renamed
predicates together with the four sibling predicates that already followed the convention.
