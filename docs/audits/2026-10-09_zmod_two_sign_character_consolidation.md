# Consolidation of the additivity of the sign character of ZMod 2

The identity `(-1) ^ (x + y).val = (-1) ^ x.val * (-1) ^ y.val` for `x y : ZMod 2`
was proved twice under the short name `neg_one_pow_val_add`: once in `ℂˣ`, in
`TNLean/Algebra/ScalarThreeCocycleCyclicExamples.lean` (with the two sides
exchanged), and once in `ℂ`, in `TNLean/MPS/MPDO/CZXGaussCircuitTuple.lean`. Both
are instances of one statement over a monoid with distributive negation, now
`ZMod.neg_one_pow_val_add` in `TNLean/Algebra/BinaryCharacterSum.lean`.

## Removed declarations and their replacement

| Removed declaration | Replacement |
|---|---|
| `TNLean.Algebra.ScalarThreeCochain.neg_one_pow_val_add` | `ZMod.neg_one_pow_val_add` at `R = ℂˣ`, used right to left |
| `MPOTensor.CZX.neg_one_pow_val_add` | `ZMod.neg_one_pow_val_add` at `R = ℂ` |

The uses in `ScalarThreeCocycleCyclicExamples`, `KleinCocycleTable`,
`KleinCocycleCompleteness`, `CZXGaussCircuitTuple` and
`CZXSecondTupleCertificate` are migrated. The blueprint entry
`thm:mpug_czx_phase_tables` cites `ZMod.neg_one_pow_val_add` in place of the CZX
name. No other use exists in `TNLean`, `blueprint`, `docs` or `scripts`.
