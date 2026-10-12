# Relocation of generic swap-symmetry infrastructure

Date: 2026-10-12. PR: refactor(MPS/MPU): move generic swap-symmetry
infrastructure out of the examples. Issue: #9212.

`TNLean/MPS/MPU/Examples/SwapSymmetryTransport.lean` contained declarations
that carry no swap-specific content. They are moved beside the structures they
concern. Statements and proofs are unchanged, and no deprecated aliases are kept.

## Moved declarations

| Declaration | New file | Name change |
|---|---|---|
| `MPOTensor.isInvariantUnderSymmetry_iff_of_pointwise` | `TNLean/MPS/MPU/Equivalence.lean` | none |
| `MPOTensor.daggerSymmetry` | `TNLean/MPS/MPU/Equivalence.lean` | none |
| `MPOTensor.transposeSymmetry` | `TNLean/MPS/MPU/Equivalence.lean` | none |
| `MPOTensor.conjugationSymmetry` | `TNLean/MPS/MPU/Equivalence.lean` | none |
| `MPOTensor.swapCombined_fixed_iff_leftMul` | `TNLean/Algebra/MatrixInvolutionConjugation.lean` | see below |

The involution lemma is renamed `Matrix.swapCombined_fixed_iff_leftMul`. It is a statement about square complex matrices and an
arbitrary involution, so it leaves the `MPOTensor` namespace. No equivalent
lemma was found in Mathlib, QICLean or TNLean.

No open pull request used `MPOTensor.swapCombined_fixed_iff_leftMul` when this
PR was opened. The callers in `SwapSymmetryTransport.lean` and
`SwapBlockedSymmetryTransport.lean`, the blueprint tag in
`ch28_mpu_swap_symmetry_transport.tex`, and the pattern ledger entry in
`docs/tactic_patterns.md` were updated.
