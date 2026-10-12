# Generic symmetry infrastructure moved out of `MPS/MPU/Examples` (2026-10-12)

Issue #9212 asked that the generic pieces of
`TNLean/MPS/MPU/Examples/SwapSymmetryTransport.lean` live beside the notions
they are about. The three concrete symmetries `daggerSymmetry`,
`transposeSymmetry` and `conjugationSymmetry`, and the pointwise criterion
`isInvariantUnderSymmetry_iff_of_pointwise`, now follow the definition of
`IsInvariantUnderSymmetry` in `TNLean/MPS/MPU/Equivalence.lean`, under their
existing names. The matrix identity that the swap example used is stated once
for a general involution in the new module
`TNLean/Algebra/InvolutionFixedEquation.lean`.

## Removed declaration and its replacement

| Removed declaration | Replacement |
|---|---|
| `Matrix.swapCombined_fixed_iff_leftMul` (`MPS/MPU/Examples/SwapSymmetryTransport.lean`) | `Matrix.involution_conj_eq_iff_leftMul` (`Algebra/InvolutionFixedEquation.lean`): the same statement for any involution `Q` over any semiring, taking `Q * Q = 1` as a hypothesis |

The four uses, two in
`TNLean/MPS/MPU/Examples/SwapSymmetryTransport.lean` with `chainSwap_mul_self`
and two in `TNLean/MPS/MPU/Examples/SwapBlockedSymmetryTransport.lean` with
`blocked_chainSwap_mul_self`, and the blueprint tag in
`blueprint/src/chapter/ch28_mpu_swap_symmetry_transport.tex` now cite the
general theorem. The `docs/tactic_patterns.md` entry for the pointwise
criterion points at its new module. No other use of the old name exists in
`TNLean`, `blueprint`, `docs` or `scripts`.
