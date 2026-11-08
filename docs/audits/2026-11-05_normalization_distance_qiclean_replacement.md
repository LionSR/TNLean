# Normalization distance lemma in QICLean

Date: 2026-11-05.

This audit records that one generic normed-space lemma was removed from the
chain area-law modules. QICLean now contains it unchanged. The removal is in the
same TNLean pull request as the QICLean pin that provides the replacement, so no
commit of `main` has both declarations or neither.

## Pin 603fc408b9 (QICLean #1036 and #1030)

The lemma says that normalizing a nonzero vector at most doubles its distance
to a unit vector: `‖Φ / ‖Φ‖ - ψ‖ ≤ 2 ‖Φ - ψ‖`. It uses no Hamiltonian, lattice
or matrix product state hypothesis.

| Removed TNLean declaration | QICLean declaration |
|---|---|
| `TNLean.MPS.AreaLaw.norm_inv_norm_smul_sub_le_two_mul` | `norm_inv_norm_smul_sub_le_two_mul` (`QICLean/Analysis/UnitNormalizationDistance.lean`) |

Under the new pin, the four call sites in `TNLean.MPS.AreaLaw` and its subnamespaces
would refer ambiguously to the old name. These are `MPSApproximation.lean`,
`StripApproximation.lean`, `EntropyScaling/RenyiApproximation.lean` and
`AKLV/SequentialApproximation.lean`. They now resolve to the QICLean lemma
through the new import in `MPSApproximation.lean`.

The two-projection variant
`TNLean.MPS.AreaLaw.LocalSolution.norm_inv_norm_smul_sub_le_two_mul` has a
different statement and is kept.
