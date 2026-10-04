# Standard-basis boundary vectors and matrices

Issue: [#8169](https://github.com/LionSR/TNLean/issues/8169).

The ancilla vector `MPSPreparation.basisVecZero hD` is now
`Pi.single ⟨0, hD⟩ 1`. The row and column boundary matrices are
`Matrix.vecMulVec` of this vector with their respective boundary vector.
The positivity witness is supplied from existing bond-dimension bounds or
`NeZero` instances; no sequential-generation conclusion is weakened.

Coordinate and conjugation proofs use `single_one_dotProduct`,
`Matrix.mulVec_single_one`, `Pi.single_star`, `Matrix.mul_vecMulVec`, and
`Matrix.vecMulVec_mulVec`. The supported-vector pairing in
`SequentialFactorization` uses the same standard-basis calculation instead
of another finite-sum expansion.

The consumer check covers all seven affected modules in `MPS/Preparation`.
Unlike the issue's original snapshot, all boundary declarations are cited
in `ch31_sequential_generation_ancilla.tex`; their names and tags remain.
No declarations are removed, and no replacement compatibility layer is added.
