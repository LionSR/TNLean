# Actual finite MPU inverse support

Source: arXiv:1703.09188, supplied StandardForm/SF, lines 603–622,
and Appendix eq:appendix-1, lines 2292–2306.

`QCA/SingletonGeneration.lean` derives finite single-site algebra generation
from the existing disjoint-union tensor generation. The existing finite
relative commutant then characterizes retained support using only outside
single-site commutators. Empty-region scalars are handled explicitly.

`QCA/FiniteInverseLocality.lean` reflects forward commutation through an
actual finite star-automorphism. It derives exact inverse support from
forward disjointness, without an inverse local family, inverse compatibility,
or a quasi-local automorphism premise.

`MPS/MPU/TwoSiteFiniteInverse.lean` applies this to the actual finite MPU
unitary. The actual forward standard-form window identity supplies every
commutator needed away from the retained region. For target `[b,b+L)` in
ambient chain `[a,a+N)`, the derived inverse support is the ambient intersection
with `[b−4k,b+L+4k) ∪ [a,a+2k) ∪ [a+N−4k,a+N)`. The proof converts the actual
finite-chain window equality to a finite inclusion-range witness through
faithfulness of the existing algebraic-local inclusion.

The boundary collars are part of the conclusion. No uniform periodic inverse
propagation, inverse-family compatibility, surjectivity of the completed
forward action, or completion of the source QCA statement is claimed.
Periodic relocation of boundary singleton windows remains necessary for that
step. Bare MPU-to-standard-form construction and the source bond-dimension
radius remain separate, as recorded in
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Validation: source/API/math inspection, generated imports, proof-integrity
and tactic-pattern scans, reader-facing prose, whitespace/width checks,
and Blueprint formatting. No local Lean command was run. All new entries
remain `notready` pending hosted elaboration and strict linters.
