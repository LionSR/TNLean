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

The boundary collars are part of this first conclusion. The later cyclic
argument below removes them on rings of length N≥6k.
`MPS/MPU/CyclicConjugation.lean` additionally derives exact cyclic covariance
of both actual finite conjugations, reusing the existing periodic MPO
closed-trace invariance, matrix reindexing, and finite site-permutation support.
`MPS/MPU/FiniteWindowSupport.lean` identifies the actual identity-tensor
windows with the existing finite chain-window operators. It derives the
actual forward support bound for every matrix C on the complete central
2k-site interval: on N=p+6k+s sites, conjugating its placement at p+2k
produces an operator supported in [p,p+6k). No source-coordinate restriction
on C or support conclusion is a premise. The existing WindowOperatorSupport
module now identifies its chain placement with the existing general site
embedding. Existing finite support reconstruction therefore recovers a
window matrix from support membership; the actual forward bound applies
to every supported central operator, not only a separately supplied
placement matrix.
`MPS/MPU/CyclicFinitePropagation.lean` now derives an actual forward bound
at every singleton of every ring N≥6k, with uniform ring radius 4k.
The central singleton is included in its complete central 2k interval;
its actual output 6k window lies in the stated ring neighbourhood.
Finite cyclic induction transports this one-site conclusion to every
site. The existing circuit neighbourhood is reused, with its rotation
identity proved at its existing owner.

`QCA/IntervalSupport.lean` identifies arbitrary canonical finite local
inclusions with the existing general site embedding after numbering the
ambient chain. Thus no new support predicate or tensor-factor construction
is introduced. `MPS/MPU/TwoSiteCyclicInverse.lean` uses this identification
to reflect actual forward singleton commutators. On every ring N≥6k,
the actual adjoint-MPU conjugate of any local target J lies in its ring
neighbourhood of radius 4k, with no boundary collars. The only supplied
standard-form datum is the forward one; inverse standard form, inverse
locality and inverse compatibility are not premises.

Constructing a compatible inverse family and proving that the completed
forward action is surjective remain separate. Bare MPU-to-standard-form
construction and the source bond-dimension radius also remain separate,
as recorded in
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Validation: source/API/math inspection, generated imports, proof-integrity
and tactic-pattern scans, reader-facing prose, whitespace/width checks,
and Blueprint formatting. No local Lean command was run. All new entries
remain `notready` pending hosted elaboration and strict linters.
