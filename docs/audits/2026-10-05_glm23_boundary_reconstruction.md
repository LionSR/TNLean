# GLM23 Appendix A: exact arbitrary-boundary reconstruction

Source: `Papers/2203.12563/REsubmission.tex`, v3, lines 2305–2455;
`fusiontensors`, `eq:orthoW`, `fusiontensors2`, and `eq:orthoV`.

## Construction

The preceding boundary-closedness leaf proves the common linear map from the
existential quantifiers. The new reconstruction uses that map as follows.

1. `Matrix.familyTraceAdjoint` is the sum of the bilinear trace adjoints of
   its target-block components. `familyTraceAdjoint_wordTuple` proves that it
   maps every target word tuple to the corresponding actual stacked or
   acted-on word matrix, for every positive length and arbitrary boundary.
2. `familyTraceAdjoint_map_mul` compares lengths L and 2L, where target word
   tuples span the product matrix algebra. Bilinearity extends equality from
   those tuples to every pair of block matrices. The resulting map is a
   Mathlib `NonUnitalAlgHom`; preservation of the ambient identity is absent.
3. `Matrix.exists_rankFactorization_of_idempotent` factors any idempotent P
   through its range as WV=P, VW=1. This includes non-Hermitian idempotents
   and rank zero.
4. `Matrix.exists_piMatrix_blocks` factors the image of each matrix unit.
   It derives biorthogonal multiplicity blocks and exact reconstruction,
   retaining sum W_cμ V_cμ = ρ(1). It assumes neither star preservation nor
   semisimplicity of an unrelated ambient algebra.
5. `exists_biorthogonalDecomposition_of_boundaryTransport` combines these
   facts. `BoundaryBlockFusion` and `BoundaryBlockAction` restrict the input
   bond spaces to the original source blocks. Thus each incoming pair gets
   its own finite multiplicities and exact local tensors, with no remainder.
6. `exists_positive_wordTupleSpanTop_of_isInjective` derives the simultaneous
   spanning length from individually injective, positive-dimensional blocks
   with no gauge-scalar duplicates. It uses existing nonzero scalar/Perron
   normalization and block-separation results, then removes the scalars.
   No normalization condition on the original source blocks is added.

## Source assumptions and local tensor conventions

The final source theorems are
`MPOTensor.IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective`
and
`MPOTensor.IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective`.
Their inputs are the source's length-independent existential boundary
condition, a literal unweighted block assembly, individual injectivity,
positive block dimensions, and exclusion of scalar-gauge duplicate target
blocks. They do not take a boundary linear map, a representation, simultaneous
word spanning, orthogonality, exact reconstruction, or vanishing remainder as
an input. On the action side no injectivity or separation assumption is made
on the incoming operator blocks.

The block assumptions are stated in the source at lines 314–323. The
orthogonal-representative convention is expressed here by
`BlocksNotGaugePhaseEquiv`; its scalar can be any nonzero complex number,
not merely one of modulus one. This matches unnormalized source tensors.
The source's one-site block inverse in Appendix A is replaced in the proof
by a derived simultaneous word length L, comparing lengths L and 2L. Since
the same boundary map works at every positive length, its length-one identity
still gives the exact original letters. The conclusion does not replace the
source tensors with blocked tensors.

The notation follows `BoundaryTransport`: V is the rectangular analysis map
from the incoming bond space to a target copy, and W is its synthesis map.
Thus V W = 1 and the incoming letter is the sum of W A V. In the source's
boundary-map formula B(X) = sum W X V, the source's W is our V and its V is
our W. This is an analysis/synthesis naming convention, not an adjoint or a
unitarity assertion. The source equations `fusiontensors`, `eq:orthoW`,
`fusiontensors2`, and `eq:orthoV` are all covered with this correspondence.

## Declaration and source ownership

| Layer | Owning modules | Source role |
| --- | --- | --- |
| Arbitrary-boundary quantifiers and linear selection | Existing `BoundaryClosedness`, `BoundaryTransport` | `algcond`, `eq:compatible`, Appendix A first paragraph |
| Bilinear trace dual and multiplicativity | `BoundaryRepresentation`, `BoundaryRepresentationClosedness` | `decompopen` at all positive lengths; compare L with 2L |
| Non-self-adjoint idempotents and matrix units | `Algebra/MatrixIdempotentFactorization`, `Algebra/MatrixUnitFactorization`, `Algebra/PiMatrixRepresentation` | Algebraic representation splitting used to obtain `eq:ortho` |
| Exact synthesis and incoming-block restriction | `BoundaryBiorthogonal`, `BoundaryRestriction`, `BoundaryBlockFusion`, `BoundaryBlockAction` | `fusiontensors`, `eq:orthoW`, `fusiontensors2`, `eq:orthoV` |
| Removal of the supplied simultaneous inverse | `InjectiveBlockWordSpan`, `BoundarySourceDecomposition` | Source block assumptions and Appendix A |

The new algebra modules have only Mathlib and lower algebra imports. They
use Mathlib's range, finite basis, matrix rank, and multiplicative linear-map
notions; the representation itself is a `NonUnitalAlgHom`, not a new local
representation structure. A source search of Mathlib's matrix and
representation-theory directories found no existing exact rectangular
matrix-unit factorization with arbitrary non-self-adjoint support. QICLean's
`StarSubalgebraIsotypicFactorization` concerns star-closed algebras and does
not replace the non-star construction here. No positivity, star-preservation,
or semisimplicity hypothesis is imported from that result. These elementary
algebra declarations currently belong to TNLean's tensor-network-facing
algebra layer; extraction to a general upstream library can preserve their
signatures without changing the source-facing result.

The blueprint leaf is `ch30_mpo_boundary_reconstruction.tex`. Its
source-facing decomposition theorem cites the two final signatures above.
Intermediate entries state their simultaneous-span assumption explicitly.
The leaf follows the arbitrary-boundary transport section; generated import
aggregators expose the new modules. The immutable global source inventory
retains its original baseline and is not relabelled as completed coverage.

## Scope retained

- Chain lengths are positive, as in the preceding closedness leaf. Extending
  the identities to the empty chain would additionally impose ambient
  completeness and is not asserted.
- The assembly is the literal unweighted block-diagonal tensor. Gauge
  transport can be handled separately; it is not silently folded into the
  assembly equality.
- The no-duplicate hypothesis excludes equivalence up to a nonzero scalar,
  matching the source's asymptotically orthogonal block representatives.
  Individual injectivity without block separation does not imply a
  simultaneous spanning length.
- The existence statements alone do not prove uniqueness up to multiplicity
  gauge or the subsequent F/L-symbol construction. The additive zipper
  modules below provide their separately stated consequences; they are not
  implicit consequences attributed to the original existence signatures.
- No periodic equality is promoted to equality of arbitrary-boundary words.
  No nilpotent remainder is discarded. No unitary or star structure is
  inferred from an arbitrary boundary map.

## Verification

Canonical targeted builds passed for the three new algebra modules and
the six representation/restriction/fusion/action modules with the pinned
Lean and dependency versions. The two final source modules, the additive
zipper/uniqueness modules, and expanded regressions remain pending canonical
verification. No full-repository build success is claimed for this candidate.

`TNLeanTest/PiMatrixRepresentation.lean` covers a proper non-self-adjoint
support representation, a zero representation with positive-dimensional
factors, zero-dimensional factors, an empty factor family, and kernel dependency
audits. `TNLeanTest/BoundaryReconstruction.lean` checks the unnormalized
injective-block hypotheses, empty-family simultaneous spanning, fixed incoming
fusion indices, action indices without operator injectivity, and the final
theorems' kernel axioms. These are theorem-signature and concrete algebraic
regressions; they do not claim that a blanket full-repository build passed.

## Additive zipper and uniqueness consequences

The new modules `BoundaryZipper`, `BoundaryZipperBlocked`, and
`BoundaryZipperUniqueness` are isolated from the frozen source existence
modules and remain pending canonical elaboration. Their blueprint nodes have
declaration tags but intentionally no `leanok` until that verification.

- `ofBiorthogonal` collects exact W/V data into the existing
  `CompleteZipperFusionFamily`. Analysis times synthesis is the coordinate
  identity; exact reconstruction gives both zipper equations by multiplication.
  It does not require synthesis times analysis to be the ambient identity.
- `IsBiorthogonalDecomposition.ofWords` and `.blockMPO` keep the same W/V
  matrices under physical blocking. `ofBiorthogonalBlocked` derives the
  simultaneous block inverse with the existing
  `exists_blockTensor_isMPOBlockLeftInverse`. No new star or compression
  remainder premise is introduced.
- `IsBoundaryClosed.exists_completeZipperFusionFamily` derives all pairwise
  decompositions from the source assumptions, then gives a positive L and a
  complete family for `blockTensor A L`. Its conclusion retains the exact
  unblocked decompositions and identifies the dimensions, multiplicities,
  and both packed rectangular maps of the constructed family. It does not
  claim a simultaneous one-site inverse for the original physical alphabet.
- `multiplicity_eq_of_isInjective` proves equality of independently chosen
  multiplicity functions by tracing nonempty words and using the derived
  simultaneous span. Positive target dimension is essential for recovering
  the integer coefficient from its multiple of the identity.
- `toZipperDecomposition` reuses the existing zipper structure without changing
  either map. `exists_unique_multiplicityGauge_of_isInjective` derives its
  no-gauge-related-block premise from simultaneous word separation and invokes
  the existing `ZipperDecomposition.exists_unique_multiplicityGauge`. The
  returned equalities are on the letter support, exactly as in that API.
  After multiplicities are identified, transporting their finite coordinate
  types allows this same-multiplicity comparison; no separate gauge theory
  has been introduced.

The constructed blocked family supports both existing fusion comparisons in
`CompleteZipperFusion`, `CompleteZipperFusionInverse`,
`CompleteZipperFusionPentagon`, and `CompleteZipperFusionGauge`.
Write P for the synthesis-oriented `printedFMatrix` of arXiv:1511.08090 and
Q for its `inversePrintedFMatrix`. They satisfy S_R P = S_L and
H_L = Q H_R, suppressing the final-bond identity factor. With GLM23's printed
upper indices as rows, its F-symbol in `Fsymbolsdef` is Q, not P or Pᵀ.
Thus `inversePrintedFMatrix_pentagon` gives GLM23's indexed `pentagon0F`.
The existing synthesis-basis regauge gives P′ = G_R⁻¹ P G_L and
Q′ = G_L⁻¹ Q G_R. For a GLM23 analysis-basis gauge A, use the API parameter
A⁻ᵀ; the result is Q′ = A_L Q A_R⁻¹. The exact theorem for this orientation
is `inversePrintedFMatrix_regauge`.

This dictionary follows the source's matrix directions: its unhatted fusion
W is analysis (our V), while its hatted W is synthesis (our W). The TikZ
picture names V1/W1 are different from those source matrix names. Regressions
apply both existing inverse and coherence results directly, without changing
their definitions. These are fusion associator consequences for the constructed
blocked family. General action L-symbols and the mixed pentagon are separate
remaining work. Their source index conventions must be checked independently.

## Source multiplicity laws

`BoundaryMultiplicity.lean` and its separate regression
`TNLeanTest/BoundaryMultiplicity.lean` extend the batch without modifying the
existence/zipper proof modules. All sixteen production modules in this batch
passed full Lean compilation in the remote validation run at commit
`250210d89cb53370084922a7c063346b57b610f6`. Their blueprint statements and
proofs are marked checked. Strict regression validation continues separately;
production compilation does not certify unelaborated regression examples.

The trace formula gives `IsMPOFusionAlgebra` and `IsMPOSymmetricFamily` for the
exact natural multiplicities obtained from W/V. A simultaneous word span
implies independence of periodic vectors by the bilinear trace pairing with
scalar identity tuples; the MPO statement follows by identifying vectorized
entries. State independence feeds the existing
`sum_fusion_mul_eq_sum_mul_of_isMPOSymmetricFamily`, yielding `IsNIMRep` for
the specified natural M. The integrality/existence routine is deliberately
not used to choose a potentially different multiplicity function. Operator
independence and physical matrix associativity likewise give
`sum_e N_ab^e N_ec^q = sum_f N_bc^f N_af^q`.

The final theorem
`IsBoundaryClosed.exists_isNIMRep_of_isBoundaryCompatible` derives the exact
decompositions, periodic expansions, NIM relation, and fusion associativity
from arbitrary-boundary closedness/compatibility and the original individual
operator/state block assumptions. No periodic expansion, independent length,
fusion law, or NIM equation is assumed in this source signature. These laws
hold for the original unblocked tensors. They do not provide a unit, duals,
positivity of categorical dimensions, F/L coherence, or a fusion-category
instance.
