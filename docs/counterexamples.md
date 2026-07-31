# Counterexample Registry

This file records checked or audited counterexamples that block tempting
shortcut lemmas. Add new entries here when an issue or PR discovers a
mathematical obstruction.

## MPDO and RFP

### Primitive constant trace powers need not be rank one

- Location: `TNLean/Archive/PerronFrobeniusRankOneCounterexample.lean`
- Main declaration:
  `TNLean.Archive.PerronFrobeniusRankOneCounterexample.counterexample_with_rectangular_pairing`
- Statement refuted: a primitive nonnegative matrix whose positive powers have
  constant trace must have rank one.
- Relevance: explicit rectangular factors satisfy $T=RL$ with $LR$
  idempotent, so even the full pairing identity of Appendix C.2 yields the
  constant traces but not rank one. An additional condition excluding the
  generalized zero-eigenspace is required.

### Virtual spanning does not eliminate the nilpotent sector pairing

- Location:
  `TNLean/Archive/PerronFrobeniusVirtualSpanningCounterexample.lean`
- Active physical-sector realization:
  `TNLean/MPS/MPDO/ActiveSectorSpanningCounterexample.lean`
- Main declaration:
  `TNLean.Archive.PerronFrobeniusVirtualSpanningCounterexample.injective_sourceZCL_tensor_with_nilpotent_sector_pairing`
- Strengthened declaration with scalar positive semidefinite neighboring operators:
  `MPOTensor.ActiveSectorSpanningCounterexample.virtual_spanning_does_not_force_rectangular_remainder_zero`
- Statement refuted by the strengthened active-sector realization: source ZCL,
  injectivity, exact idempotence of the physical-trace rectangular product,
  primitivity and trace normalization of the active trace matrix, full spanning
  of the virtual matrix algebra, and positive semidefiniteness of every neighboring operator
  imply that the active trace matrix is idempotent, or equivalently that the
  rectangular remainder vanishes.
- Witness: four rational pairs $l_k,r_k$ with $LQ$ idempotent and $T=QL$
  primitive, but $Q(1-LQ)L=T-T^2\ne0$. The matrices $l_k r_k$ span
  $M_2(\mathbb R)$ and occur as the diagonal slices of an injective
  source-ZCL MPO tensor.
- Boundary: the witness is not identified with the factors selected by the
  SAL inverse-map construction. It therefore isolates the missing
  SAL/provenance consequence but does not refute the full statement of
  Lemma C.5.

### BiCF does not follow from the other per-copy `HorizontalCFData` fields

- Location: `TNLean/MPS/MPDO/BiCFDerivation.lean`
- Statement refuted: blockwise injectivity, left-canonicality, nonzero weights,
  and pairwise distinct weights imply `MPSTensor.HasBiCF`.
- Witness: two scalar blocks over one physical letter with weights `1` and `2`;
  the trace-pairing cancellation cannot isolate the two blocks.

### Positive-length global PRFP data do not imply tensor-level ZCL

- Location: `TNLean/MPS/MPDO/LocalPurificationRFP.lean`
- Main declaration:
  `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL`
- Statement refuted: the global PRFP equation, MPDO positivity, and a nonzero
  physical-trace transfer imply source zero correlation length.
- Witness: the one-letter tensor with sole entry
  $Q=\left(\begin{smallmatrix}1&0&0\\0&0&1\\0&0&0\end{smallmatrix}\right)$.
  Every positive power has trace one, but $Q^2$ is not a positive scalar
  multiple of $Q$.
- Relevance: positive-length density operators do not detect a nilpotent bond
  sector. A local purification identity or a source-specified minimality or
  canonical-representative condition is therefore necessary for a
  global-to-local implication.

### An unused BNT member need not share a joint residual isometry

- Location: `TNLean/MPS/RFP/BNTResidualIsometryCounterexample.lean`
- Main declaration: `MPSTensor.cpsvCorollary312_arbitraryBNT_counterexample`
- Statement refuted: every member of an arbitrary BNT representing a
  renormalization fixed point belongs to one joint residual-isometry family.
- Witness: the bond-one tensors $A^0=1$, $A^1=0$ and
  $B^0=B^1=1/\sqrt{2}$, with BNT coefficients $1$ and $0$. Both transfer maps
  are the identity and the positive-length MPV families are linearly
  independent, but their cross inner product is $1/\sqrt{2}\ne0$.
- Proved boundary: every active listed canonical block has unit-modulus weight
  and is individually a renormalization fixed point. The joint residual-isometry
  statement for active phase-class representatives remains open at this stage;
  unused arbitrary-BNT members lie outside that corrected active statement.

## Block Separation and Canonical Form

### Weighted MPV cancellation does not imply per-block SameMPV

- Location: `TNLean/Archive/BlockSepCounterexample.lean`
- Main declaration: `MPSTensor.counterexample_block_powsum_separation`
- Statement refuted: weighted all-length MPV cancellation with distinct nonzero
  weights and injective blocks implies per-block `SameMPV`.
- Relevance: block separation needs canonical-form normalization or a stronger
  selector theorem.

### Whole-tensor SameMPV does not identify equal-norm blocks

- Location: `docs/audits/2026-04-21_issue652_gap1_blocker.md`
- Statement refuted: total `SameMPV₂` data alone determines same-norm primitive
  blocks on one side.
- Witness: two scalar bond-dimension-`1` blocks over two physical letters, with
  equal weights, whose assembled tensor agrees with itself but whose individual
  blocks already disagree at length `1`.

### Same assembled MPVs determine gauge phases, not exact block MPVs

- Location: `TNLean/MPS/FundamentalTheorem/Full/BlocksMatch.lean`
- Statement refuted: assembled `SameMPV₂` forces exact per-block `SameMPV₂`.
- Witness: replace one block by `zeta * (X * A * X^-1)` with `|zeta| = 1` and
  `zeta != 1`, and compensate the assembly weight by `muB = muA / zeta`.
- Replacement target: per-block `GaugePhaseEquiv`.

### Equal-norm blocks need not be gauge-phase equivalent

- Location: `TNLean/MPS/CanonicalForm/GaugePhaseFromOverlap.lean`
- Statement refuted: equal BNT-level norms plus the full-tensor MPV hypothesis
  force non-decaying cross-overlaps, hence gauge-phase equivalence.
- Relevance: issue #299 records the counterexample; the theorem keeps the
  required non-decay hypothesis explicit.

### Supported compression preserves positive lengths, not length zero

- Location: `TNLean/MPS/CanonicalForm/CyclicSectors/CompressionPositive.lean`
- Statement refuted: supported-projection compression gives heterogeneous
  `SameMPV₂` at all lengths.
- Witness: the length-zero coefficient changes from `trace 1 = D` to
  `trace P`, so only positive-length MPVs are preserved.

### All-zero scalar blocks must be excluded before TP gauging

- Location: `TNLean/MPS/CanonicalForm/NormalReduction/TPGauge.lean`
- Statement refuted: the blockwise Perron-Frobenius TP-gauge step has an
  unconditional arbitrary-input theorem under the current `SameMPV₂`
  interface.
- Witness: the all-zero scalar block; the theorem therefore requires a
  nonzero Kraus operator in each input block.

## Multiplicative Domain

### Corner support does not imply multiplicative-domain membership

- Location: `docs/audits/2026-04-21_issue599_corner_multiplicativeDomain_counterexample.md`
- Statement refuted: `P * X = X`, `X * P = X`, `T(P) = P`, and
  `P` in the multiplicative domain force `X` into the multiplicative domain.
- Witness: the dephasing channel on `M_2(C)` with `P = 1` and `X = E01`.
- Relevance: the fixed-point-algebra route is needed; corner support alone is
  insufficient.

## Wielandt and PEPS

### Cumulative spanning does not imply normality without aperiodicity

- Locations: `TNLean/Wielandt/SpanGrowth/CumulativeToWordSpan.lean`,
  `TNLean/Algebra/BurnsideMatrix.lean`,
  `blueprint/src/chapter/ch08_wielandt.tex`
- Statement refuted: cumulative spanning, or algebra generation, implies that a
  single word length spans the full matrix algebra.
- Witness: the tensor generated by `e12` and `e21`, whose word spans alternate
  between diagonal and off-diagonal subspaces.

### Irreducible channels need not be primitive

- Location: `TNLean/QPF/Primitive.lean`
- Statement refuted: irreducibility of a channel implies primitivity.
- Witness: an irreducible channel can have period greater than `1`; primitivity
  is a stronger peripheral-spectrum condition.

### The peripheral eigenvalue set alone does not imply irreducibility

- Location: `TNLean/Channel/Semigroup/Primitivity/MainTheorem.lean`
- Statement refuted: `peripheralEigenvalues E = {1}` implies irreducibility.
- Witness: the identity map on `M_2(C)` has peripheral eigenvalue set `{1}` in
  the current definition but is not irreducible.

### PEPS gauge uniqueness is not global-scalar uniqueness

- Locations: `TNLean/PEPS/FundamentalTheorem.lean`,
  `blueprint/src/chapter/ch23_algebraic_ft.tex`
- Statement refuted: two PEPS gauge families differ by one global scalar.
- Witness: the connected triangle, bond-dimension-`1` counterexample from
  issue #762.
- Replacement target: uniqueness modulo balanced edge scalars,
  `TNLean.PEPS.GaugeEquivModEdgeScalars`.

## Parent Hamiltonian

### Positivity is necessary in the martingale spectral step

- Location: `TNLean/MPS/ParentHamiltonian/Martingale.lean`
- Statement refuted: the quadratic-form inequality `H^2 >= gamma H` alone gives
  the norm lower bound on the orthogonal complement of `ker H`.
- Witness: `H = -Id` satisfies the inequality vacuously for positive `gamma`
  but fails the desired lower-bound conclusion.
