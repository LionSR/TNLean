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
  `TNLean/MPS/MPDO/ActiveSectorSpanningCounterexample.lean` and
  `TNLean/MPS/MPDO/ActiveSectorSpanningRFP.lean`
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
- The all-cut Markov decomposition and inverse-map calculation identify this
  witness with the source-selected SAL factorization, so it proves the complete
  raw-tensor obstruction to the rank-one step. It does not refute Lemma C.5
  under all standing hypotheses: the raw tensor is not the injective normal
  tensor assumed in Case I, while its normal representative loses the paper's
  literal ZCL identity.
- Normalization boundary: explicit trace-preserving completely positive maps
  show that the raw witness $\mathcal K$, and its two-site blocking, are
  renormalization fixed points. However, its singleton BNT coefficient is
  $\sqrt5/4<1$, so it does not satisfy the source's global unit-weight
  convention. The normalized representative
  $A=(4/\sqrt5)\mathcal K$ retains SAL and the scale-invariant `IsSourceZCL`
  relation, but the physical-trace transfer of $A^{[2]}$ is
  $(16/5)\operatorname{diag}(1,0)$ and is not idempotent. Hence
  `blockTwo_normalizedTensor_not_isRFPViaTS` rules out Definition 4.1 for the
  blocked normalized tensor. This refutes the broadened implication obtained
  by replacing the paper's literal ZCL diagram with `IsSourceZCL`; it is not an
  unqualified counterexample to Theorem 4.9, because $A$ fails the literal
  diagram. Thus this four-sector witness leaves the source
  (ii)$\Rightarrow$(v) route unsettled at the boundary between global BNT
  normalization and literal physical-trace-transfer normalization.

### Coefficient absorption need not preserve normality

- Location: `TNLean/MPS/MPDO/CaseIIAbsorptionCounterexample.lean`
- Main declaration:
  `MPOTensor.CaseIIAbsorptionCounterexample.ambient_isSAL_isSimpleCanonicalForm_and_firstAbsorbed_not_isNormalTensor`
- Statement refuted: the Case-II step at CPSV16 lines 1646--1665 treats the
  tensor obtained by absorbing a common copy weight into a normal BNT
  representative as normal.
- Witness: the diagonal two-sector MPO has globally normalized weights
  $(1/\sqrt2,1)$, positive periodic operators of trace two, SAL, literal
  physical-trace ZCL, normalized fixed-representative simple canonical form,
  and biCF. The first absorbed representative nevertheless has transfer
  spectral radius $1/2$ and is not normal.
- Scope: this is proof-path drift in the printed argument. The non-Cartesian
  construction below refutes only the implication from the inherited local
  analytic properties; it has no ambient simple-biCF witness. The source-context
  factorization remains issue #6775. The source first projects into each local
  physical subspace labelled by $j$ and then applies the representative
  channels supplied by that factorization. The projector-controlled assembly
  is formalized in #6632. The
  direct sector-mixing alternative formerly tracked in #6793 is not a separate
  source obligation.

### An absorbed normal representative need not have neighboring trace factors

- Location: `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean`
- Main declaration:
  `MPOTensor.NonCartesianActiveSectorCandidate.full_lowLevel_counterexample`
- Statement refuted: injectivity, SAL, literal physical-trace idempotence, and
  being a nonzero scalar multiple of a normal tensor imply the existence of a
  physical-sector factorization with normalized rank-one neighboring traces.
- Witness: the four diagonal physical slices are the outer products determined
  by
  \[
  L=\begin{pmatrix}1&1&1&1\\1&2&-7&4\end{pmatrix},\qquad
  R=\begin{pmatrix}
  1/4&-3/100\\1/4&-1/100\\1/4&1/100\\1/4&3/100
  \end{pmatrix}.
  \]
  Here $LR=\operatorname{diag}(1,0)$, while $RL$ has rank two. The four
  slices span $M_2(\mathbb C)$ and admit positive scalar neighboring
  operators, which give injectivity and SAL. Perron normalization supplies the
  required normal representative.
- Universal obstruction: the scalar slice and two simple-spectrum slices
  force the left and right factors in every possible sector decomposition to
  be one-dimensional. The resulting neighboring trace matrix has a nonzero
  two-by-two minor and therefore cannot be of the form $(a_kb_h)_{k,h}$.
- Boundary: these low-level analytic hypotheses do not imply the
  factorization. The witness does not supply the ambient simple-biCF
  reconstruction or line-246 unit-weight convention, so the source-context
  assertion remains open in issue #6775. The explicit label-mixing channels of
  the earlier active-spanning example do not give the general construction
  used by the source.

### Unequal raw copies refute Theorem 4.9(iv)$\Rightarrow$(v)

- Location: `TNLean/MPS/MPDO/Theorem49RepeatedCopyCounterexample.lean`
- Main declaration:
  `MPOTensor.CaseIIAbsorptionCounterexample.printed_theorem49_iv_to_v_is_false`
- Statement refuted: under the printed standing simple-biCF-BNT and MPDO
  hypotheses, condition (iv) implies that the two-site-blocked tensor satisfies
  Definition 4.1.
- Witness: one scalar normal representative $A=1$, repeated with raw canonical
  weights $1$ and $1/2$. The conjunction theorem checks the exact canonical
  assembly and global unit weight, MPDO positivity, nonnilpotence of the sole
  representative, simultaneous one-letter span, representative MPDO
  positivity, the distinct-layer equation, and the full physical-sector and
  neighboring-trace factorization of condition (iv), together with MPDO
  positivity of the two-site block.
- Obstruction: the sole local matrix is $K^{00}=\operatorname{diag}(1,1/2)$.
  Definition 4.1 for $K^{[2]}$ would make its physical-trace transfer
  idempotent, hence would give $1+2^{-4}=1+2^{-2}$ after taking traces.
- Scope: this does not refute `prop2to5`, whose hypothesis is condition (ii).
  The earlier ZCL argument first forces common repeated-copy weights and
  absorbs them. The all-sector factorization and projector-controlled channel
  assembly remain missing for that viable route.

### Horizontal periodic equality does not determine vertical BNT coefficients

- Location:
  `TNLean/MPS/MPDO/VerticalCoefficientPresentationCounterexample.lean`
- Main declaration:
  `MPOTensor.VerticalCoefficientPresentationCounterexample.sameMPV₂Pos_and_no_relabelled_coefficient_equality`
- Statement refuted: two tensor-attached vertical BNT algebra clauses on MPO
  tensors with the same positive-length horizontal MPV family have equal
  structure coefficients after relabelling.
- Witness: the one-letter tensors with sole matrices
  $P=\left(\begin{smallmatrix}1&0\\0&0\end{smallmatrix}\right)$ and
  $Q=\left(\begin{smallmatrix}1&3/4\\0&0\end{smallmatrix}\right)$.
  They satisfy $Q=XPX^{-1}$ for the nonunitary horizontal gauge
  $X=\left(\begin{smallmatrix}1&-3/4\\0&1\end{smallmatrix}\right)$, and both
  generate the scalar identity at every positive length. Their normalized
  vertical representatives are $P$ and $(4/5)Q$, with multiplicity weights
  $1$ and $5/4$, so their one-label coefficients are $1$ and $(4/5)^L$.
- Scope: this refutes the bare cross-presentation assertion in issue #6395,
  even for MPDOs. It does not refute CPSV16 Proposition 4.13 or Theorem 4.14,
  which begin with a horizontally canonical tensor and choose one vertical
  presentation. The sheared tensor is not asserted to be a literal horizontal
  canonical representative. The correct comparison under explicit vertical
  transport is scale covariant; exact equality requires an additional
  normalization compatibility condition.

### BiCF does not follow from the other per-copy `HorizontalCFData` fields

- Location: `TNLean/MPS/MPDO/BiCFDerivation.lean`
- Statement refuted: blockwise injectivity, left-canonicality, nonzero weights,
  and pairwise distinct weights imply `MPSTensor.HasBiCF`.
- Witness: two scalar blocks over one physical letter with weights `1` and `2`;
  the trace-pairing cancellation cannot isolate the two blocks.

### Positive-length global PRFP data do not imply tensor-level ZCL

- Location: `TNLean/MPS/MPDO/LocalPurificationRFP.lean`
- Main declaration:
  `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isPhysicalTraceIdempotent`
- Stronger companion declaration:
  `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL`
- Statement refuted: CPSV16 Theorem 4.4's global PRFP condition implies the
  literal Definition 4.2 physical-trace idempotence equation, even with MPDO
  positivity and a nonzero physical-trace transfer.
- Witness: the one-letter tensor with sole entry
  $Q=\left(\begin{smallmatrix}1&0&0\\0&0&1\\0&0&0\end{smallmatrix}\right)$.
  Every positive power has trace one, but $Q^2\ne Q$; more strongly, $Q^2$ is
  not a positive scalar multiple of $Q$.
- Relevance: positive-length density operators do not detect a nilpotent bond
  sector. A local purification identity or a source-specified minimality or
  canonical-representative condition is therefore necessary for a
  global-to-local implication.

### MPU unitarity and simple contractions do not identify the source-v Gram contraction

- Location: `TNLean/MPS/MPU/SourceVCounterexample.lean`
- Main declaration:
  `MPOTensor.SourceVCounterexample.sourceYTensor_gram_ne_inserted`
- Statement refuted: MPU unitarity, a positive-definite source weight, and the
  exact supplied simple contractions imply that the source-$Y$ Gram
  contraction equals the rank-one-inserted double-layer contraction.
- Corrected boundary: the witness has no positive-definite fixed point for its
  normalized transfer map, so it admits no reduced canonical-form-II
  presentation with full-active-support. The example therefore refutes only
  the unrestricted source-$v$ Gram identification, not a statement under the
  reduced-CFII and full-active-support hypotheses.

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

- Location: `QICLean/QPF/Primitive.lean`
- Statement refuted: irreducibility of a channel implies primitivity.
- Witness: an irreducible channel can have period greater than `1`; primitivity
  is a stronger peripheral-spectrum condition.

### The peripheral eigenvalue set alone does not imply irreducibility

- Location: `QICLean/Channel/Semigroup/Primitivity/MainTheorem.lean`
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
