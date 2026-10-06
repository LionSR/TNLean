# MPS parent-Hamiltonian completion audit

This audit compares the seven “Done when” requirements of [issue #190](https://github.com/LionSR/TNLean/issues/190) with the mathematical statements present on 2026-10-02. It also examines the compact multiblock requirement of [issue #8467](https://github.com/LionSR/TNLean/issues/8467). The assessment concerns theorem hypotheses, conclusions, and their sources. Successful elaboration or a positive spectral bound under additional assumptions would not by itself establish a source theorem. No conclusion below asserts that a public issue has been closed.

For a tensor $A$, write $G_N(A)$ for its open-boundary matrix product space, $H_{N,R}(A)$ for its canonical periodic parent Hamiltonian, and $H^{\mathrm{open}}_{N,R}(A)$ for its open parent Hamiltonian. A simultaneous injectivity length $S$ means that the length-$S$ word tuples of the distinct normal blocks span the product of their matrix algebras. The proved interaction ranges considered below satisfy $R\geq S+1$. This is a restriction of those theorems, not a convention that narrows the source definition of a parent interaction.

## The seven completion requirements

### 1. Nachtergaele’s abstract index thresholds (#7478)

The source is `References/cond-mat_9410110/main.tex:1030–1094,1119–1130,1195–1259`. Conditions C1–C3 have lower endpoints, whereas the printed proof estimates all martingale differences. The printed unrestricted conclusion is false: the one-site chain with its leftmost interaction reduced by a factor of two satisfies the source-threshold conditions but violates the stated lower bound.

The exact transcription and counterexample are `FrustrationFree.UnrestrictedNachtergaeleEstimate` and `FrustrationFree.not_unrestrictedNachtergaeleEstimate` in [NachtergaeleLowerEndpoint.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/NachtergaeleLowerEndpoint.lean). The corrected statements are `energy_lower_bound_of_nachtergaele_c1_c3_threshold` and `energy_lower_bound_of_nachtergaele_c1_c3_of_martingaleDifference_below_eq_zero` in [NachtergaeleFullRangeEstimate.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/NachtergaeleFullRangeEstimate.lean). The first controls the martingale mass above the threshold; the second recovers the printed coefficient when the omitted differences annihilate the vector. The full-range norm corollary uses the abstract finite-dimensional spectral theorem.

The mathematical obstruction is settled by a false-source correction, rather than a proof of the false unrestricted claim. The repair and its MPS applicability are recorded in [the lower-endpoint note](../paper-gaps/nachtergaele96_theorem_2_1_lower_endpoint.tex). In the compatible open MPS specialization, the early local terms vanish and the boundary C3 product is zero, so the full coefficient applies.

### 2. The block-injective periodic gap (#7676)

The source is `Papers/2011.12127/TN-Review-main.tex:2114–2129,2183–2187`, with the degenerate martingale argument in Nachtergaele’s Section 6. The claim that every available gap theorem assumes a single normalized primitive tensor is obsolete.

For arbitrary original blocks of positive dimensions and nonzero weights, `exists_parentHamiltonianES_toTensorFromBlocks_uniform_gap_of_wordTupleSpanTop` in [BlockGapAtSimultaneousInjectivity.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/BlockGapAtSimultaneousInjectivity.lean:41) proves, for each $R\geq S+1$, a positive periodic gap uniform over every chain length. Normalization and block inequivalence are derived inside the proof. [BlockDiagonalGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/BlockDiagonalGap.lean:83) also retains the prescribed PGVWC07 bound $R\geq3(r-1)(L_0+1)+1$ from a common individual injectivity length.

[CanonicalGapAtSimultaneousInjectivity.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/CanonicalGapAtSimultaneousInjectivity.lean) transfers this result to an original canonical tensor, including repeated copies. [ParentInteractionGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/ParentInteractionGap.lean) handles every fixed positive parent interaction. The two theorems in [CanonicalGapAtBoundedRange.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/CanonicalGapAtBoundedRange.lean:40) remove the supplied simultaneous-span assumption at the sufficient range $R\geq3D^5$.

Thus the range-qualified block-injective assertion is proved, including general positive interactions. The source definition at lines 1996–1999 permits arbitrary interaction length, and its gap theorem at lines 2183–2187 has no range qualifier. Comparable ground-space and uniqueness statements explicitly attach length conditions. Consequently the range hypothesis cannot silently be supplied as a convention. These signatures do not establish the original unrestricted gap assertion. [The interaction-range note](../paper-gaps/cpgsv21_block_parent_interaction_range.tex) resolves the comparison from a chosen range $2p$ to the prescribed PGVWC07 range and to $S+1$; its resolved status does not settle arbitrary shorter ranges.

### 3. Normalization-free normal tensors (#7677)

The sources are `References/cond-mat_9410110/main.tex:1394–1435` and PGVWC07, Theorem 4, `Papers/quant-ph_0608197/MPSarchive.tex:742–767`.

`exists_isPrimitiveMPS_gauge_of_isNormal` in [PrimitiveGaugeExistence.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveGaugeExistence.lean:116) takes normality of the original tensor and produces a nonzero rescaling, an invertible virtual gauge, a normalized primitive representative, and a positive-definite invariant density. Its conclusion preserves every local ground space, parent interaction, and chain ground space. `exists_parentHamiltonianES_uniform_gap_of_isNormal` in the same file proves a gap for the original tensor, uniform over every periodic length, at a constructed admissible range. No trace-preserving gauge is a hypothesis on the original tensor.

The requirement is proved. The stronger compact single-normal-block result is in [CompactNormalParentGap.lean](../../TNLean/MPS/ParentHamiltonian/CompactNormalParentGap.lean:327), at every prescribed range $R\geq D^4+1$. The open-chain counterparts in [NormalOpenGapAtWielandtRange.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/NormalOpenGapAtWielandtRange.lean) give the gap at every such range for all $N\geq R$, including the shortest admissible chain.

### 4. The FNW coefficient and C3 threshold (#6367)

The sources are FNW, Lemmas 5.2, 5.3, and 6.2, and Nachtergaele’s Section 6, equation `boundAm` (`References/cond-mat_9410110/main.tex:2398–2412`). The proved weighted coefficient is $a(m)(1+a(m))/a_-(m)$. [FNWProjectorDefect.lean](../../TNLean/MPS/ParentHamiltonian/FNWProjectorDefect.lean) and [FNWGeometricDefect.lean](../../TNLean/MPS/ParentHamiltonian/FNWGeometricDefect.lean) give its rational geometric form $c\lambda^m(1+c\lambda^m)/(1-c\lambda^m)$. [C3Threshold.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/C3Threshold.lean:189) uses this coefficient to choose the martingale threshold. The estimate determining the threshold no longer comes from the deleted inverse-Gram reconstruction.

[FNWTransferEigenvalueRate.lean](../../TNLean/MPS/ParentHamiltonian/FNWTransferEigenvalueRate.lean:58) proves that the source’s nonunit transfer-eigenvalue condition implies the required weighted remainder spectral-radius condition, without diagonalizability. The prescribed-rate assertion is therefore established.

The fixed choice $c=k^2$ at every prescribed admissible rate from the injectivity threshold is false. `FNWDimensionConstant.exists_dimensionFour_counterexample` in [Counterexample.lean](../../TNLean/MPS/ParentHamiltonian/FNWDimensionConstant/Counterexample.lean:41) supplies an injective primitive tensor with $k=4$, rate $1/1000$, and overlap-two physical defect at least $1/16$, exceeding the printed coefficient. [FNWEventualPrefactor.lean](../../TNLean/MPS/ParentHamiltonian/FNWEventualPrefactor.lean) proves the corrected eventual statement for every prescribed positive prefactor. The onset may depend on the tensor, rate, and prefactor.

The weighted estimate, rate prescription, and corrected prefactor assertion are proved. Identifying the false fixed-threshold bound with $k^2$ is not a remaining theorem to prove.

### 5. Deletion of the divisible-length cyclic reconstruction (#7679)

Nachtergaele’s Theorem 2.1(ii) rescales compatible open intervals (`References/cond-mat_9410110/main.tex:1264–1276`). It does not establish the former cyclic sparse-sum comparison.

The declarations `exists_parentHamiltonianES_gap_eighth_mul` and `blockTensor_parentHamiltonianES_conj_le`, their modules, and their blueprint entries are absent. The replacement is the compatible open-chain estimate followed by the exact cyclic active-block identity and [FiniteRangeKnabeGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/FiniteRangeKnabeGap.lean). The resulting periodic gap has no divisibility restriction. The finite-range coefficient is identified as a separate derivation in [its note](../paper-gaps/knabe88_finite_range_coefficient.tex), rather than attributed to Nachtergaele.

The deletion requirement is fulfilled. The surviving explicit $1/8$ theorem for a blocked tensor is a different result and does not restore the removed original-site reconstruction.

### 6. The block-injective ground space at the printed length data (#7680)

The source is `Papers/2011.12127/TN-Review-main.tex:2078–2094,2114–2129`. The issue’s demand for the kernel equality at every $L\leq N$ independently of injectivity is false. For GHZ, the simultaneous injectivity length is $S=1$, but $G_1=\mathbb C^2$ makes the range-one Hamiltonian zero; its kernel is not the two-dimensional periodic block span. The source’s inversion and regrowth argument uses $S+1$ sites.

[BlockGroundSpaceAtInjectivityLength.lean](../../TNLean/MPS/ParentHamiltonian/BlockGroundSpaceAtInjectivityLength.lean:53) proves the exact periodic block span for every $S+1\leq L\leq N$, including $N=L=S+1$, without normalization on the original blocks. [CanonicalBlockGroundSpaceAtInjectivityLength.lean](../../TNLean/MPS/ParentHamiltonian/CanonicalBlockGroundSpaceAtInjectivityLength.lean:48) includes repeated canonical copies and arbitrary positive terms with the prescribed local kernels.

[CanonicalBoundedRangeGroundSpace.lean](../../TNLean/MPS/ParentHamiltonian/CanonicalBoundedRangeGroundSpace.lean:70) further supplies $0<R\leq3D^5$ and the exact original canonical kernel for all $R\leq L\leq N$. The strict span estimate gives $S+1\leq3D^5$, so the statement includes $N=L=3D^5$. The earlier extra blocking, unitality, and complementary-length requirements are absent from these statements.

The range-qualified ground-space theorem is proved. The issue’s unrestricted interaction-length requirement is refuted and is not a possible strengthening; it cannot be counted as literally proved. The interpretation and proof are documented in [the ground-space note](../paper-gaps/cpgsv21_block_diagonal_parent_ground_space.tex:190).

### 7. Chapter 13 and the martingale note

Chapter 13 states the corrected source-threshold estimate, its repair, the printed counterexample, the weighted FNW numerator, the eigenvalue-rate implication, the prefactor counterexample, and the eventual correction. Its block-gap and ground-space entries retain their actual interaction-range conditions. It also includes the automatic $3D^5$ gap, strict open Knabe intervals, and compact multiblock conclusions.

[The martingale note](../paper-gaps/cpgsv21_martingale_overlap.tex) retains the `false-source` classification for the prefactor assertion and now records status `resolved`. Its concluding block-gap paragraph states the prescribed-$S$ theorem and both canonical dimension-bound theorems, with their exact quantifiers and a reference to the interaction-range note. The false lower-endpoint assertion remains separately corrected. Neither chapter nor note claims the false unrestricted ground-space conclusion. Their range-qualified gap theorems must also remain distinguished from the source’s unrestricted gap assertion.

This is a mathematical consistency assessment. Global declaration checking and publication validation are separate checks; they are not evidence that an unrestricted source assertion follows from a restricted theorem.

## Compact multiblock families (#8467)

The source is `Papers/1010.3732/paper_v3.tex:2475–2580`. Appendix A proves a gap uniform in the path parameter and chain length for a fixed normal block structure, including positive interactions that are not projections. Its argument uses transfer spectral ratios, inter-block overlaps, and a continuous finite-window gap.

`exists_uniform_parentHamiltonianES_toTensorFromBlocks_gap_of_compact_all_lengths` in [CompactBlockParentGap.lean](../../TNLean/MPS/ParentHamiltonian/CompactBlockParentGap.lean:130) takes fixed positive block dimensions, continuous block tensors, nonzero weights, a common simultaneous injectivity length $S>0$, $R\geq S+1$, and a compact parameter set. It concludes one positive gap uniform in the parameter and every ring $N\geq R$. The weights need not be continuous because they do not affect the local spaces.

`exists_uniform_block_parentHamiltonianES_gap_of_compact_isNormalTensor` derives a common $S$ from pairwise inequivalent normal-form blocks and proves the same conclusion at every $R\geq3\max(\sum_jD_j,1)^5$. `exists_uniform_block_parentInteraction_gap_of_compact` in [CompactParentInteractionGap.lean](../../TNLean/MPS/ParentHamiltonian/CompactParentInteractionGap.lean) covers continuous positive interactions with exactly the corresponding local kernels. The comparison constant is uniform on the compact set.

The proof derives a strict open interval at each parameter from [BlockOpenGapAtSimultaneousInjectivity.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/BlockOpenGapAtSimultaneousInjectivity.lean:96). Continuous joint local-space projections preserve the interval inequality nearby. Knabe’s inequality and a finite subcover give a common gap for long rings. Continuous periodic-kernel projections and finite-dimensional positivity handle the finitely many short rings. Those continuity statements are proved in [BlockGroundSpaceContinuity.lean](../../TNLean/MPS/ParentHamiltonian/BlockGroundSpaceContinuity.lean) and [BlockPeriodicGroundSpaceContinuity.lean](../../TNLean/MPS/ParentHamiltonian/BlockPeriodicGroundSpaceContinuity.lean).

The requested finite-window inter-block overlap continuity is explicitly proved by `continuous_norm_groundSpaceES_overlap_family`. No declaration proving continuity of an ordered per-block second transfer eigenvalue was found in the relevant development. It must not be listed as proved. Such continuity is unnecessary for the alternative proof: compactness is applied to strict finite-window inequalities, rather than to uniform transfer decay constants. Thus #8467’s multiblock uniform-gap conclusion and its positive-interaction extension are established; its specified transfer-eigenvalue auxiliary step and its particular Nachtergaele coefficient are not formalized by this argument.

For the source’s already-blocked isometric deformation, simultaneous injectivity is preserved by the invertible physical deformation, so $S=1$ and $R=2$ satisfy the general theorem’s assumptions. [PhysicalActionWordTupleSpan.lean](../../TNLean/MPS/ParentHamiltonian/PhysicalActionWordTupleSpan.lean) proves this preservation, including rectangular changes with a left inverse. [PositivePhysicalDeformationGap.lean](../../TNLean/MPS/ParentHamiltonian/PositivePhysicalDeformationGap.lean) constructs $Q_\gamma=\gamma Q+(1-\gamma)I$ from a supplied positive factor and proves the uniform gap for both canonical projections and the exact source interactions $h_\gamma=(Q_\gamma^{-1})^{\otimes2}h_0(Q_\gamma^{-1})^{\otimes2}$.

[LeftPolar.lean](../../TNLean/MPS/ParentHamiltonian/LeftPolar.lean) and [IsometricDeformation.lean](../../TNLean/MPS/ParentHamiltonian/IsometricDeformation.lean) now derive this factor from the original block tensor. For the joint physical matrix $P_{i,(j,a,b)}=A_i^j(a,b)$, they construct $Q=(PP^\dagger)^{1/2}+I-E$ and $W$, prove $Q>0$, $QW=P$, $WW^\dagger=E$, and $\operatorname{ran}E=\operatorname{ran}P$. The identity extension outside the physical support keeps the original physical dimension. The constructed path has endpoints $W$ and $A$, is continuous, preserves every simultaneous word span, and has uniform canonical and positive-interaction gaps for every ring $N\geq2$. Pairwise inequivalent normal blocks admit the required initial blocking at a positive length $L$ with $L+1\leq3\max(\sum_jD_j,1)^5$; this corollary assumes no supplied polar factor or simultaneous injectivity length. Thus the earlier absence of the joint left polar construction is removed.

[CompactOpenParentGap.lean](../../TNLean/MPS/ParentHamiltonian/CompactOpenParentGap.lean)
now proves a positive gap uniform in both the compact tensor parameter and
every open-chain length \(N\geq R\), with \(R\geq S+1\). Its normal-block
consequence derives a common sufficient range from the dimensions.
[CompactOpenParentInteractionGap.lean](../../TNLean/MPS/ParentHamiltonian/CompactOpenParentInteractionGap.lean)
extends the bound to continuous positive local interactions with the same
kernels, allowing both the tensors and interactions to vary.

The proof uses
[OpenFiniteRangeKnabeGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/OpenFiniteRangeKnabeGap.lean).
If all open volumes \(R\leq W\leq m+R-1\) have a gap \(\gamma\) and
\((R-1)^2<m\gamma\), then every open chain has gap at least
\((m\gamma-(R-1)^2)/(m-R+1)\). The local interactions are indexed on a
longer cyclic group, with zero interactions in the added indices; the physical
Hilbert space remains the original open chain. Each nonzero window is an
embedded open interval, including intervals truncated at either endpoint.
This is a derivation from the abstract finite-range inequality, rather than
an implication from a periodic-chain gap.

[OpenGapContinuity.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/OpenGapContinuity.lean)
preserves a strict gap on these finitely many intervals near one parameter.
At that parameter the pointwise all-length gap permits a window with strict
Knabe threshold. The finite-size criterion gives a positive gap for all
lengths throughout one neighborhood; a finite subcover treats the compact
set.
[OpenIsometricDeformationGap.lean](../../TNLean/MPS/ParentHamiltonian/OpenIsometricDeformationGap.lean)
applies both compact open-chain results to the positive affine path and the
constructed joint polar path. The canonical two-site parent and the source's
inverse-conjugated positive interaction have gaps uniform in the path
parameter and every open length at least two. For pairwise inequivalent
normal blocks, each conclusion holds after a positive initial blocking with
\(L+1\leq3\max(\sum_jD_j,1)^5\). The bounded simultaneous blocking lemma
is shared by the periodic and open consequences.
 The earlier bounded-volume assertion in
[CompactOpenIntervalGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/CompactOpenIntervalGap.lean)
remains a separate finite-window result, while the new compact theorem has
no finite upper bound on the chain length.

## Prescribed open-chain gaps at long interaction ranges

[PrescribedOpenGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/PrescribedOpenGap.lean)
proves a sharper quantitative consequence. For pairwise inequivalent normal
blocks of positive dimensions, nonzero block weights, and every
\(0<\eta<1\), all sufficiently large \(p\) give canonical open-chain gap
at least \(1-\eta\) for every \(N\geq2p\). Primitive normalization is
derived inside the normal-block consequence; it is not imposed on the
original blocks. The interaction range increases with the requested bound.

Write \(N=pM+q\), where \(0\leq q<p\).
[SparseGroupedOpenGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/SparseGroupedOpenGap.lean)
samples the range-\(2p\) interactions at starts \(0,p,\ldots,p(M-2)\).
The full grouped energy estimate applies to this sampled sum with coefficient
\(\kappa_p=(1-\epsilon_p\sqrt2)^2\). For \(q>0\), one terminal
range-\(2p\) interaction has a different start from every sampled term;
their sum is therefore bounded by the full Hamiltonian with coefficient one.
The two ground spaces overlap on \(2p-q\geq p\) sites.
[TwoGroundProjectionGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/TwoGroundProjectionGap.lean)
combines these estimates with coefficient \(\kappa_p(1-\epsilon_p)\).
Since the projection error tends to zero, this coefficient tends to one.
This removes both the divisibility condition and the fixed loss in the
earlier two-interval estimate. It is derived from Nachtergaele's grouped
martingale and three-interval estimates, rather than asserted as the exact
printed coefficient of a separate source theorem.

## Symmetry of the polar deformation

[IsometricDeformationCovariance.lean](../../TNLean/MPS/ParentHamiltonian/IsometricDeformationCovariance.lean)
proves the polar-decomposition implication in SPC11,
`Papers/1010.3732/paper_v3.tex:645–676`. Supplied physical and virtual
unitaries satisfying \(UP=PX\) force \([U,PP^\dagger]=0\), commutation
with the support projection and the identity-extended positive factor,
and \(UW=WX\). The same covariance holds throughout the affine path.
The identity extension outside the physical support is included explicitly.

To infer parent-Hamiltonian symmetry, the original MPS boundary space must
also be invariant under the on-site action. An arbitrary unitary on the
joint matrix-coordinate space need not preserve virtual MPS contractions.
[IsometricDeformationSymmetry.lean](../../TNLean/MPS/ParentHamiltonian/IsometricDeformationSymmetry.lean)
proves this conditional implication for both open and periodic parent
Hamiltonians and for the source's positive interaction deformation.
[InjectiveIsometricDeformationSymmetry.lean](../../TNLean/MPS/ParentHamiltonian/InjectiveIsometricDeformationSymmetry.lean)
derives the needed virtual unitary and polar commutation for a single
injective block with either trace-preserving or unital canonical normalization
and exact vector symmetry; the parent-symmetry module derives the corresponding Hamiltonian
consequences without supplied virtual covariance. The trace-preserving case
matches the source's partial-trace convention in the recorded coordinates;
the unital case uses its dual orientation.
The complete source assertion requires deriving the appropriate virtual
unitary and boundary-space invariance from state symmetry after a standard
gauge choice. This distinction and the remaining multiblock step are recorded
in [the symmetry note](../paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex).

## The infinite-volume gap and the ground-state classification

Nachtergaele's Theorem 1.2 also bounds the infinite-volume commutator energy
in each pure GVBS ground state. Its final source argument is at
`References/cond-mat_9410110/main.tex:2649–2675`.
[GroundExpectationGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/GroundExpectationGap.lean)
proves the exact finite-volume estimate

\[
\langle\psi,X^*[H,X]\psi\rangle
\geq\gamma\bigl(\|X\psi\|^2-\|P_{\ker H}X\psi\|^2\bigr)
\]

for any zero-energy vector \(\psi\). Its limiting theorem allows varying
Hilbert spaces and gives the desired bound when the full ground-projection
term tends to zero. That decay is an explicit additional hypothesis of the
intermediate theorem. Scalar centering removes only the component along
\(\psi\), and does not remove other finite-volume ground components.
For one-dimensional finite-volume kernels, the same module proves that
the projection term is exactly the squared absolute value of the observable
mean. Its rank-one limiting corollary therefore needs only convergence of
that mean to zero, together with the norm and energy expectations.
Finite-volume uniqueness remains an explicit hypothesis.
For a single normalized primitive tensor with a positive-definite invariant
matrix, [LocalObservableInsertion.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableInsertion.lean)
identifies the exact inserted transfer expression for an interior observable
and proves its virtual Gram limit.
[GroundSpaceCompressionNorm.lean](../../TNLean/MPS/ParentHamiltonian/GroundSpaceCompressionNorm.lean)
transfers that limit through the eventually bounded inverse Gram operators.
[BoundaryObservableCompression.lean](../../TNLean/MPS/ParentHamiltonian/BoundaryObservableCompression.lean)
then proves scalar compression on the entire finite-chain boundary space,
centered ground-projection decay, and local expectation convergence on unit
ground vectors. No finite open-chain uniqueness is assumed.
[LocalObservableExpectation.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableExpectation.lean)
proves positivity, normalization, complex linearity, and consistency under
adjoining identity sites. These statements do not require primitivity;
left consistency uses trace preservation, and right consistency uses the
invariant matrix. [PrimitiveBoundaryCommutatorGap.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveBoundaryCommutatorGap.lean)
combines the norm limit and full projection decay for a centered observable.
Its limiting energy is an explicit hypothesis of that intermediate statement.
[BulkObservableCommutator.lean](../../TNLean/MPS/ParentHamiltonian/BulkObservableCommutator.lean)
proves that the finite-range commutator energy operator is the inclusion of
one fixed local observable. [PrimitiveLocalCommutatorGap.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveLocalCommutatorGap.lean)
derives its expectation limit and proves the centered local inequality with
one positive constant for every observable at each range $R\geq D^4+1$.
This final primitive consequence has no supplied norm, projection, energy
limit, or boundary-vector hypothesis. [LocalObservableState.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableState.lean)
proves the finite local functional has operator norm one and preserves
adjoints. [IntervalObservableCoordinates.lean](../../TNLean/MPS/ParentHamiltonian/IntervalObservableCoordinates.lean)
identifies the finite integer-interval inclusion with this observable placement.
[PrimitiveLocalParentInteractionGap.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveLocalParentInteractionGap.lean)
extends the primitive inequality to every positive local interaction with
the prescribed MPS kernel, at the same sufficient range. Comparison with
the canonical interaction supplies the gap and preserves the open-chain kernel.
[LocalObservableRegionExpectation.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableRegionExpectation.lean)
proves independence of the containing interval and compatibility on arbitrary
finite regions.
[CompatibleLocalState.lean](../../TNLean/QCA/CompatibleLocalState.lean)
extends compatible contractive positive local functionals continuously to
the quasi-local algebra.
[LocalObservableQuasiLocalState.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableQuasiLocalState.lean)
applies this construction to the tensor expectations and proves normalization,
positivity, and norm one.
[LocalObservableTranslationInvariance.lean](../../TNLean/MPS/ParentHamiltonian/LocalObservableTranslationInvariance.lean)
proves translation invariance on finite regions and on the completed algebra.
[QuasiLocalPrimitiveGap.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalPrimitiveGap.lean)
states the positive-parent commutator bound in this concrete quasi-local state,
uniformly over interval positions and centered observables.
[BoundaryCrossObservableCompression.lean](../../TNLean/MPS/ParentHamiltonian/BoundaryCrossObservableCompression.lean)
proves that compression into an inequivalent sector vanishes by distant-prefix
locality. The right free interval need not grow for this cross estimate.
[GroundSpaceSectorCompressionDecay.lean](../../TNLean/MPS/ParentHamiltonian/GroundSpaceSectorCompressionDecay.lean)
assembles vanishing column compressions for finitely many asymptotically
orthogonal subspaces.
[BlockBoundaryObservableCompression.lean](../../TNLean/MPS/ParentHamiltonian/BlockBoundaryObservableCompression.lean)
therefore proves centered compression into the full multiblock ground space.
[MultiblockLocalCommutatorGap.lean](../../TNLean/MPS/ParentHamiltonian/MultiblockLocalCommutatorGap.lean)
combines this decay with the norm and energy limits. At simultaneous
injectivity length $S>0$ and range $R\geq S+1$, it derives one positive
constant for every primitive sector and every centered observable, including
arbitrary positive parent interactions.
[QuasiLocalMultiblockGap.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalMultiblockGap.lean)
expresses this common bound in the concrete completed sector states.
[LocalParentExpectation.lean](../../TNLean/MPS/ParentHamiltonian/LocalParentExpectation.lean)
proves their exact local support and zero expectation for parent interactions.
[PrimitiveQuasiLocalUniqueness.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveQuasiLocalUniqueness.lean)
proves that any normalized positive quasi-local state supported in every
finite-interval primitive MPS space equals the constructed state, without
assuming translation invariance. The support-compression identity follows
from Cauchy--Schwarz, and the scalar compression limit identifies all local
expectations. [PrimitiveQuasiLocalPurity.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveQuasiLocalPurity.lean)
then proves that the constructed state is pure among all states: every
constituent of a convex decomposition inherits the support constraints.
[QuasiLocalCommutatorLocality.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalCommutatorLocality.lean)
identifies the literal finite-volume quasi-local energy with the fixed patch
once both interaction margins are present.
[LocalCommutatorExpectation.lean](../../TNLean/MPS/ParentHamiltonian/LocalCommutatorExpectation.lean)
proves that its expectation is real and nonnegative in each sector, without
injectivity or a gap hypothesis.
[QuasiLocalMultiblockLimitGap.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalMultiblockLimitGap.lean)
therefore proves the literal infinite-volume commutator inequality, with one
positive constant for all constructed pure sectors at $R\geq S+1$.
[QuasiLocalGroundStateSupport.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalGroundStateSupport.lean)
also derives eventual joint MPS support from the source's eventual
finite-chain kernel hypothesis and zero expectation of every local term.
No invariance of the competing state, parent-kernel identity at the original
range, or comparison of that range with an injectivity length is assumed.
[MultiblockQuasiLocalFace.lean](../../TNLean/MPS/ParentHamiltonian/MultiblockQuasiLocalFace.lean)
derives a finite convex decomposition from eventual joint support.
[MultiblockQuasiLocalGroundStates.lean](../../TNLean/MPS/ParentHamiltonian/MultiblockQuasiLocalGroundStates.lean)
therefore classifies the whole zero-energy face, and its pure states,
for the given inequivalent primitive family. Purity is taken among all
quasi-local states.
[EventualKernelOpenGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/EventualKernelOpenGap.lean)
also proves a uniform finite-chain gap at every length for an arbitrary
positive interaction under the same eventual kernel hypothesis.
A sufficiently long finite-window comparison supplies the large-volume gap;
a finite minimum handles the shorter volumes. The original range need only
be positive. These statements concern the given primitive sector family;
the bridge from more general periodic GVBS presentations remains separate.
[QuasiLocalGroundStateGap.lean](../../TNLean/MPS/ParentHamiltonian/QuasiLocalGroundStateGap.lean)
now retains the same constant for both the all-length finite-chain gap and
the literal commutator inequality in every pure zero-energy state.
Its original-family corollary derives the primitive normalization from
simultaneous word span, without relating the original range to that length.
[PrimitiveGroundStateInteractionExistence.lean](../../TNLean/MPS/ParentHamiltonian/PrimitiveGroundStateInteractionExistence.lean)
constructs a positive canonical interaction realizing the classified face,
with exact finite-chain kernels at every length at least its derived range.
The precise distinction is recorded in
[the ground-projection note](../paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex).

## The review’s unrestricted interaction-range assertion

The seven original requirements cannot all be counted as proved by reinterpreting the range scope. The source definition permits arbitrary positive interaction length, and the source’s blanket gap claim supplies no restriction to $R\geq S+1$. The new counterexample formally refutes that unrestricted shorter-range assertion. The corrected endpoint and prefactor results likewise settle false-source questions by corrections, rather than by proving the printed false claims. The original issue must be assessed with those distinctions explicit.

There is a fully verified counterexample refuting the unrestricted gap assertion. Consider three scalar blocks over a qubit alphabet,

$$
A^0=(1,0),\qquad A^1=(0,1),\qquad A^+=(2^{-1/2},2^{-1/2}),
$$

with every weight equal to one, and let $B=A^0\oplus A^1\oplus A^+$. All blocks have positive bond dimension, are normal with transfer map the identity on $\mathbb C$, and are pairwise inequivalent under virtual similarity and phase. Thus $B$ is a nondegenerate canonical tensor of bond dimension three. Its simultaneous span is full at $S=2$: the words $00,01,11$ give independent tuples $(1,0,1/2)$, $(0,0,1/2)$, $(0,1,1/2)$.

At interaction range $R=2$, its exact local space is

$$
G_2(B)=\operatorname{span}\{|00\rangle,|11\rangle,|++\rangle\}
       =\operatorname{Sym}^2(\mathbb C^2).
$$

The canonical parent term is therefore $h=|\psi^-\rangle\langle\psi^-|=(I-F)/2$, where $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ and $F$ exchanges the two sites. This is a nonzero positive parent interaction with exactly the source-defined kernel. The periodic Hamiltonian is the spin-$1/2$ ferromagnetic Heisenberg chain, shifted to ground energy zero.

For $N\geq3$, let $|j\rangle$ denote the configuration with one spin in state $1$ at site $j$ and all others in state $0$. Direct evaluation gives

$$
H_N|j\rangle=|j\rangle-\tfrac12|j-1\rangle-\tfrac12|j+1\rangle.
$$

Hence the nonzero Fourier vector $v_N=\sum_{j=0}^{N-1}e^{2\pi i j/N}|j\rangle$ has eigenvalue $\varepsilon_N=1-\cos(2\pi/N)>0$. Positivity and self-adjointness imply $v_N\perp\ker H_N$. Since $\varepsilon_N\to0$, no positive gap constant can be uniform in $N$. This calculation uses the exact parent kernel, rather than an uncle Hamiltonian or a larger local kernel. It also shows why ground-space failure alone was insufficient to diagnose the gap: the positive excitation energies themselves approach zero.

This counterexample does not refute Nachtergaele's Theorem 1.2.
The ferromagnetic finite-chain kernel is larger than the three prescribed
sector spaces at long lengths, so its eventual kernel hypothesis fails.
The source explicitly distinguishes that hypothesis from equality of the
infinite-volume ground-state faces at
`References/cond-mat_9410110/main.tex:933–955`.

The earlier primary literature does not supply the unrestricted assertion. [Fernández-González, Schuch, Wolf, Cirac, and Pérez-García, Section 2.3, Definition 3 and Remark 1](https://arxiv.org/html/1210.6613) first assumes a jointly injective blocked tensor in its parent construction, and explains the sufficient interaction length $k+1$ when blocking $k$ sites gives injectivity. The comparison in PGVWC07 also uses its injectivity condition. These statements do not remove the missing range hypothesis in the review’s broader definition.

The counterexample is recorded explicitly in [the short-range parent-gap note](../paper-gaps/cpgsv21_short_range_parent_gap.tex), whose status is `false-source/resolved`. [ShortRangeHeisenbergTensor.lean](../../TNLean/MPS/ParentHamiltonian/ShortRangeHeisenbergTensor.lean) proves the direct source basis-of-normal-tensors certificate, joint injectivity at length two and its failure at length one, and the exact singlet parent projection. [ShortRangeHeisenbergGap.lean](../../TNLean/MPS/ParentHamiltonian/ShortRangeHeisenbergGap.lean) proves the nonzero Fourier eigenvector identity and `not_exists_eventual_uniform_gap_shortRangeHeisenbergTensor_two`, ruling out a positive uniform gap even after excluding any finite set of ring lengths. The two supporting algebra modules prove the one-magnon exchange recurrence and the positive eigenvalue limit. Its identification with the Heisenberg model is consistent with the primary spectral analysis of [Koma and Nachtergaele](https://arxiv.org/abs/cond-mat/9512120), whose isotropic limit is gapless. The verified conclusion is a tensor with three normalized normal blocks and a fixed positive range $R=2$ for which no $\gamma>0$ can satisfy $\gamma\|v\|\leq\|H_{N,R}(B)v\|$ for all sufficiently large $N$ and all $v\perp\ker H_{N,R}(B)$. The main counterexample, source BNT certificate, compact deformation gaps, and arbitrary sufficient-range normal gaps use only `propext`, `Classical.choice`, and `Quot.sound`.

The open-chain strengthening is now proved: [BlockOpenGapAllLengths.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/BlockOpenGapAllLengths.lean) gives a positive gap at every admissible $R\geq S+1$, uniformly for every $N\geq R$. [NormalBlockOpenGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/NormalBlockOpenGap.lean) derives a sufficient range from the dimensions, and [CanonicalOpenGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/CanonicalOpenGap.lean) includes multiplicities and ambient reconstruction. These statements remain separate from the unrestricted source issue, which is formally refuted. The seven requirements are accounted for by the proved sufficient-range theorems and the explicit corrections or counterexamples to the false source statements; the distinction from literal proofs of the printed assertions is retained throughout.

## Verification

The all-length open-chain proof uses three supporting results.
[IntervalGapTransport.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/IntervalGapTransport.lean)
preserves finite-interval gaps after adjoining free sites.
[IntervalKernelTransport.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/IntervalKernelTransport.lean)
identifies the terminal kernel with the reassociated tail boundary space.
[OverlappingIntervalGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/OverlappingIntervalGap.lean)
combines a prefix gap and a terminal gap: a common lower bound $\kappa$ and
projection defect at most $1/2$ give the full-chain gap $\kappa/16$.
[PrimitiveBlockOpenGapAllLengths.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/PrimitiveBlockOpenGapAllLengths.lean)
uses the overlap estimate to remove divisibility of the chain length.
Finite-interval comparison and a finite minimum complete the prescribed-range
statement in the original tensor. The compact varying-tensor extension adds
zero padding, the open finite-size criterion, finite-window continuity, and
compact positive-interaction comparison. The combined source check for all
eighteen supporting and consequence sources, including the refactored
isometric-deformation source, passed with `relaxedAutoImplicit=false`,
`maxSynthPendingDepth=3`, and the standard Mathlib linter set. All 69 audited
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
the source check has no warnings or unfinished proofs. The corresponding source bodies were checked against their recorded
hashes. The later combined check covers 62 source bodies and 304 public
axiom queries, including the sharp near-one open-chain estimate, both
canonical symmetry orientations, full primitive boundary compression,
local expectation and interval properties, compatible-state completion,
translation invariance, exact local support, full multiblock projection decay,
and the positive-parent quasi-local commutator inequalities in one sector
and throughout the block family, together with rectangular mixed insertion
identities and decay, literal commutator locality and limits, primitive supported-state
uniqueness and purity, joint sector decomposition, finite convex-weight
compactness, and the implication from local zero energy to joint support.
It passed with the same strict options,
no warnings, no unfinished proofs, and only the three axioms above.
The 62 source bodies at that snapshot agreed with their recorded hashes.
Subsequent declarations have passed focused strict checks; their final combined
source audit is recorded below when completed. The blueprint
source synchronization at that snapshot passed for all 15,273 referenced declarations.
Changed-declaration coverage also passed for the audited sources, with no
missing definition, theorem, or lemma entries.
The generated import check passed for 66 aggregators and 2080 production
modules at the earlier aggregate-build snapshot. The subsequent regeneration
covers 2098 production modules; verification of the latest generated files
and new aggregate build is recorded separately as it completes. The refreshed parent-Hamiltonian and quasi-local aggregate modules
passed the prescribed build under the shared repository lock. The
extended finite-range coefficient note compiled without unresolved citations,
and all six rendered pages were inspected. The prescribed package build reached the new modules and found a missing
complex-order scope in the symmetry module. The scope has been added, and
the actual module passed a separate strict Lean check. A fresh prescribed
package build succeeded under the shared repository lock, and
`leanblueprint checkdecls` then passed. A further focused wrapper build of
the completed local-state, interval, and commutator modules also passed,
as did focused builds of the compatible-state extension, finite-region and
quasi-local tensor states, translation invariance, and the primitive
quasi-local commutator bound. Focused prescribed builds of full multiblock
projection decay, both multiblock commutator modules, and exact local support
also passed. The current global compiled-declaration check reports eight missing names,
all in the concurrent PEPS development. No parent-Hamiltonian or quasi-local
declaration is missing. A focused compiled-declaration check passed for 1961 distinct references
from the 41 parent-Hamiltonian chapters and the exact-source audit.
Changed-declaration blueprint coverage also passed for the 52-source snapshot.

Before the all-length strengthening, the parent-Hamiltonian modules and the `TNLean.MPS` import module passed the prescribed Lake build. The final axiom checks for the short-range counterexample, its source BNT certificate, the positive affine deformation gap, and the arbitrary sufficient-range normal gaps report only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof or additional axiom was introduced.

Declaration checking passed for all 637 references in the four relevant BNT and parent-Hamiltonian chapters, and for all 217 references in the five associated paper-gap notes. Blueprint source synchronization and web generation passed. The new counterexample note compiled with resolved citations and equation references, and its four rendered pages were inspected.

An earlier full repository build encountered an unrelated error in `TNLean/PEPS/RegularRegionConnectivity.lean:145`. Global blueprint declaration checking likewise reported 60 missing declarations, all in the concurrent PEPS development. These failures do not occur in the parent-Hamiltonian modules or the focused declaration lists, but the complete repository checks are not reported as passing.

The latest combined verification covers 96 complete module bodies and five
changed declarations from four lower modules, checked as exact declaration
slices in separate audit namespaces. It contains 492 public kernel queries.
Every query passed with only `propext`, `Classical.choice`, and `Quot.sound`;
the strict source check exited successfully without warnings or unfinished
proofs. All 100 whole-file hashes remained unchanged during the check.
The focused lower checks cover block-space inclusion, two active-window
coordinate identities, the nonwrapping suffix-start equivalence, and the
generic counting lemma for positive open-window sums. Their remaining
consumers use the compiled canonical modules. Blueprint source synchronization
and changed-declaration coverage passed for all 15,433 references. The current
66 generated import modules cover 2132 production modules, and their check passed.
Focused prescribed package builds of the literal multiblock gap, joint support,
and full ground-state classification passed. The corresponding parent-Hamiltonian
and QCA aggregate build passed with 9915 jobs. That aggregate preceded the
new blocking results described below; their current aggregate verification is
recorded separately when completed.
The updated ground-projection note compiled with resolved references and no
layout warnings. All four rendered pages were inspected; paragraph breaks
were adjusted to avoid isolated opening lines at page boundaries.

## Periodic tensors and physical blocking

For a periodic tensor, blocking by its period now derives a nonempty family
of primitive sectors with faithful invariant matrices. Isometric compression
preserves every finite boundary space, and selecting gauge-phase representatives
removes repeated sectors without changing the joint spaces. No invariant matrix,
sector inequivalence, or primitive presentation is supplied as an extra hypothesis.
A finite weighted family of periodic tensors likewise admits an exact primitive
presentation after blocking by a common positive multiple of the periods.

Blocking identifies the entire normalized positive state spaces and preserves
purity. Support on all original intervals is equivalent to support on all aligned
intervals, and hence to full interval support on the blocked chain. For any tensor,
the eventual open-chain kernel identity for a positive interaction of positive
range is equivalent to its zero-energy states satisfying all MPS support
conditions. These facts give both the entire zero-energy face and its pure states
for a periodic tensor or a finite weighted periodic family: the face is the convex
hull of the transported primitive sector states, and its pure states are exactly
those states. Competing states need not be translation invariant.

The finite Hamiltonian comparison is also explicit. Let the blocked interaction
be the regrouped original open Hamiltonian on $KL$ sites. For $N\geq K$ and
$R+L\leq KL+1$, decoding the configurations gives

$$
H_h(NL)\ \leq\ H_{\widehat h}(N)\ \leq\ (KL+1-R)H_h(NL).
$$

The kernels consequently coincide. The eventual original MPS kernel condition
therefore becomes the eventual blocked MPS kernel condition. A blocked norm gap
transfers with divisor $KL+1-R$. A positive minimum with the finitely many smaller
divisible volumes gives a uniform gap for every length $NL$, with its actual
kernel. In particular a periodic tensor has a uniform gap at every
period-divisible length. This does not yet prove the gap at other residue lengths;
their correlated residual boundary spaces must also be controlled.

Configuration reindexing, arbitrary original local observable transport, the
positive commutator comparison, and the foregoing classification and divisible
gap results passed independent strict Lean checks. Their kernel queries report
only `propext`, `Classical.choice`, and `Quot.sound`, with no unfinished proof or
additional axiom. The final separation conversion is shared by a proved helper,
following the rule of three; the two classification statements and the divisible
gap statement passed their strict checks again after that proof-only refactoring.
The independent mathematical review confirmed the counting constant, complete
kernel complements, and finite minima at short divisible volumes.

An exact decomposition at residual lengths is also proved: the space at
$NL+r$ is the sum of rectangular boundary-map ranges over the compressed
sectors. Each map retains the original $r$-site tail inside its contraction.
The isometries and both intertwining identities are derived from periodicity;
the residual tail is not replaced by arbitrary independent configurations.
This identity holds also at zero lengths. It is a support-space result;
the quantitative overlapping-projection estimate is still separate.

Prescribed package builds passed for interval and state transport (3132 jobs),
joint support and the periodic blocked spaces (9783 jobs), the single-periodic
ground-state classification (9805 jobs), common-period family presentations
(9296 jobs), and the blocked Hamiltonian comparison (9751 jobs). New target modules
had no warnings; the logs replay existing deprecation warnings in the Brouwer
dependencies. A later source synchronization passed all 15,905 blueprint
references and the selected changed-declaration coverage. Import generation and
checking passed for 66 aggregators covering 2199 production modules.
The subsequent parent-Hamiltonian and QCA aggregate build passed with 9946 jobs,
including the refactored periodic classification and divisible gap theorems.
The source synchronization then passed 15,940 references, and the generated
imports covered 2207 production modules. The residual-space, common-period
family-gap, and generic infinite-volume blocking transport results have also
passed their separate strict source and kernel checks; their final aggregate
build is pending.

The revised ground-projection note compiles with resolved references and no
layout warnings. Its five-page version was rendered and inspected, including
the blocking comparison and the distinction between divisible and all lengths.

A compiled declaration check importing the older root module reported 31 missing
parent-Hamiltonian and QCA declarations after their focused builds. Its root
import environment was stale. This check is not reported as passing; the final
compiled verification must import the rebuilt parent-Hamiltonian and QCA
aggregates. The unrestricted Nachtergaele Theorems 1.1 and 1.2 remain separate
from the primitive-family and periodic-tensor results: the general GVBS support
identification, original interaction construction, and the finite-volume gaps in all remaining residue classes
are still required.

The original-chain infinite-volume assertion is now also proved for a periodic
MPS tensor. Its hypotheses are periodicity, positive physical dimension,
$R>0$, $h\geq0$, and the eventual original open-chain kernel identity.
One positive constant works for every pure state in the original zero-energy
face and every centered local observable. The literal complex commutator
energy limit is included, along arbitrary filters on which both margins
diverge. Primitive sectors, faithful matrices, and separation are derived,
and translation invariance of a competing state is not assumed. The strict
kernel check for `PeriodicQuasiLocalGroundStateGap.lean` passed with standard
logical axioms only and no warnings. The generic original-chain blocking
transport has five separately checked public declarations.

The compiled canonical declarations of the already built audited modules
were checked independently: all 527 declarations passed. Nine further
residual-space and common-period family-gap declarations have passed source
kernel audits and await the corresponding aggregate artifacts. This focused
check does not assert that every declaration in the full repository or every
blueprint chapter was checked.

The next parent-Hamiltonian aggregate build passed with 9,950 jobs, including
the residual ground-space decomposition and the periodic-family aligned gap.
The corresponding independent compiled check passed for all 536 canonical
audited declarations. This supersedes the earlier nine pending declarations.
The generic commutator transport and the former periodic composition also
passed their actual package builds; the shortened periodic proof through
`BlockedPrimitiveQuasiLocalGap.lean` has a fresh strict source audit with
standard logical axioms only.

The updated six-page mathematical note compiled without warnings or
overfull or underfull boxes. Its changed pages were rendered and visually
checked. Section 9 records the original-chain literal commutator gap and
its positive-functional comparison argument. The unrestricted general-GVBS
assertion and the remaining finite-volume residue estimates are explicitly
kept separate.

`ResidualBoundaryOverlap.lean` establishes three estimates: the exact transfer
of a prefix angle bound to correlated residual ranges; uniform residual angle
decay for inequivalent primitive prefixes; and convergence of the finite sum
of residual-sector projections to the projection onto their joint space.
The tail length may vary arbitrarily. Strict standalone verification and
three kernel queries passed with standard logical axioms only and no warnings.
The estimate for three overlapping intervals is a further mathematical step.

A later comparison with the broad source audit confirms that all 96 complete
module bodies remain unchanged, and that the five focused declarations are
still byte-for-byte present in their current source files. The four containing
lower modules have changed outside those extracted bodies; their entire-file
hashes are therefore not claimed to be current. The exact comparison is
recorded in `/tmp/tnlean-parent-broad-audit-current-comparison.json`.

The commutator-gap statements have been strengthened to quantify one positive
constant before all states, local observables, filters, and boundary margins.
The proof chooses this constant from the finite primitive family before any
exhaustion. Independent mathematical review found no additional hypothesis: the
eventual original kernel identity is the hypothesis printed in Nachtergaele's
Theorem 1.2, and no interaction-range bound beyond positivity is supplied.
For the finite weighted periodic family, the common length and all primitive
normalization and separation data are derived internally. The empty-family
conclusion is an empty zero-energy face, not ground-state existence.

The generic and weighted-family strengthened proofs have complete source
bodies and clean warm verification. Fresh standalone audits have temporarily
encountered unavailable unrelated import artifacts during the concurrent full
repository build. These import failures occur before their proof bodies and
are not recorded as successful checks. The final aggregate verification is
waiting under the prescribed shared build lock.

The periodic residual projector-sum theorem and the promoted cyclic separation
lemma passed a strict exact-source audit with only standard logical axioms and
no warnings. The residual sector decomposition and projector comparison are
now derived from periodicity alone. They do not imply the full three-interval
defect estimate. The extended six-page note, including finite periodic
families, compiled cleanly and its changed final page was visually checked.

The cyclic-degree continuation now has three checked algebraic components.
`CyclicWordSpan.lean` proves that left-canonical normalization propagates a
full word span in one cyclic degree to every later length. Its six complete
source declarations passed strict elaboration and six kernel queries, with
only the standard axioms. `CyclicBlockedWordSpan.lean` has six checked
complete declarations extracting the initial cyclic span from simultaneous
compressed-sector word spanning. `CyclicBoundaryIntersection.lean` has eleven
checked complete declarations deriving the one-step intersection from this
span, with injectivity confined to the relevant cyclic boundary space.
The latter two audits include the exact cyclic-degree dependency bodies;
compiled module verification is pending the shared build lock. None of these
intermediate statements asserts eventual spanning from periodicity alone.

`SupportedRangeProjector.lean` contributes two strictly checked formulas for
range projections from a supported Gram inverse and for the three-map
projection difference. `ResidualBoundaryOverlap.lean` now has four strictly
checked declarations, including its exact bilinear identity and a uniform
sector-angle estimate for every residual tail length. The raw periodic
projection-sum consequence has also passed its exact-source kernel audit.
The supported residual Gram estimate and the three-window estimate remain
in progress; no all-residue finite-chain gap is claimed.

The locked regeneration and build completed successfully with 9,961 jobs
(`/tmp/tnlean-parent-cyclic-regenerate-build.log`). Its targets were the
parent-Hamiltonian and quasi-local aggregates and the supported-projector
module. This verifies the compiled module boundaries for the cyclic
word-span, cyclic boundary intersection, cyclic primitive decomposition,
residual Gram, residual overlap, and strengthened infinite-volume gap results.
Regeneration and build were performed under one shared lock.

The strengthened raw-periodic infinite-volume gap passed its current strict
exact-source audit (`/tmp/tnlean-periodic-quasi-gap-uniform-exhaustion-audit.log`).
The same positive constant precedes every state, observable, filter, and margin
in the conclusion. The period-one primitive faithful-witness theorem and its
residual projection-sum consumer also passed their current strict audit.
`ResidualBoundaryGram.lean` has fifteen public declarations whose complete
source passed strict elaboration and fifteen kernel queries with no warnings
and only the standard axioms. It derives the correlated row corner and its
uniform Gram error from periodicity; a supported inverse is being constructed
in a separate module.

`SupportedRangeProjectorNorm.lean` now proves the operator norm bound and its
arbitrary-filter convergence consequence from the exact supported
factorization. Its two complete declarations passed strict elaboration and
two kernel queries, with no warnings and only the standard axioms. Their
actual compiled module check remains pending the next locked build.

The next locked build completed with 9,963 jobs
(`/tmp/tnlean-parent-residual-coordinates-build.log`), including the supported
projector norm module, the exact residual-window coordinate module, and the
parent-Hamiltonian and quasi-local aggregates. The residual-window module has
ten complete public declarations, all strictly checked with standard axioms
only and no warnings. Its identities factor the full residual boundary through
both overlapping windows and compute the mixed Gram pairing, with all lengths
including zero. They do not yet estimate the projector difference.

The current compiled-kernel audit passed all 621 requested declarations
(`/tmp/tnlean-parent-current-compiled-kernel.log` and the corresponding result
and manifest). Every printed dependency set is contained in the standard
axioms; there are no missing declarations, errors, or warnings. Three
additional compiled signature checks verify the strengthened quantifier order
for the generic blocked, finite periodic-family, and raw periodic
infinite-volume gaps. The new declaration set includes the supported norm
estimates, all fifteen residual Gram declarations, all ten exact residual
window declarations, and the cyclic span/intersection components.

The raw periodic residual projection-sum consumer was subsequently simplified
to use the common cyclic primitive-sector resolution. Its statement is
unchanged; the duplicated primitive, faithful-density, separation, and
isometry extraction was removed. The complete updated body passed its strict
kernel audit (`/tmp/tnlean-periodic-residual-refactor-final-audit.log`) with
standard axioms only and no warnings. The revised blueprint proof cites the
common resolution. A fresh compiled check of this refactor is still pending.

The four complete declarations in `PeriodicOriginalIntersection.lean` now
derive eventual original cyclic spanning, original one-step intersection,
canonical open kernels for every range above a derived threshold and every
volume at least that range, and a positive original parent interaction. No
physical or bond dimension instance is supplied. The exact four bodies plus
the common canonical-matrix helper passed strict elaboration and seven
standard-only kernel queries with no warnings.

`PeriodicParentInteractionGap.lean` combines this interaction construction
with the strengthened periodic infinite-volume gap. Its headline signature
has only the periodic tensor hypothesis: physical nonvanishing is derived
internally. It gives one interaction with exact kernels for all volumes above
its range and one positive commutator constant before all pure states,
observables, filters, and margins. Its complete source with the two exact
new dependency bodies passed eight standard-only kernel queries with no
diagnostics. A subsequent docstring correction changed no declaration or
proof tokens; the manifest records it. This closes the original interaction
construction for a single explicit normalized periodic tensor; general GVBS
identification and all-residue finite-chain gaps remain separate.

The canonical interaction matrix construction was promoted to
`CanonicalParentInteractionMatrix.lean` and three existing consumers were
refactored without statement changes. The helper passed three strict queries;
the three complete updated consumer sources passed respectively two, five,
and four strict queries, all standard-only and without warnings. Of the old
96 complete-source audit bodies, 93 remain byte-for-byte unchanged; these
three now have fresh complete-source checks. The five selected lower bodies
remain unchanged. This updates the historical broad-audit provenance rather
than treating changed source hashes as unchanged.

The mathematical ground-projection note now includes Section 10, deriving the
original cyclic spanning, restricted boundary injectivity, intersection,
positive canonical interaction, and its infinite-volume gap. The rebuilt PDF
has seven pages and no TeX warnings, undefined references, or overfull boxes.
Pages 5--7 were rendered and visually verified after the update; pages 1--4
were previously verified and remain unchanged.

The supported residual inverse module has twenty-two complete public
results. Its exact-source strict/kernel audit passed with standard axioms
only and no warnings. It constructs self-adjoint supported Gram inverses,
bounds their norms uniformly over every tail length, and proves their
uniform-limit displacement for an arbitrary diverging prefix filter and
arbitrary tails. `ResidualWindowGram.lean` adds seven strictly checked
identities and coefficient-one bounds for the two window Grams, together
with their uniform boundary norms. Neither module alone proves the remaining
three-window projector estimate.

`ResidualWindowVirtualNorm.lean` proves the length-independent square-root
bond-dimension bound for the virtual prefix map. Its complete source passed
two strict kernel queries with standard axioms only and no diagnostics.
`ResidualWindowCrossOverlap.lean` passed five such queries and proves uniform
relative angles and projection-product decay between distinct sectors, with
arbitrary prefix and tail lengths.

`Martingale/ResidueCoverGapCriterion.lean` passed nine complete-source queries
(twelve with the canonical interaction helper). It proves the energy comparison
for the aligned left interval and the finite family of terminal residues, their
exact kernel intersection, and a periodic all-length gap criterion. The
overlapping-projection bound remains an explicit hypothesis of that criterion;
the unconditional all-residue gap has not yet been concluded.

The right residual-window sector-sum module passed four strict complete-source
queries, with its two exact direct-sum dependencies included in the audit.
All axioms are standard and there are no diagnostics. Its bound and limit
allow arbitrary preceding prefixes and arbitrary residual tails. The generic
finite-sector assembly (two declarations) and all-selections uniformization
(one declaration) also passed their complete-source strict kernel checks.
They are inputs to the remaining original-chain defect comparison.

The locked integration refresh acquired the repository lock and regenerated
the aggregators once under that lock. It includes the new right-window,
Gram-inverse, cancellation, original-interaction, and infinite-gap modules.
A replayed end-of-file whitespace warning in the direct-sum operator module
was identified; its source audit had concatenated that file with the next
body and thus did not expose its missing final newline. The correction
changes no declaration or proof tokens.

The first locked integration build compiled the new original intersection,
positive interaction, automatic periodic infinite-volume gap, residual inverse,
right-window sector sum, and finite-cover criterion. Its combined target failed
only because the cancellation module omitted its own matrix-notation scope;
concatenated dependency sources had supplied that scope in the earlier audit.
The scope was added and the actual standalone package-option check passed.
The direct-sum module's final newline was also corrected. A new complete locked
refresh is queued at `/tmp/tnlean-parent-residual-final-build.log`.

The five left-window sector-sum statements and the limit-to-finite-gap criterion
passed their complete-source strict checks with standard axioms only and no
diagnostics. The criterion still explicitly assumes the actual physical
cover-projection limit; its elimination is the remaining tensor argument.

The second locked integration build passed all 9979 jobs. The original
interaction and infinite-volume gap, supported residual inverse, left/right
window sector sums, cancellation, and finite-cover limit criterion now have
actual package-option builds. A remaining new whitespace warning identifies
the missing final newline of the window-Gram file and is being corrected.

Independent comparison with `References/cond-mat_9410110/main.tex` found no
mathematical error in the cancellation, factor estimates, or cover criterion.
The metric acts on the right, the cyclic support acts on the left, and they
commute; the support cancellation is justified by the exact tail-adjoint
range. The references for these overlapping-window components were corrected
from commutation (i) to (ii), without changing proof tokens. Part (i) is the
sector projection-sum estimate; part (ii) is the overlapping-window defect.
The source anchors are (3.15), lines 1567--1574; `boundAm`, lines 2394--2409;
commutation (i)/(ii), lines 2453--2465; and the finite-gap proposition,
lines 2593--2614. The explicit numerical lower bounds in that proposition
remain separate from the eventual positive-gap criterion.

The third locked integration build passed all 9982 jobs. It includes the
eight window-Gram identities, both exact original-chain window-range
identifications, the full-window sector sum and cover identification, and
the three-operator perturbation estimate. The earlier missing final newline
in the window-Gram file is corrected. The overlapping-window citation repairs
are included in this build.

The finite residual mixed-Gram displacement now passes its complete-source
strict check at the ordinary heartbeat limit, with standard axioms only and
no diagnostics. It permits arbitrary prefix and residual-tail lengths while
the shared middle interval tends to infinity. The blueprint contains all
fifty-two public declarations in the thirteen recently completed operator,
window, and finite-cover modules checked by
`/tmp/tnlean-parent-ready-physical-reverse-blueprint.json`. The remaining
same-sector step is to convert this mixed-Gram displacement to a product of
supported range projections. The unconditional all-residue finite-chain
gap is therefore still pending.

The nonzero physical dimension of a normalized periodic tensor is now the
public consequence `IsPeriodic.physDim_ne_zero`. Its complete defining module
passes strict standalone elaboration without diagnostics. The original kernel
and infinite-volume gap constructions use this consequence, and the planned
all-length finite-gap construction uses the same fact. The promotion removes
the repeated empty-alphabet argument without adding a dimension hypothesis.

The residual proof session's tactic-pattern scan is recorded at
`/tmp/tnlean-parent-residual-tactic-patterns.log`. Its highest-ranked patterns
belong to earlier boundary and spectator arguments. The finite-fiber relative
angle calculations remain the previously recorded two-occurrence candidate;
the canonical interaction matrix and physical-dimension consequences are
shared mathematical lemmas.

An external synchronization saved the shared main working tree, including
untracked sources, in stash `519ea3524c69d0f014d812e1932506fe525cc11a`
at 2026-10-02 23:58:28 UTC. Sources disappeared during the ongoing locked
build; four scheduled targets consequently failed with missing-source
diagnostics. No theorem diagnostic caused this failure, and its compiled
kernel-query callback did not run.

The coherent tracked and untracked source snapshot was recovered in
`worktrees/parent-gap-recovery`, based on exact `origin/main` at
`4f21dc48c2a9ed0ab3d899232301fe6c98d624c9`. The stash was neither removed
nor applied to the simultaneously changing main tree. Canonical cache seeding
uses the fully warmed `worktrees/hot-main` at that same revision. Later
strictly checked sources were retained from their exact temporary snapshots.
The nonzero physical-dimension consequence now lives in
`MPS/Periodic/PhysicalDimension.lean`, with the same statement and proof;
the periodic definition module remains identical to the base revision.

The two supported-projector statements and the two joint-sector projection
statements passed complete-source strict kernel checks without diagnostics,
using only standard logical axioms. The periodic joint-sector statement
derives every primitive, faithful, separation, intertwining, and tail-support
witness from periodicity. It permits arbitrary exterior lengths while the
common interval grows. The exact physical-cover isometry and all four
left-window identities also passed their source checks. The intermediate
gap criterion retains its exact-kernel conclusion at the same chosen range.

Recovery preservation checks confirmed the exact operator, right, full, and
left-cover sources. The residual inverse and cross-overlap differences from
earlier manifests are citation prose only; their declaration and proof
bodies are preserved. The recovery blueprint has complete reverse coverage
for fifty-nine public declarations in the recently finished operator,
window, criterion, and dimension modules.

The unconditional physical-cover limit and both all-volume gap statements
passed one strict check of eight exact complete sources and fifteen kernel
queries, without warnings or errors. Every axiom set consists of `propext`,
`Classical.choice`, and `Quot.sound`. The physical limit allows arbitrary
exterior lengths. Periodicity alone chooses one canonical interaction range,
exact kernels at all volumes above that range, and a positive actual-kernel
norm gap at every volume. The positive matrix interaction uses precisely
that range and the same gap. Independent mathematical review found no extra
hypothesis or unsupported numerical claim.

The canonical seed from exact, fully warmed `origin/main` succeeded in the
recovery worktree. The final parent-Hamiltonian and QCA integration build
is queued under the repository lock, followed by 740 compiled kernel queries
and six public signature checks. The recently completed declarations have
complete reverse blueprint coverage: 62 public declarations, none missing.
The recovered whole-tree source synchronization has three unrelated missing
references, in the BNT blocking and local-circuit chapters; all reviewed
parent-Hamiltonian references resolve. These three references are not changed
by this work. The report is
`/tmp/tnlean-parent-recovery-blueprint-sync.json`.

The physical-dimension consequence also passes strict standalone elaboration
in its new module against the recovered prebuilt dependencies, without
diagnostics. Its statement and proof are unchanged by the move. The
mathematical note now explains the all-residue argument and closes that
finite-volume step for one normalized periodic tensor, while retaining the
separate general-GVBS presentation question.

The updated mathematical note renders as eight pages. Its final LaTeX log
has no warnings or box diagnostics. Pages 5--8, which contain the changed
scope statements and the new all-length argument, were visually inspected;
there is no clipping or overlap. Earlier pages retain their previously
reviewed text. The PDF and rendering record are under
`/tmp/tnlean-ground-projection-note/`.

The combined finite- and infinite-volume theorem now chooses one positive
interaction and retains both conclusions for that same interaction. Its
complete-source strict check passed without diagnostics, with standard
axioms only. The finite and infinite gap constants may differ, and both
are chosen before the state, observable, and exhaustion. Reverse coverage
now includes 63 public declarations, all tagged. The planned compiled audit
has 741 axiom queries and seven public signature checks. The whole-tree
blueprint synchronization still has precisely the same three unrelated
missing references; the parent-Hamiltonian entries have none.

The twelve recently appended proof entries now place their called-result
dependencies inside the proof, leaving only defining notions in statement
dependencies, in accordance with the blueprint style guide.

The first recovery aggregate build reached the new operator limits, original
intersection, and local faithful support modules, but stopped at consumers
of two missing strengthened blocking bounds. The recovered stash copy of
`MPS/MPDO/CPSVSharpBlocking.lean` was older than the pinned base revision.
Its exact version from `4f21dc48c2a9ed0ab3d899232301fe6c98d624c9` was restored;
that version already proves both bounds with the additional interaction site.
No theorem was weakened or newly assumed. The stale source is preserved under
`/tmp/tnlean-recovery-CPSVSharpBlocking-stale-stash.lean`, and the restoration
record is `/tmp/tnlean-parent-recovery-blocking-bound-restoration.json`.
The compiled-query callback of the failed build did not run.

Three further support results passed complete-source strict checks without
diagnostics and with standard axioms only. Periodic phase-class representatives
preserve the original joint boundary spaces at every length; the supplied
phase relation is upgraded to an actual gauge relation by the periodic overlap
dichotomy. A normalized tensor with a positive-definite stationary matrix
admits a nonempty periodic corner presentation with literal isometries, both
intertwining directions, and all-length support equality. A normalized tensor
with an arbitrary faithful virtual matrix has a positive density of trace
one on each finite interval, whose actual matrix range is exactly the boundary
space. Stationarity is unnecessary for that finite-density statement.
The respective evidence is recorded in the final manifests for
`PeriodicSectorRepresentatives`, `FaithfulPeriodicGroundSpace`, and
`LocalDensitySupport` under `/tmp/`.

The new `GroundSpaceIndependence` module passes a strict complete-source check
of all three public declarations. The lower Gram estimate proves independence
when the overlap-bound matrix has norm less than one. Uniformly vanishing
pairwise overlaps therefore give eventual independence, even for varying
Hilbert spaces and arbitrary filters. Distinct primitive faithful tensors
satisfy this condition. Its exact source hash is
`e8047d727fa332eeb601c236c9edb3ca83347196c46624411a27e3f9df52311b`;
the evidence is `/tmp/tnlean-ground-space-independence-final-manifest.json`.

The corrected integration build is running under the common repository lock.
Its frozen compiled audit has 752 axiom queries and ten signature checks.
Reverse blueprint coverage includes all 74 public declarations in the
recently integrated modules. Whole-tree source synchronization now has one
unrelated missing reference, `Matrix.rectKronecker_one`, in the local-circuit
chapter; restoring the pinned blocking source resolved the other two.
No parent-Hamiltonian reference is missing.

The mathematical note now includes the same-interaction finite and
infinite-volume theorem and the faithful finite-density and periodic-sector
support arguments. The updated PDF has nine pages. Its final LaTeX log has
no warnings or box diagnostics; the changed pages 8 and 9 were visually
inspected and are readable without clipping or overlap. The record is
`/tmp/tnlean-ground-projection-note/faithful-support-pdf-qa.json`.

The second recovery integration build compiled the strengthened blocking
bounds, all-length periodic finite gap, and same-interaction finite and
infinite gap. It stopped only at a missing complex-positivity scope in the
new faithful periodic presentation file. The declaration and proof were
unchanged by adding that scope; direct standalone elaboration then passed.
The compiled-query callback of this second failed build did not run.

The third recovery integration build PASSED all 10,025 scheduled jobs,
including the parent-Hamiltonian and QCA aggregates. Its compiled callback
and independent validation PASSED all 761 axiom queries and thirteen signature
checks, without diagnostics. Every axiom set is contained in `propext`,
`Classical.choice`, and `Quot.sound`; all 54 recorded source hashes agree.
The immutable evidence is
`/tmp/tnlean-parent-recovery-compiled-kernel-761-passed-manifest.json`,
`/tmp/tnlean-parent-recovery-compiled-kernel-761-passed.log`, and
`/tmp/tnlean-parent-recovery-compiled-kernel-761-passed-result.json`.
The actual build log is `/tmp/tnlean-parent-recovery-final-build-3.log`.

The checked development includes the matrix-free joint intersection criterion,
with explicit middle-space independence and individual intersection identities,
and the literal quasi-local finite-density support theorem. The latter gives
one density matrix for every translated interval of a fixed length, with
range exactly the tensor boundary space. The faithful-generator infinite-volume
gap follows from its periodic presentation and the actual eventual kernel
identity, without irreducibility or periodicity of the supplied generator.
All 83 recently integrated public declarations have reverse blueprint coverage.

Further strict complete-source checks pass for the finite-family intersection
argument, support compression, and original-length periodic independence.
The family intersection argument obtains exact canonical open kernels from
individual intersections and middle-space independence, without a supplied
simultaneous word span. Periodic tensors now have uniformly bounded boundary
preimages at every sufficiently large original length. Their original mixed
transfer decay gives vanishing pairwise support angles and eventual independence
for an inequivalent finite family. Equivalent repeated sectors are retained by
first selecting representatives with exact all-length joint support equality.

Stationary support compression supplies faithful normalized generators and
preserves every finite insertion expectation, including length zero. It does
not identify the original and compressed full boundary spaces: unused or
transient original directions can enlarge the former. The independent strict
records are the final manifests for `PrimitiveFamilyIntersection`,
`PeriodicGroundSpaceIndependence`, and `StationarySupportCompression` in `/tmp/`.

The common empty-physical-alphabet argument has been promoted to
`IsLeftCanonical.physDim_ne_zero`; the periodic and finite-density consumers
pass direct strict checks after using that helper. A separate arbitrary-tensor
criterion extends an eventual aligned gap to every original length from
exact kernels and supplied residual cover limits. It is explicitly conditional;
it is not presented as an unrestricted family gap theorem. Its evidence is
`/tmp/tnlean-family-residue-cover-gap-final-manifest.json`.

The fourth actual integration command is waiting for the repository-wide
build lock. The previously passed 761-query evidence remains immutable.
No compiled result from this fourth command is claimed until it finishes.

The latest strict source checks also construct the interaction for a finite
periodic weighted family. Selecting gauge and phase representatives gives
eventual original-length independence, then exact canonical kernels and a
common literal infinite-volume commutator gap. No interaction, kernel identity,
sector independence, or simultaneous word span is supplied. Applying its
all-length support identity to faithful stationary generators constructs the
same conclusions for an arbitrary normalized tensor with a faithful fixed
point. Its own generated quasi-local state belongs to the zero-energy face;
purity of that state is not assumed or asserted.

Stationary support compression now preserves the actual continuous quasi-local
functional. Equality on finite insertion expectations gives equality on every
finite region, and uniqueness of the continuous extension gives equality on
the completed algebra. This does not identify the original full boundary
spaces with those of the compression. Strict evidence is recorded in
`/tmp/tnlean-periodic-block-family-parent-gap-final-manifest.json`,
`/tmp/tnlean-faithful-parent-interaction-gap-final-manifest.json`, and
`/tmp/tnlean-quasi-state-equality-final-manifest.json`.

The prepared integration audit currently contains 797 axiom queries and
22 signature checks, with reverse blueprint coverage for all 119 newly
collected public declarations. These are prepared checks, distinct from the
761-query compiled audit that has already passed. The fourth build still
awaits the shared lock.

The nonfaithful stationary-state construction passes a strict fifteen-body
check with eight standard-only axiom queries and no diagnostics. From
normalization and a nonzero positive stationary matrix alone, it obtains
faithful compressed generators for the identical quasi-local state, a
positive constructed interaction, exact compressed boundary kernels for
every volume at least its range, membership of the original generated state
in the zero-energy face, and one literal commutator gap for all pure states
in that face. The kernel statement is about the compressed tensor; it does
not assert equality with the original full boundary spaces. Evidence:
`/tmp/tnlean-stationary-parent-gap-final-manifest.json`.

The physical residual-cover criterion and exact coordinate resolution of a
finite direct sum also pass complete-source strict checks. Their respective
evidence is `/tmp/tnlean-physical-residual-cover-limit-final-manifest.json`
and `/tmp/tnlean-block-inclusion-resolution-final-manifest.json`. Both remain
auxiliary statements with their actual hypotheses explicit. The prepared
compiled audit now has 802 queries; its execution still awaits the fourth
integration build.

The finite-family argument now constructs canonical interactions with exact
open boundary kernels at every sufficiently long volume and a uniform gap
above the actual kernel at every original length. The complete twenty-body
strict check passed without diagnostics and with standard logical axioms
only. Faithful stationary generators inherit these all-length finite gaps;
the same constructed interaction contains their generated state and has
the literal infinite-volume gap. Stationary support compression extends
this construction to a nonzero positive stationary matrix while preserving
the actual quasi-local state. Its kernel remains that of the compressed
tensor. Exact evidence is recorded in the final manifests for
`periodic-block-family-open-gap`, `faithful-parent-finite-gap`, and
`stationary-parent-finite-gap` under `/tmp/tnlean-`.

For a prescribed positive interaction of positive range, eventual exact
open kernels suffice to transfer the canonical gaps. The long-window
comparison adds no assumption on the local interaction kernel. The faithful
generator specialization proves both finite and infinite gaps for the
same prescribed interaction. The generic transfer and the twenty-four-body
faithful specialization both passed strict checking with no diagnostics
and standard logical axioms only. Their records are
`/tmp/tnlean-canonical-gap-to-interaction-gap-final-manifest.json` and
`/tmp/tnlean-faithful-given-interaction-gap-final-manifest.json`.

The supplied-isometry calculation also identifies the source one-site
Heisenberg insertion and its trace duality. A multi-site source-order
identification requires a separate reversal argument; an arbitrary GVBS
boundary-limit presentation has not yet been normalized into the supplied
generating-data setting. These remaining points stay explicit in the note.

All retained displays in the newly appended blueprint portion now use
`align`, and all 145 collected public declarations have blueprint coverage.
The prepared compiled audit contains 823 axiom queries and 32 signature
checks. The fourth integration command still awaits the repository-wide
build lock; the immutable passed compiled record remains 761 queries.
The refreshed mathematical PDF has twelve pages, no LaTeX warnings, and
visually verified updated pages 9--12; its exact record is
`/tmp/tnlean-ground-projection-note/final-hour-pdf-qa.json`.

The final additions give both gaps for the same prescribed positive
interaction of a periodic weighted family, using only eventual exact joint
open kernels. Their twenty-two-body strict audit passed without diagnostics
and with standard logical axioms only; the exact record is
`/tmp/tnlean-periodic-block-family-interaction-gap-final-manifest.json`.

The multi-site source convention is now explicit: a written Heisenberg
composition has the expectation of the reversed physical tensor product
in the forward-word convention. This includes the empty product and
requires no positivity, normalization, or stationarity for the trace
identity. Its two-body strict audit passed; evidence is
`/tmp/tnlean-source-ordered-insertion-final-manifest.json`. General GVBS
boundary-limit normalization remains separate.

The final prepared compiled audit has 827 queries and 35 signature checks;
all 149 collected public declarations have blueprint coverage. Source
synchronization has one unrelated missing declaration,
`Matrix.rectKronecker_one` in the local-circuit chapter. The twelve-page
PDF and its visual record were refreshed after these last additions.
Both prepared proof-refinement patches pass applicability checks and
remain unapplied while the queued integration inputs are frozen.

The fourth integration command has now completed successfully: all 10,055
scheduled ParentHamiltonian/QCA jobs passed, followed by 827 compiled
axiom queries and 35 signature checks. Exact source hashes were validated;
all queried theorems use only standard logical axioms, and the query log
has no diagnostics. Immutable evidence is retained under
`/tmp/tnlean-parent-recovery-compiled-kernel-827-passed`. One build-time
whitespace warning at the end of `PrimitiveFamilyIntersection.lean` is
being removed with the prepared proof refinements. The separate blueprint
source check still has the unrelated local-circuit declaration mismatch
reported above.
