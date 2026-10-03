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

## The original unrestricted assertion

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

The earlier primary literature does not supply the unrestricted assertion. [Fernández-González, Schuch, Wolf, Cirac, and Pérez-García, Section 2.3, Definition 3 and Remark 1](https://arxiv.org/html/1210.6613) first assumes a jointly injective blocked tensor in its parent construction, and explains the sufficient interaction length $k+1$ when blocking $k$ sites gives injectivity. The comparison in PGVWC07 also uses its injectivity condition. These statements do not remove the missing range hypothesis in the review’s broader definition.

The counterexample is recorded explicitly in [the short-range parent-gap note](../paper-gaps/cpgsv21_short_range_parent_gap.tex), whose status is `false-source/resolved`. [ShortRangeHeisenbergTensor.lean](../../TNLean/MPS/ParentHamiltonian/ShortRangeHeisenbergTensor.lean) proves the direct source basis-of-normal-tensors certificate, joint injectivity at length two and its failure at length one, and the exact singlet parent projection. [ShortRangeHeisenbergGap.lean](../../TNLean/MPS/ParentHamiltonian/ShortRangeHeisenbergGap.lean) proves the nonzero Fourier eigenvector identity and `not_exists_eventual_uniform_gap_shortRangeHeisenbergTensor_two`, ruling out a positive uniform gap even after excluding any finite set of ring lengths. The two supporting algebra modules prove the one-magnon exchange recurrence and the positive eigenvalue limit. Its identification with the Heisenberg model is consistent with the primary spectral analysis of [Koma and Nachtergaele](https://arxiv.org/abs/cond-mat/9512120), whose isotropic limit is gapless. The verified conclusion is a tensor with three normalized normal blocks and a fixed positive range $R=2$ for which no $\gamma>0$ can satisfy $\gamma\|v\|\leq\|H_{N,R}(B)v\|$ for all sufficiently large $N$ and all $v\perp\ker H_{N,R}(B)$. The main counterexample, source BNT certificate, compact deformation gaps, and arbitrary sufficient-range normal gaps use only `propext`, `Classical.choice`, and `Quot.sound`.

A different useful strengthening would give an open-chain gap at each *admissible* $R\geq S+1$ uniformly for every $N\geq R$, rather than only the current subsequence $N=pM$. That statement remains separate from the unrestricted source issue. This possible strengthening is not needed to settle the unrestricted assertion, which is now formally refuted. The seven requirements are accounted for by the proved sufficient-range theorems and the explicit corrections or counterexamples to the false source statements; the distinction from literal proofs of the printed assertions is retained throughout.

## Verification

The open-chain strengthening now has two proved supporting results.
[IntervalGapTransport.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/IntervalGapTransport.lean)
preserves a finite-interval gap when the interval Hamiltonian acts on a larger
chain. [OverlappingIntervalGap.lean](../../TNLean/MPS/ParentHamiltonian/Martingale/OverlappingIntervalGap.lean)
combines a prefix gap and a terminal-interval gap: if their common lower bound
is $\kappa$ and the product of their ground projections differs from the
full-chain ground projection by at most $1/2$, then the full-chain gap is at
least $\kappa/16$. The all-length multiblock conclusion still requires the
assembly of these results with the boundary-space kernel identities and the
uniform three-interval projector estimate; it is not counted as proved here.

The new modules and the `TNLean.MPS` import module passed the prescribed Lake build. The final axiom checks for the short-range counterexample, its source BNT certificate, the positive affine deformation gap, and the arbitrary sufficient-range normal gaps report only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof or additional axiom was introduced.

Declaration checking passed for all 637 references in the four relevant BNT and parent-Hamiltonian chapters, and for all 217 references in the five associated paper-gap notes. Blueprint source synchronization and web generation passed. The new counterexample note compiled with resolved citations and equation references, and its four rendered pages were inspected.

The full repository build encountered an unrelated error in `TNLean/PEPS/RegularRegionConnectivity.lean:145`. Global blueprint declaration checking likewise reported 60 missing declarations, all in the concurrent PEPS development. These failures do not occur in the parent-Hamiltonian modules or the focused declaration lists, but the complete repository checks are not reported as passing.
