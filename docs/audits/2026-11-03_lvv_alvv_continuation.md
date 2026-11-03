# LVV and ALVV: completed arguments and remaining conclusions

The mathematical conclusions below distinguish merged results from the checked local continuation. Upstream main was checked at `729589b6e9c2ee41c0e9707523f0e055ce4e96f0` on 3 November 2026. The latest merge adds site-dependent product forms and a controlled-Z construction; it does not add an LVV or ALVV construction. The open trackers therefore do not, by themselves, describe which construction steps remain.

## Successive viable sets

The sampled LVV induction was merged in [#10339](https://github.com/LionSR/TNLean/pull/10339). Its polynomial coefficients are uniform when an upper bound for the ground-energy-to-gap ratio is fixed. The Gaussian construction, merged in [#10362](https://github.com/LionSR/TNLean/pull/10362), removes that restriction. Both construct retained families successively and obtain the final approximating vector from their final span. The Gaussian construction also gives arbitrary requested accuracy through the proved product-state extension.

These are existence and approximation theorems. They retain the corrected quadratic trimming radius, the quadratic matrix-net exponent and the library's constant-cut bond estimate. They do not assert every printed inverse-gap dependence or a computational running time. The source errors and quantitative restrictions remain in the corresponding paper-gap notes.

## Degenerate ground spaces

The physical improving families, arbitrary-accuracy bootstrap and interval entropy estimate were merged in [#10248](https://github.com/LionSR/TNLean/pull/10248), [#10250](https://github.com/LionSR/TNLean/pull/10250) and [#10256](https://github.com/LionSR/TNLean/pull/10256).

The continuation constructs balanced interval trees with full leaves of length at most four window widths. One variant performs a single collective trim at each long parent; the interleaved variant applies the improving family to the current space and trims at every round. The resulting theorems retain the corrected current-space assignment and integer iteration count.

For the actual canonical random construction, one common reference, collection of clipped targets and collection of improving families are chosen before the trimming radius and all unitary samples. Every sample satisfies the recorded dimension and rank bounds. Joint original-ground-space viability, at error 3/200, is required only at the full-chain root and the internal intervals in its actual balanced subdivision. This event is Borel under the specified finite product Haar law, and its failure probability is at most

    max(L-1,0)/(L+1)^2.

The proof uses the true failure event of the literal sampled parent. A parent coordinate does not affect either actual child. Uniform conditional section estimates therefore bound the union of guarded failures, and the actual root subdivision contains at most L-1 internal intervals. No viability assumption on other overlapping intervals or supplied sampling-success hypothesis is used. See [PhysicalDGCanonicalJointProbability.lean](../../TNLean/MPS/AreaLaw/PhysicalDGCanonicalJointProbability.lean).

The canonical construction also has a checked approximation theorem. For fixed local dimension q and positive gap lower bound gamma, constants C>0 and k are chosen before the chain, interactions, ground multiplicity r, requested accuracy eta and samples. The physical families precede eta. At each positive eta, one common radius is selected before the samples. Every successful sample supplies its own actual root, unchanged, to the literal final filter-and-trim iteration. The actual compressed Ritz subspace of its terminal space has dimension r, both directed errors at most eta/2, and a common bound for every vector:

    bond <= C [(L+1)(r+1)(1+1/eta)]^k.

The same bond bounds every vector of that sample's initial native root. This concerns the actual recursive output and its actual Ritz space. See [PhysicalDGCanonicalApproximation.lean](../../TNLean/MPS/AreaLaw/PhysicalDGCanonicalApproximation.lean).

A separate theorem for the selected interleaved operation gives explicit coefficient and degree estimates: one universal C0 precedes q and gamma, and both k and log(max(C,1)) are at most C0 U^10/g^2, where g=min(gamma,1) and U=1+log(max(q,50))+log(1/g). See [PhysicalDGInterleavedPolynomialBond.lean](../../TNLean/MPS/AreaLaw/PhysicalDGInterleavedPolynomialBond.lean). The canonical theorem above currently records the qualitative polynomial conclusion.

The block leaves, hard-clipped families, capped gap, fixed failure scale and corrected counts are documented in the paper-gap notes. Identification with the printed soft-truncated generation procedure, its printed energy-power count and its computational running time remain separate obligations. A polynomial bound on output size is not a proof of polynomial running time.

## Low-energy subspaces

Let H have positive-contraction nearest-neighbour terms, let lambda_0 be its least eigenvalue, and let G(c) be the closed spectral subspace below lambda_0+c. For each fixed bandwidth eta>0, the entropy theorem chooses K_eta before the chain length, local dimension, interactions, interval, positive deficit and unit vector. For every positive local dimension q, every unit vector in G(eta-v) and every interval J,

    S_J(psi) <= log dim G(eta)
        + (K_eta/v) (1+log q+log(1+1/v))^3.

No spectral gap or invariance of an original spectral band under a clipped polynomial is assumed. The coefficient on log dim G(eta) is one.

The sharper MPS approximation now gives one normalized witness satisfying both a designated-cut bound and a global bound, with strict overlap greater than 1-delta. Both integer budgets precede the vector, and each bond contains one factor dim G(eta). Writing g=min(min(v,eta/2)/6,1), u=1+log q+log(1/g), the logarithm of the remaining factor is bounded by

    K_eta [u^3/g + g^(-1/4) A^(3/4) u] (1+log A).

For the designated cut A uses log(128/delta); the global bound uses log(128(L+1)/delta). The same witness has squared distance at most delta/2. The scalar case q=1 and zero-length and endpoint cases are included. See [LowDensityDesignatedApproximation.lean](../../TNLean/MPS/AreaLaw/LowDensityDesignatedApproximation.lean) and [the low-energy scope note](../paper-gaps/alvv16_low_energy_family_scope.tex). The continuation also constructs the actual linear image of a standard orthonormal basis of the inner band under its chosen normalized MPS approximants. The map is injective; its range has exactly the inner-band dimension; it approximates the inner band in both directions; and its standard orthonormal basis consists of MPS with bond at most rInner*rOuter*B. The common factor B precedes the basis and vectors. Its accuracy profile uses log(1024(L+1)(rInner+1)/delta). This is mathematical basis existence; the source's complete low-density algorithm, energy guarantee and running time remain separate. See [LowEnergyMPSBasis.lean](../../TNLean/MPS/AreaLaw/LowEnergyMPSBasis.lean).

## Soft truncation and recursive energy estimates

The corrected residual bounds retain the full one-sided ten-unit range of estimated regional energies. Both buffered spectral comparisons and the Hermitian MPO construction concern the same actual soft Hamiltonian. The printed cluster estimate remains false; its two exact counterexamples are retained. The actual polynomial soft cap is bounded by t(1+log m), not by t.

The continuation constructs a native positive centered operator for the same central soft replacement with its original collars. Its norm is at most t(1+log m)+4 ell+14. Its attained ground energy eSoft satisfies eSoft<=eParent<=eSoft+rho, and its energy on the entire original ground space is at most 2+rho times the squared norm. These are consequences of the original interactions, not supplied trial-energy hypotheses. They concern the centered operator; no volume-independent norm is asserted for the unshifted Hamiltonian.

The actual left, middle, right and parent minima satisfy

    eLeft+eMiddle+eRight <= eParent <= eLeft+eMiddle+eRight+2.

Thus a parent estimate pParent in [eParent-8,eParent] gives the required middle center pParent-eLeft-eRight-2 in [eMiddle-10,eMiddle]. The new node theorem derives this window from two child estimates of width 49/16. A subsequent individually checked theorem gives the simultaneous assignment for the deterministic selected operation.

The companion energy-transfer theorem gives energy at most three on the actual projected target when the residual is at most 1/16, the original-to-target loss is at most 1/[1024(A+1)] and the candidate loss is at most 1/[100(A+1)], for centered norm bound A. Explicit scalar choices now discharge these budgets: the soft parameters m=12, t=768 and auxiliary cutoff T=384 give rho=32 exp(-42)+1/64<1/16. The calibrated count D bounds A+1, and the actual hard-family target loss and one-word image loss satisfy the required D+1 bounds.

For specified target T and family F carrying the proved calibration and ordered-word certificates, the physical consumer constructs the actual raw regional matrix before its unknown soft minimum, the actual untrimmed word candidate and the actual compressed eigenbasis. Its last eigenvalue lambdaRaw satisfies eSoft<=lambdaRaw<=eSoft+3. Thus p=lambdaRaw-3 belongs to [eParent-3-rho,eParent]. Neither an energy bound nor a minimizing trial vector is supplied as a hypothesis. The conditional certificate is retained explicitly in this auxiliary statement. A further theorem invokes the original tree construction once and applies the update to its same targets, families, operation and actual child spaces. It derives the middle center from attained collar minima and arbitrary admissible child estimates, and returns the raw compressed minimum minus three with width 49/16. For the deterministic operation selected by the original tree theorem, one simultaneous scalar assignment is now individually checked: every valid short leaf uses an attained original regional minimum, every balanced long node uses its already-assigned child values and the same raw compression, and the width is 49/16 throughout. This deterministic theorem uses viability at every valid interval. A further checked theorem assigns energies on the actual successful canonical root and its listed internal intervals, using the same targets, families and child spaces. Each used short leaf has its attained original minimum, and each used long node has its actual raw compressed minimum minus three. The width remains 49/16. Outside that root subdivision, the scalar function is extended by original attained minima; no additional sampling success is asserted. Thus the L-1 probability count suffices for the used energy recursion, without an all-overlap viability claim. See [the centering note](../paper-gaps/alvv16_soft_regional_energy_centering.tex).

## Measurable sampling and trimming

Closed spectral cutoffs and Hermitian range projections are now proved Borel without a fixed-rank or spectral-gap assumption. Gram–Schmidt is Borel even on dependent and zero families. Ordered orthonormal range frames are Borel on each fixed-rank matrix stratum; this does not assert measurability of an arbitrarily chosen standard orthonormal basis.

Using these actual range bases, the existing Haar sampler has a jointly Borel ambient projector in its input matrix and unitary. The existing finite-family image support is Borel, with range exactly the sum of the operator images. The literal collective trimming products are Borel for every finite vector family; their products and final subspace are independent of the orthonormal basis used for a fixed input subspace. The true closeness-success set is closed in projection coordinates, so its actual failure complement is Borel.

For the literal canonical tree, these results give Borel retained projections, true regional viability events and the joint success event. The entire exterior of each interval is retained, so the target may be entangled with that exterior. A finite product of Haar laws supplies every possible-rank coordinate before the candidate is known; the sampler uses its actual rank and the clamped sample size. The actual parent section fixes both child spaces. Finite-product integration and the guarded-failure union bound then give the physical joint probability estimate above. No measurability of a chosen Ritz eigenbasis is asserted.

## The remaining soft-generation comparison

The next operator-family theorem must concern the same actual three-region soft Hamiltonian. Its middle term has a constructed Hermitian MPO approximation, while the exterior terms and collars remain exact. The missing composition is an actual Chebyshev improving family for this approximating matrix, with an actual tensor decomposition, quantitative minimum gain and complementary contraction, and a spectral-space comparison to the original ground space. Both the soft-truncation residual and the MPO approximation error must be retained.

The corrected simultaneous residual currently contains a term T^m/(m t^(m-1)), in addition to the exponential tail and spectral-subspace dimension factor. At m=4, this does not discharge the present hard-family construction's much smaller D^(-24)s^(-10) comparison budget at the same source scales. A new soft parameter choice, or a proof requiring less precision from its consumers, is needed. Replacing the hard clipping function alone does not establish this theorem. The corrected shifted-heat MPO bounds already give logarithmic dependence on chain length, scale and inverse approximation accuracy, so the false printed cluster estimate is no longer the obstruction to this comparison. The false printed uniform soft-energy estimate and the scalar-centering correction remain documented.

## Verification

The combined continuation at TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` and QICLean `b2ea12a0139820758e161514968ed9ead661c5a7` passed a locked full build of 15,758 jobs in 91.920 seconds, both complete blueprint declaration lists, paper-gap declaration resolution, strict changed-module checks and foundation inspection of 683 public declarations. No Mathlib source was compiled; the prebuilt Mathlib root retained its previous hash. Strict checks covered sixteen companion modules and thirteen tensor-network modules or existing regression sources. Their largest recorded times were 9.673 and 16.754 seconds respectively.

This combined verification includes the same interleaved root's refinement and Ritz extraction, the polynomial coefficient and degree estimates, the same-family ordered-word estimates, the single-witness low-energy approximation, the actual low-energy MPS basis, the conditional actual raw energy estimate, the explicit soft-energy parameters, the central-center conversion, the quantitative energy transfer, and the spectral, frame, trimming, true-event and uniform-section results. It does not establish the remaining recursive energy invariant, adaptive success probability or running time.

The same-tree node energy update, actual-root merge count, composition of the actual sampler and trim, binary failure estimate, fixed Haar product law, true regional viability events and extracted projection-range identities are included in these combined checks. They do not by themselves establish the complete recursive energy invariant or adaptive tree theorem.

Subsequent individually checked contributions establish the deterministic recursive energy assignment, the canonical sampled tree's Borel projections and coordinate dependence, uniform true parent failure, joint physical success, the root-restricted energy assignment and literal same-root Ritz approximation with a uniform polynomial MPS bond. These contributions await the combined build. Their individual checks use explicit immutable dependency sources and objects against the verified pair above; they are not yet represented by that pair's combined-build record.

No proof placeholders, additional axioms or permanent Lean test fixtures were introduced. Temporary inspection sources were deleted. Unrelated primary-worktree changes are preserved. The continuation has not been pushed or merged.
