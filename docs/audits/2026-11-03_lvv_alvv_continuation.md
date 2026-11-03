# LVV and ALVV: completed arguments and remaining conclusions

The mathematical conclusions below distinguish merged results from the checked local continuation. Upstream main was checked at `5a13935af88f0349e57dfb2a0edd75e40aae0437` on 3 November 2026. Its latest correctness changes do not add an LVV or ALVV construction. The open trackers therefore do not, by themselves, describe which construction steps remain.

## Successive viable sets

The sampled LVV induction was merged in [#10339](https://github.com/LionSR/TNLean/pull/10339). Its polynomial coefficients are uniform when an upper bound for the ground-energy-to-gap ratio is fixed. The Gaussian construction, merged in [#10362](https://github.com/LionSR/TNLean/pull/10362), removes that restriction. Both construct retained families successively and obtain the final approximating vector from their final span. The Gaussian construction also gives arbitrary requested accuracy through the proved product-state extension.

These are existence and approximation theorems. They retain the corrected quadratic trimming radius, the quadratic matrix-net exponent and the library's constant-cut bond estimate. They do not assert every printed inverse-gap dependence or a computational running time. The source errors and quantitative restrictions remain in the corresponding paper-gap notes.

## Degenerate ground spaces

The physical improving families, arbitrary-accuracy bootstrap and interval entropy estimate were merged in [#10248](https://github.com/LionSR/TNLean/pull/10248), [#10250](https://github.com/LionSR/TNLean/pull/10250) and [#10256](https://github.com/LionSR/TNLean/pull/10256).

The continuation constructs two balanced interval trees. The first performs one collective trim at each long parent. The second uses the intended current-space image followed by collective trimming at every round. These are separate constructions. The interleaved tree has full leaves of length at most four window widths, an actual chosen Haar unitary at every long parent, and original-ground-space viability at most 3/200 at each retained interval. Its fixed-child success event is measurable and nonempty, with failure at most (L+1)^(-2). This does not yet give a joint probability theorem for the adaptive algorithm.

The same interleaved root now has a native MPS bound, literal final filter-and-trim refinement and an actual compressed Ritz subspace. The Ritz space has the original ground-space dimension r; both directed errors are at most eta/2; and one bond bounds every vector of this same space. For fixed local dimension q and positive gap lower bound gamma, constants C>0 and k are chosen before the chain, interactions, r and eta, and the bond satisfies

    bond <= C [(L+1)(r+1)(1+1/eta)]^k.

There is one universal C0, chosen before q and gamma, such that both k and log(max(C,1)) are at most C0 U^10/g^2, where g=min(gamma,1) and U=1+log(max(q,50))+log(1/g). The proof concerns this actual recursive output, not a separately chosen approximating MPS. The common family parameter depends on L and r through its explicit calibration. These conclusions are in [PhysicalDGInterleavedPolynomialBond.lean](../../TNLean/MPS/AreaLaw/PhysicalDGInterleavedPolynomialBond.lean).

The printed unchanged-sample assignment requires the documented current-space correction. The printed integer count, adaptive success probability, energy-estimation invariant, source-sharp parameter dependence and running time remain separate obligations. A polynomial bound on output size is not a proof of polynomial running time.

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

Thus a parent estimate pParent in [eParent-8,eParent] gives the required middle center pParent-eLeft-eRight-2 in [eMiddle-10,eMiddle]. The new node theorem derives this window from two child estimates of width 49/16. A simultaneous recursive assignment of the scalar estimates remains open.

The companion energy-transfer theorem gives energy at most three on the actual projected target when the residual is at most 1/16, the original-to-target loss is at most 1/[1024(A+1)] and the candidate loss is at most 1/[100(A+1)], for centered norm bound A. Explicit scalar choices now discharge these budgets: the soft parameters m=12, t=768 and auxiliary cutoff T=384 give rho=32 exp(-42)+1/64<1/16. The calibrated count D bounds A+1, and the actual hard-family target loss and one-word image loss satisfy the required D+1 bounds.

For specified target T and family F carrying the proved calibration and ordered-word certificates, the physical consumer constructs the actual raw regional matrix before its unknown soft minimum, the actual untrimmed word candidate and the actual compressed eigenbasis. Its last eigenvalue lambdaRaw satisfies eSoft<=lambdaRaw<=eSoft+3. Thus p=lambdaRaw-3 belongs to [eParent-3-rho,eParent]. Neither an energy bound nor a minimizing trial vector is supplied as a hypothesis. The conditional certificate is retained explicitly in this auxiliary statement. A further theorem invokes the original tree construction once and applies the update to its same targets, families, operation and actual child spaces. It derives the middle center from attained collar minima and arbitrary admissible child estimates, and returns the raw compressed minimum minus three with width 49/16. The simultaneous recursive scalar assignment remains separate. See [the centering note](../paper-gaps/alvv16_soft_regional_energy_centering.tex).

## Measurable sampling and trimming

Closed spectral cutoffs and Hermitian range projections are now proved Borel without a fixed-rank or spectral-gap assumption. Gram–Schmidt is Borel even on dependent and zero families. Ordered orthonormal range frames are Borel on each fixed-rank matrix stratum; this does not assert measurability of an arbitrarily chosen standard orthonormal basis.

Using these actual range bases, the existing Haar sampler has a jointly Borel ambient projector in its input matrix and unitary. The existing finite-family image support is Borel, with range exactly the sum of the operator images. The literal collective trimming products are Borel for every finite vector family; their products and final subspace are independent of the orthonormal basis used for a fixed input subspace. The true closeness-success set is closed in projection coordinates, so its actual failure complement is Borel.

Finally, a uniform section failure bound epsilon over earlier successful histories A integrates to at most epsilon times the measure of A. For independent probability samples, adding the next failure increases the earlier failure probability by at most epsilon. These measure-theoretic estimates do not require jointly choosing the auxiliary success hulls. The subsequent continuation composes the actual rank-dependent sampler, fixed-family image and collective trim into a globally Borel ambient projection. It proves equality with the trim formed from every orthonormal basis of the same input range. The true closeness event for this output is Borel. A binary probability estimate adds the two child errors and a uniform parent section error. The true regional viability event, with its entire exterior space and arbitrary fixed entangled target, is now Borel. The same statement holds for the existing adjacent-interval merge in its actual coordinates. A fixed product of Haar laws supplies all possible-rank sampler coordinates before the input is known, and the original sampling estimate applies at its actual rank and clamped sample size. Its uniform physical specialization, the literal interleaved iteration and the complete physical-tree probability theorem remain separate steps.

## Verification

The combined continuation at TNLean `9ff185339e7556649699446504eda0c3e15bedf6` and QICLean `6878435c2a2483ba929687579b2575dd393d71bb` passed a locked full build of 15,741 jobs in 188.340 seconds, both complete blueprint declaration lists, paper-gap declaration resolution, strict changed-module checks and foundation inspection of 635 public declarations. No Mathlib source was compiled; the prebuilt Mathlib root retained its previous hash. Strict checks covered twenty-four companion modules and twelve tensor-network modules. Their largest recorded times were 9.338 and 12.258 seconds respectively.

This combined verification includes the same interleaved root's refinement and Ritz extraction, the polynomial coefficient and degree estimates, the same-family ordered-word estimates, the single-witness low-energy approximation, the actual low-energy MPS basis, the conditional actual raw energy estimate, the explicit soft-energy parameters, the central-center conversion, the quantitative energy transfer, and the spectral, frame, trimming, true-event and uniform-section results. It does not establish the remaining recursive energy invariant, adaptive success probability or running time.

The later same-tree node energy update, actual-root merge count, composition of the actual sampler and trim, binary failure estimate and extracted projection-range identities have passed individual strict checks and imported foundation inspections. Their combined adoption checks remain pending. These results do not by themselves establish the complete recursive energy invariant or adaptive tree theorem.

No proof placeholders, additional axioms or permanent Lean test fixtures were introduced. Temporary inspection sources were deleted. Unrelated primary-worktree changes are preserved. The continuation has not been pushed or merged.
