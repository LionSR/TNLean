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

Thus a parent estimate pParent in [eParent-8,eParent] gives the required middle center pParent-eLeft-eRight-2 in [eMiddle-10,eMiddle]. The derivation of that parent-estimate window from the actual recursive candidate remains open.

The companion energy-transfer theorem gives energy at most three on the actual projected target when the residual is at most 1/16, the original-to-target loss is at most 1/[1024(A+1)] and the candidate loss is at most 1/[100(A+1)], for centered norm bound A. The calibrated family, iterations, sampled node and tree now retain the ordered-word estimates for their same chosen target and operator family. In particular, the tree retains the target and its mutual comparison with the original ground space before choosing the threshold and operation. The remaining quantitative losses must be discharged for these actual witnesses; independently choosing an energy family would not establish their identification. See [the centering note](../paper-gaps/alvv16_soft_regional_energy_centering.tex).

## Verification

The combined continuation at TNLean `e2706cbe715c49745d4399d37dabe3d2559cc494` and QICLean `de8a9d1286709f39d8c37d4d52d6e336925863e5` passed a locked full build of 15,723 jobs, both complete blueprint declaration lists, paper-gap declaration resolution, strict changed-module checks and foundation inspection of 562 public declarations. No Mathlib source was compiled; the prebuilt Mathlib root retained its previous hash. Strict checks covered sixteen companion modules and thirty-nine tensor-network modules or existing regression sources. Their largest recorded times were 29.368 and 21.241 seconds respectively. The warning above twenty-five seconds is retained.

This combined verification includes the same interleaved root's refinement and Ritz extraction, the polynomial coefficient and degree estimates, the same-family ordered-word estimates, the single-witness low-energy approximation, the actual low-energy MPS basis, the soft-parent energy bound, the central-center conversion and the quantitative energy transfer. It does not establish the remaining recursive energy invariant, adaptive success probability or running time.

Subsequent individually checked contributions include explicit fixed soft-energy parameters, a shared nonzero-projection lemma, regional operator coordinate identities, real scalar quadratic-form shifts, and Borel closed spectral cutoffs and Hermitian range projections. Their combined adoption checks remain pending. The spectral measurability results are prerequisites for a future adaptive probability theorem; they do not by themselves make the complete sampling and trimming operation measurable.

No proof placeholders, additional axioms or permanent Lean test fixtures were introduced. Temporary inspection sources were deleted. Unrelated primary-worktree changes are preserved. The continuation has not been pushed or merged.
