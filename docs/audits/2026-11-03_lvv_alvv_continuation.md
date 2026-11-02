# LVV and ALVV: completed arguments and remaining conclusions

The open issue descriptions do not by themselves describe the mathematical state of the library. This account distinguishes the merged LVV constructions from the subsequent ALVV developments and states the remaining quantitative conclusions separately. Upstream `main` was checked at `5a41b9ffd27f3fbfdaaede5341a5c48e7c2f0c13` on 3 November 2026, local time.

## Successive viable sets

The sampled LVV induction was merged in [#10339](https://github.com/LionSR/TNLean/pull/10339). Its polynomial coefficients are uniform when an upper bound for the ground-energy-to-gap ratio is fixed. The Gaussian construction, merged in [#10362](https://github.com/LionSR/TNLean/pull/10362), removes that restriction. Both construct the retained families successively and obtain the final approximating vector from their final span. The Gaussian construction also gives arbitrary requested accuracy through the proved product-state extension.

These are existence and approximation theorems. They retain the corrected quadratic trimming radius, the quadratic matrix-net exponent and the library's constant-cut bond estimate. They do not assert every printed inverse-gap dependence or a computational running time. The source errors and quantitative restrictions are recorded in the corresponding paper-gap notes. Thus the absence of a closed tracker is not evidence that the successive existence construction is still missing.

## Degenerate and low-energy spaces

For degenerate ground spaces, the physical improving families, arbitrary-accuracy bootstrap and interval entropy estimate were merged in [#10248](https://github.com/LionSR/TNLean/pull/10248), [#10250](https://github.com/LionSR/TNLean/pull/10250) and [#10256](https://github.com/LionSR/TNLean/pull/10256). The continuation further constructs an actual balanced-tree root, its literal final filter-and-trim iterates, and the Ritz subspace of that same refined space. Its dimension is the original ground-space dimension, both directed approximation errors are bounded, and one explicit MPS bond bounds every vector in the Ritz space.

This tree uses full leaves of length at most four window widths and one collective trim at each long parent. It is not yet the source's interleaved construction. Its final iteration count is derived from the requested Ritz error; it is not identified with the printed count. Uniform polynomial bounds for all parameters of the actual output, interleaved trimming, and the source's adaptive probability and energy-estimation assertions remain distinct obligations.

For the low-energy result, let `H` be a positive-contraction nearest-neighbour Hamiltonian, let `lambda_0` be its least eigenvalue, and write `G(c)` for its closed spectral subspace below `lambda_0+c`. The completed entropy argument chooses, for each fixed bandwidth `eta>0`, a coefficient `K_eta>0` before the chain length, local dimension, interactions, interval, positive deficit and unit vector. For `q>=2`, every unit vector in `G(eta-v)` and every interval `J` satisfy

    S_J(psi) <= log dim G(eta)
        + (K_eta/v) (1 + log q + log(1+1/v))^3.

No spectral gap or invariance of an original spectral band under a clipped polynomial is assumed. The proof fixes one viable outer-band space before all accuracy choices. The actual improving families then control tails of one fixed physical reduced state. This is why the coefficient on `log dim G(eta)` is exactly one. For `v>eta`, the target contains no unit vector. The sharper accuracy-dependent Schmidt-rank and MPS estimates remain separate.

The principal statements are in [LowDensityEntropyBound.lean](../../TNLean/MPS/AreaLaw/LowDensityEntropyBound.lean) and [PhysicalDGTreeApproximation.lean](../../TNLean/MPS/AreaLaw/PhysicalDGTreeApproximation.lean). The fixed-bandwidth convention and the local-dimension restriction are stated in [the low-energy scope note](../paper-gaps/alvv16_low_energy_family_scope.tex).

## Soft truncation

The corrected simultaneous residual bounds retain the full one-sided ten-unit range of estimated regional energies. The attained soft ground vector now bounds the difference between the original and soft ground energies. Both buffered spectral comparisons and the Hermitian MPO construction concern the same actual soft Hamiltonian. The spectral-window count includes the zero-width endpoint.

These conclusions are in [FiveRegionSoftRepresentation.lean](../../TNLean/MPS/AreaLaw/ALVV/FiveRegionSoftRepresentation.lean). The residual, scale, cutoff and cluster bond bounds remain explicit. The false printed cluster estimate is not used. Choosing all parameters with the source's advertised efficiency and proving the complete efficient-filter construction remain open; an MPO existence theorem with a corrected bound alone does not establish them. See [the soft-truncation note](../paper-gaps/alvv16_soft_regional_residuals.tex).

## Verification

The preceding continuation passed a locked full build of 15,662 jobs, both complete blueprint declaration lists, paper-gap declaration resolution, strict changed-module checks and foundation inspection of 424 changed public declarations. No Mathlib source was compiled. The new entropy and same-Hamiltonian spectral/MPO contributions also passed individual strict checks and imported foundation inspections. Their combined full build and declaration checks are pending the next coordinated integration.

All three new physical low-energy entropy modules use the default heartbeat budget. No proof placeholders, additional axioms or permanent Lean test fixtures were introduced. The temporary foundation-inspection sources were deleted. Unrelated primary-worktree changes are preserved, and the continuation has not been pushed or merged.
