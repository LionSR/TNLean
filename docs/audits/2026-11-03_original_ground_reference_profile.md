# An original-ground reference and one common trimming radius

The new results construct a reference directly from the original physical ground
space, including Hamiltonians with flat spectrum. One reference and one positive
radius then work in the actual interval/full-exterior coordinates for every
parent. No nearby reference space or MPS approximation is supplied as a premise.

## Source and precise scope

That passage invokes the area law to replace the original ground space by a
nearby space of polynomial bond dimension. The new reference is mutually
`1/100000`-close, a stronger fixed accuracy than the printed `10^-4`
reference. The scalar normalization and final spectral-filter arguments are
not used.

The printed trimming lemma is `lem:trimming`, lines 660–697. Its corrected
weighted reference estimate is recorded in the QICLean-owned note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf.
The new radius reserves the exact `1/1000` weighted budget used by the existing
constant-error half-sampling and trimming result. It is not asserted to equal
the printed final-accuracy threshold in `eq:algo-xi-dg`, lines 1802–1804, which
also depends on the requested accuracy and a power of the improving-family
count. No algorithm, running-time bound, or sharp inverse-gap exponent is claimed.
The known false cluster and uniform soft-energy statements are untouched.

## The original ground space, including flat spectrum

`exists_physical_ground_isOpenMPS_reference_subspace` retains the logarithmic
profile of the existing physical reference construction and its universal
constant. Its hypotheses are actual supported nearest-neighbour terms
`0 <= h_i <= I`, a spectral value mu, and the original gap implication
`z = mu or mu + gamma <= z`. Positive local dimension is explicit.

A distinct excited energy is selected internally when it exists. The old
`exists_physical_dg_isOpenMPS_reference_subspace` is then applied unchanged.
Otherwise the gap implication forces every actual eigenvalue to equal mu,
so the ground space G is the whole Hilbert space. Take U = G and B = 1.
Every cut matrix has rank at most the full configuration dimension r, and
r <= r^2. The exact cut-rank construction gives the all-vector bond ceiling
r^2 B, with zero reference error. Empty chains and one-site chains are included.
In this case r can be q^N; polynomial dependence on N and r does not assert
polynomial dependence on N alone.

The physical reference is independent of the new random tree. Its original
construction uses approximants of an orthonormal basis of G and sequential
truncation. The transitive TN source closure of the three new modules has
247 modules and no PhysicalDGTree, PhysicalDGCanonical, PhysicalDGInterleaved,
CanonicalIntervalSampling or UniformPhysicalSoftImproving ancestor. The exact
source hashes are recorded in the external manifest directory. In particular,
no MPS reference is obtained from the output whose rank it is used to control.

## Polynomial profile and the native rank square

For fixed q and gamma, set g = min(gamma,1),
u = 1 + log q + log(1/g), a0 = u^3/g, and a1 = g^(-1/4)u.
At fixed reference accuracy let

    Z = (N+1)(r+1),
    b0 = 16 + log(1/g) + log(3200000),
    C0 = exp(K*(a0+5*a1)*b0),
    p0 = ceil(K*(a0+5*a1)).

The existing `Real.reference_profile_polynomial_bound` gives
B <= C0 Z^p0. The new physical polynomial theorem chooses
C = 1 + C0^2 and P = 4 + 2*p0 before N, the Hamiltonian, and r. It constructs
that same reference with d = r^2 B and d^2 <= C Z^P.

For each parent interval J, the whole-chain reference is mapped by the actual
configuration-splitting isometry to the native interval and its full exterior.
An internal prefix of J has two boundaries against the whole chain, so the
correct common rank is bRef = d^2, not d. This is the existing
`schmidtRank_cutEnvVector_interval_reference_le` result. No additional collar
factor is required, since the global reference is mapped directly to the actual
parent interval. Mutual closeness is preserved by that same isometry.

## Radius and candidate size are separate

The one common threshold is

    xi = 1/[1000*d*sqrt(N+1)] > 0.

The existing uniform-radius theorem gives

    xi*sqrt(kCuts*bRef) <= 1/1000       whenever kCuts <= N.

There is no candidate-basis dimension in this loss budget. The proof also derives

    xi^(-2) = 10^6*bRef*(N+1) <= 10^6*C*Z^(P+1).

Candidate/image dimension is a different quantity. The existing weighted-rank
and finite-span MPS results use the coarse ceiling

    B_out(M) = 10^6*bRef*(N+1)*M^2.

The physical profile returns its numerical polynomial bound for every natural M.
Substitution of an actual parent's candidate count, and its dimension estimate
such as card(F)*Smax^2, remains a separate consumer. This batch does not assume
or construct that parent's sampled output.
