# Physical low-energy comparison at every positive accuracy

The declaration
`TNLean.MPS.AreaLaw.exists_five_region_physical_low_energy_closeness`
constructs both one-sided comparisons between the original and clipped
physical low-energy spaces at shifted cutoffs. The source passages are
ALVV, [arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2),
`lem:hard-trunc`, lines 927–969, and `t:aisgapless`, lines 1027–1041,
of `local_alg_arxiv_v2.tex`. The official TeX source has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The Hamiltonian is the original positive nearest-neighbour sum with local
terms bounded by the identity. For every bandwidth $\eta>0$, cutoff shift $w>0$
and error $\delta>0$, the theorem chooses the explicit threshold

$$
C_*=288e^{11/8},\qquad
z_*=\min\{1,\delta w^2/[2(6+\eta)]\},\qquad
t=21+\eta+8\log(C_*/z_*).
$$

The regional energies are certified minima: a common unit vector attains
each one, and each regional matrix minus its specified energy is positive
semidefinite. The original centered ground energy is likewise certified by
a unit eigenvector and a global attained lower bound, with $0\le E_0\le4$.
Neither spectral bases, a gap, a residual estimate, nor a numerical smallness
condition is supplied as an additional hypothesis.

The spaces below $E_0+\eta$ for either matrix are $\delta$-close to the spaces
below $E_0+\eta+w$ for the other. The directions are separate and use different
cutoffs; no same-cutoff equality or equal-rank conclusion is asserted.
The actual residual $\xi$ is at most one and satisfies
$2(6+\eta)\xi\le\delta w^2$. The existing finite spectral-window perturbation
estimate applies in both orders with window half-width $\xi$. Its ceiling
bound uses only $E_0\le4$ and $\xi\le1$.

This proves the physical shifted-cutoff comparison needed for the
low-density construction. The nested improving polynomial family, its
quantitative count and the dyadic minimal-dimension bootstrap remain open.
The binary-tree construction and the correction of the efficient
cluster-expansion argument are separate tasks. The selected dependency
remains QICLean `af7e5c90650e5ddb06c2befac508df97fd20b2e3`; the unpublished
nested-target companion contribution is not assumed by this proof.

Frozen contribution `1da9db7921eb856be498e6c00339ac78c9b74ab4` passes the
guarded ordinary target (3385 jobs), the complete library (14997 jobs), both
strict changed-source checks with the unchanged 45-second limit, and local
foundation inspection of the actual imported ordinary declaration. The latter
gives exactly `propext`, `Classical.choice` and `Quot.sound`. Pinned diagram
dependencies, source/declaration comparison, reverse coverage and compiled
blueprint declaration checks all pass. Mathlib artifacts are prebuilt and the
selected companion revision is unchanged. No permanent theorem-test files are
included. The completion marks state the shifted-cutoff result above; they do
not assert the low-density area law or the merge-tree construction.
