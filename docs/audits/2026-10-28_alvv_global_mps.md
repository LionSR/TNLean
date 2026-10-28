# One normalized matrix product approximant for the full ground space

The principal declaration is
`TNLean.MPS.AreaLaw.exists_physical_dg_normalized_isOpenMPS_approximation`.
It concerns the global approximation part of ALVV,
[arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), Theorem 4.9,
`local_alg_arxiv_v2.tex`, lines 1080–1086. The source TeX has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The assumptions are the original positive nearest-neighbour terms bounded by
the identity, two spectral values $\mu<\nu$, and a supplied gap $\gamma>0$
above the full original ground space $G$. Neither a marginal-tail bound nor a
collection of approximants is assumed.

There is one universal $K>0$ before every chain, local dimension,
Hamiltonian, gap and accuracy. Put $r=\dim G$, $g=\min(\gamma,1)$ and
$u=1+\log q+\log(1/g)$. For each $0<\delta\le1$, define

$$
 b=16+\log(1/g)+\log\bigl(16(L+1)/\delta\bigr).
$$

The theorem selects an integer $B\ge1$ before the ground vector, with

$$
 \log B\le K\left(\frac{u^3}{g}+g^{-1/4}b^{3/4}u\right)(1+\log b).
$$

Every original unit vector $\psi\in G$ has a single original unit vector
$\Phi$ with an open-boundary matrix product representation of bond dimension
at most $rB$, absolute overlap at least $1-\delta$, and squared norm error
at most $\delta/2$. Thus the degeneracy factor is linear and the rank bounds
hold simultaneously at all prefix cuts of that same $\Phi$.

For the proof, fix $\delta_c=\delta/(16(L+1))$. At each cut the physical
fixed-cut theorem constructs a normalized approximant of absolute overlap
at least $1-\delta_c$ and rank at most a common integer
$D=r\lceil e^E\rceil$. The maximal Schmidt-overlap theorem bounds the original
marginal's leading $D$ eigenvalue mass below by $(1-\delta_c)^2$. Its discarded
mass is consequently at most $2\delta_c$.

These cut-dependent approximants are used only for that spectral estimate.
The final unnormalized vector is the single sequential projection product
$\Phi_0=P_1\cdots P_{L-1}\psi$, where each $P_k$ lifts the leading spectral
projection of the original prefix marginal. The existing squared-error
sequential-truncation theorem gives $\|\Phi_0-\psi\|^2\le\delta/8$ and the
open matrix product representation with bond bound $D$. This makes
$\Phi_0$ nonzero. Normalizing it at most doubles the norm error and leaves
the bond bound unchanged. Rounding the common exponential costs at most one
in its logarithm, which is absorbed into the universal constant.

The normalized-gap comparison and the independent-parameter correction are
recorded in [the parameter note](../paper-gaps/alvv16_approximation_parameters.tex).
For $0<\gamma\le1$ the explicit estimate has the source's inverse-gap cubic
local logarithms and quarter-power gap, three-quarter-power logarithmic
accuracy term. Larger supplied gaps use $g=1$; comparison with the unrestricted
printed gap dependence remains open. The low-energy theorem and the binary-tree
algorithm are separate results.

The combined contribution is integrated on exact TNLean main revision
`c457d2be30e12c770fb7807e822f0ca72739f498`, preserving its removal of theorem
fixtures and its unrelated mathematical additions. Frozen integration
`0341b256badfec30365411d5b77923777fc06208` passes the guarded global target
(9632 jobs), the full library (14996 jobs), all 38 changed-source strict checks
and five existing regression checks with the unchanged 45-second limit.
Actual imported declarations from the ordinary object files pass local
foundation inspection with exactly `propext`, `Classical.choice` and
`Quot.sound`. Pinned blueprint dependencies, source/declaration
synchronization and compiled declaration checks pass. Mathlib artifacts are
prebuilt, and the selected QICLean revision is unchanged. No permanent theorem
test files are included. The subsequent documentation changes state the
source's second-eigenvalue assumption and the remaining capped-gap comparison;
they do not alter any mathematical signature or proof body.
