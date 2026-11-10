# Normalized physical ground-state approximation

The principal declaration is
`TNLean.MPS.AreaLaw.exists_physical_dg_interval_normalized_approximation`.
It concerns the fixed-cut part of ALVV,
[arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), Theorem 4.9,
`local_alg_arxiv_v2.tex`, lines 1048–1085. The official TeX source has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The Hamiltonian is the original sum of supported positive nearest-neighbour
terms bounded by the identity. The hypotheses give two spectral values
$\mu<\nu$, a supplied gap $\gamma>0$, and no spectrum in
$(\mu,\mu+\gamma)$. The target $G$ is the full original ground space.
No viable subspace, rank bound, overlap, spectral basis, tensor representation
or truncation residual is supplied as a hypothesis.

One universal constant $K>0$ precedes every chain, local dimension,
Hamiltonian, gap, interval, accuracy and ground vector. For
$g=\min(\gamma,1)$, $u=1+\log q+\log(1/g)$ and
$a=16+\log(1/g)+\log(1/\delta)$, every original unit vector $\psi\in G$
and every $0<\delta\le1$ have an original unit approximant $\phi$ satisfying

$$
 |\langle\phi,\psi\rangle|\ge1-\delta,
 \qquad
 \log\operatorname{SR}_{J:J^c}(\phi)
 \le\log(\dim G)+
 K\left(\frac{u^3}{g}+g^{-1/4}a^{3/4}u\right)(1+\log a).
$$

The rank is evaluated in the actual finite-product coordinates of the interval
and its complement. It is not the rank of a separately supplied coordinate
matrix. Prefix intervals include the source's fixed cuts. The result also
covers empty and short intervals.

The initial $0.015$-viable subspace $W_0$ is selected before the accuracy and
vector. Its dimension is bounded by $(\dim G)D_0^{24}$. The independently
chosen hard threshold and polynomial window give a family of $D_1^2$
operators, and the enlarged subspace has dimension at most
$(\dim G)D_0^{24}D_1^2$. In particular, the degeneracy factor is linear.
The proof transfers $W_0$ to the actual clipped target at error $0.04$,
improves it to error at most $\delta/5$, and transfers back to the original
ground space at error at most $\delta/2$. The existing viable-subspace
projection theorem constructs a normalized physical vector with this rank
bound. No approximation hypothesis is substituted for that construction.

For $0<\gamma\le1$, the explicit estimate has the source's inverse-gap cubic
local logarithms and the quarter-power gap, three-quarter-power logarithmic
accuracy term. The factor $1+\log a$ displays the additional logarithmic
correction. For larger supplied gaps the bound uses $g=1$; the comparison
with the unrestricted printed gap dependence remains open. The independent
parameter correction, the explicit failure regime for the printed
prescription, and this gap normalization are recorded in
[the parameter note](../paper-gaps/alvv16_approximation_parameters.tex).
The global matrix product state conclusion is a separate subsequent
construction from these fixed-cut bounds. Its single sequentially truncated
vector is described in `2026-10-28_alvv_global_mps.md`; separate fixed-cut
approximants alone do not establish that conclusion.

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
