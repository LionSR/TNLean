# Sharp AKLV approximation by actual sequential truncation

## Mathematical statement

There are universal constants $A\ge1$ and $C>0$, chosen before the
chain, local dimension, gap and requested accuracy. Let
$H=\sum_{i=0}^{L-2}h_i$ be a nearest-neighbour sum whose terms are supported
positive contractions. Suppose that $\Omega$ is a unit ground vector of
energy $\mu$, that
$H-\mu I\ge g(I-|\Omega\rangle\langle\Omega|)$ for $g>0$, and that
$\mu+g$ is in the spectrum. Thus $g$ is an actual first excitation,
rather than merely a supplied lower bound.

For $0<\epsilon\le1$, put

$$
 \rho=\frac{\epsilon^2}{16(L+1)},\qquad
 u=1+\log q+\log(1/g),\qquad
 z=\log\frac{2048(L+1)}{\epsilon^2},\qquad
 s_0=\lceil Au^2/g\rceil.
$$

The theorem `exists_aklv_sharp_physical_sequential_mps_approximation`
constructs the ordered product of the leading $D$-dimensional marginal
spectral projections, in the order $L-1,L-2,\ldots,1$. The product applied
to $\Omega$ is nonzero. Its actual normalization is an open-boundary
matrix product state of bond dimension at most $D$ and norm distance at
most $\epsilon$ from $\Omega$, where

$$
 \log D\le C\left[\frac{u^3}{g}+
       \left(\frac{z^3}{g}\right)^{1/4}(u+\log(z+1))\right].
$$

This is the fourth-root logarithmic dependence used in AKLV,
arXiv:1301.1162v1, Section 7, lines 1503–1517. The official local source
is `/tmp/tnlean-aklv-official-source-20261029/source/1dfrustrated34.tex`,
with SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
No running-time statement is made.

## Actual filters and the two scalar regimes

The parameters remain those of the frozen accuracy-dependent construction:
$m=\lceil(z^3/g)^{1/4}\rceil$, $s=s_0+2m$,
$t=T(g)+16z$, and $\ell=\lceil z\sqrt{(2t+s)/g}\rceil$.
The rank budget is exactly

$$
 D=\max\left\{
 D_0[q(\ell+1)]^{32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)},
 q^{s-\lfloor s/2\rfloor}\right\},\qquad
 D_0=[q(s_0^2+1)]^{32(2s_0+1)}.
$$

All comparisons needed for this expression are proved from the selected
parameters. If $z\le s_0$, then $\ell\le66s_0^2$, and its logarithmic
rank cost is at most $10000\log D_0$. If $s_0\le z$, then $m<z+1$,
$2t+s\le4225z$, and $\ell\le66m^2$. In either quadratic degree regime,
$\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1\le76n$ for the
corresponding scale $n$. The actual initial rank satisfies
$\log D_0\le C_0(A)u^3/g$, where
$C_0(A)=100(A+1)(8+2\log(A+1))$.
A sufficient final coefficient is $C(A)=10001C_0(A)+800000$.
The square-root-degree choice is preserved; no enlarged square degree or
exponential-in-degree rank estimate is substituted.

At every fitting cut the retained approximant is the actual polynomial
image of the actual initialized vector. The corresponding predicate
retains its polynomial, clipped Hamiltonian, phase, normalization and
physical regional minima. If the enlarged window does not fit, the exact
vector $\Omega$ supplies the boundary alternative using
$q^{\min\{k,L-k\}}$. Thus no fit premise remains, including at the
endpoint cuts and in short chains. The two distinct spectral values
force $q\ge2$ and $L>0$. The unique-ground endpoint-unitary argument then
derives $g\le1$ from the original interaction. No extra local-dimension
or upper-gap premise is used by the final physical theorem.

## From cut approximants to one matrix product state

For unit vectors, squared distance at most $\rho$ gives squared overlap
at least $1-\rho$. QICLean's existing homogeneous Ky Fan overlap bound
therefore gives discarded marginal mass at most $\rho$ at each cut.
The general sequential leading-eigenprojection theorem gives squared
error at most $(L-1)\rho\le\epsilon^2/16$ for its actual ordered product.
Normalization at most doubles distance to the unit target, and scalar
normalization preserves its matrix product representation.

Only the general overlap, sequential truncation and normalization
inequalities are used. The proof does not call an independent area law
or matrix product approximation existence theorem. The existing general
normalization inequality is imported from `MPSApproximation.lean`; its
proof uses only the triangle inequality and reverse triangle inequality.

The source support, energy normalization and index corrections remain
recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`. The actual
first-excited-energy hypothesis remains explicit. This completes the
sharp approximation route from the physical filters. It does not complete
the separate entropy summation from the coherent changing-target sequence,
or an unrestricted all-window formulation of the source robustness theorem.

## Verification

All eight production modules passed strict actual-name private checks
against mathematical TNLean snapshot
`da3ab8dcc9f9149cbbdcc56cae817ff783825f24`, documentation-only successor
`f93bc77b3dddcc292125eea18b96af153225251b`, and exact QIC package
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`.
The frozen private parents are TNLean commits
`6d94b8b122624fb1ac0a8774293fda2a31509aa6` and
`3fed6139cb9092258a3e6f9bf96f71fdcc6b543b`, and QIC helper
`aa5ede2ad00ab2106c5106549caa743d078b0722`.
Every selected imported source and ordinary object is guarded, as are the
frozen own-parent source and private-object pairs. The final expanded
provider guard covers 350 imported modules. All six selected import roots
report zero pending dependencies.

The strict checks disable automatic implicit arguments, enable Mathlib's
standard linters, and treat warnings as errors. The final physical modules
checked in 15.96 and 4.51 seconds; earlier exact-source checks of the other
six modules were all below eight seconds. An imported foundation audit of
all 18 new public declarations passed in 3.77 seconds and found only
`propext`, `Classical.choice`, and `Quot.sound`, or a subset.
The audit commands and outputs are temporary, and no fixture is committed.

The new blueprint chapter covers all 18 new public declarations. A scoped
tactic-pattern scan found no repeated blocks at its default thresholds.
The fourth-root ceiling comparison and quadratic-degree exponent bound
are factored once and reused. Reader-facing prose and proof-integrity
checks are recorded with the frozen patch. The source-gap document also
moves its premature document terminator to the end so that the already
present coherent-sequence and accuracy-window sections are rendered.

Only own source files and temporary private outputs were written. No
provider source, build object or cache was changed or copied, no Mathlib
source was built, and no ordinary build was queued. Ordinary target/full
builds and compiled blueprint verification remain integration gates.
Generated aggregators and chapter registration are excluded. The new
chapter belongs after `ch35_aklv_accuracy_window.tex`.
