# AKLV favorable scalar parameters

`AKLV/FavorableParameters.lean` proves a uniform scalar choice for the sharp
AKLV polynomial rank budget and squared Chebyshev shrinking coefficient.
It reuses `Real.exists_dg_scalar_parameters` with \(C_H=2081/2\) and \(M=0\).
No new logarithmic absorption argument or numerical ceiling construction is
introduced.

## Quantifiers and bounds

One universal constant \(A\ge21\) is chosen before the local dimension and gap.
For every integer \(q\ge2\) and \(0<g\le1\), put

\[
u=1+\log q+\log(1/g),\qquad s=\lceil Au^2/g\rceil,\qquad \ell=s^2.
\]

The theorem retains both ceiling bounds, proves \(s\ge21\) and
\(s\ge\log(1/g)\), and establishes the exact natural-number identities
\(\ell/s=s\) and \(\lfloor\sqrt\ell\rfloor=s\).
Define

\[
t_0=1024+16\log(1/g),\quad R=2t_0+s,\quad
D=\bigl(q(s^2+1)\bigr)^{32(2s+1)},\quad
D_{\rm aux}=(qs^2)^{22s}.
\]

The checked arithmetic gives

\[
0<R\le2081s,\qquad D\le D_{\rm aux}^{9}.
\]

Indeed \(R\le2048+33s\le2081s\), while
\(q(s^2+1)\le(qs^2)^2\) and \(64(2s+1)\le198s\).
For the actual squared shrinking expression

\[
\delta=4\exp\left(-4\ell\sqrt{(9g/10)/R}\right)>0,
\]

monotonicity gives

\[
\delta\le\delta_{\rm aux}
 :=4\exp\left(-4s^2\sqrt{(4g/5)/R}\right).
\]

Since \(D_{\rm aux}\ge1\), the existing joint scalar tradeoff yields

\[
D\delta\le D_{\rm aux}^{12}\delta_{\rm aux}
 \le10^{-5}<1/256.
\]

The same rank comparison gives the explicit uniform bound

\[
\log D\le198(A+1)\bigl(6+2\log(A+1)\bigr)\,u^3/g.
\]

All logarithms of the inverse gap remain visible. The constant is universal;
it does not depend on \(q\), \(g\), chain length, or a Hamiltonian.

## Source and physical scope

The source is [AKLV, arXiv:1301.1162v1](https://arxiv.org/abs/1301.1162v1),
Section 6.1, the parameter choice after Theorem 6.1 and the proof of Lemma 6.3,
`1dfrustrated34.tex`, lines 1016–1048. The official source SHA-256 is
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
This theorem is a scalar auxiliary. It does not assert that a finite chain has
room for the chosen window, construct a physical filter or normalized output,
or prove the varying-target recursion or entropy bound.

The logarithmic-threshold physical results were frozen separately. This scalar
proof neither imports nor applies them. In particular, the older
polynomial-threshold filter is not used at \(t_0\). A physical application at
that threshold requires integration and use of the stronger logarithmic theorem.

## Verification

Production SHA-256:
`6ece3306d11ef8ae85bf9f815b2760ff0ddb5bbde489b4d2ced84a6f958e0745`.

The actual named module passes strict private checking in 3.66 seconds with
strict implicit arguments, Mathlib standard linters, warnings as errors and
the default heartbeat limit. Imported manual foundation inspection passes in
2.08 seconds and reports only `propext`, `Classical.choice`, and `Quot.sound`.
The scoped tactic scan finds no repeated blocks at its default thresholds;
the two uses of the ceiling-scale logarithm comparison are recorded in the
shared ledger. No permanent inspection fixture is added.

Checks use the fully built TNLean mathematical snapshot
`5cec1958d1a56d1f20cfdbd1161ef946a410f41c`, its documentation-only successor
`d0ddc83b8bafec64a83cf450e2232cc60f9aa8f0`, and unchanged QICLean pin
`cc9e79084d26336c95e843c13928a3963a9debb2`. The sole repository import is the
checked `PolynomialFilterParameters` module; the remaining imports are prebuilt
Mathlib artifacts. Its source and object hashes, the manifest and toolchain
are guarded before and after checking. A fresh private namespace contains no
modified module from the unintegrated logarithmic contribution.

The worktree contains source only, with no `.lake` directory. No provider,
dependency pin, shared cache or Mathlib source is changed. No ordinary build is
queued. Ordinary module and compiled-blueprint checks remain with common
integration. Place the separate chapter after `ch35_aklv_clipped_filter.tex`;
no chapter registration or generated aggregator change is included.
