# A physical regional exponential moment

For an arbitrary prescribed interval (J=[p,r)) of a positive unit
nearest-neighbour chain, the original regional Hamiltonian (A_J) satisfies
a dimension-independent exponential-moment bound on the original low-energy
window. The regional minimum and the full centered ground energy are
constructed from the physical terms, before the approximate regional energy,
window width, or any vector is specified.

The source comparison is ALVV, arXiv:1602.08828v2, `def:soft-trunc` and
`lem:exp-approx`, lines 1175–1255. The first printed uniform energy estimate
is false; its exact mathematical counterexample is documented in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`. The theorem
proved here is an auxiliary exponential-moment bound. It does not assert
the printed estimate or the full two-sided soft spectral comparison.

## Statement and construction

Split the chain into the left interval, (J), and the right interval.
The actual crossing set has cardinality at most two. The existing disjoint
regional construction supplies attained minima (e_i), a common unit
minimizer, and an attained ground energy (E_0in[0,2]) for

\[
H_c=H-\left(\sum_i e_i\right)I.
\]

Repeated cuts express this literal partition using the existing five-region
construction with two empty regions. No length or endpoint restriction is
added. The regional minimum (e_J) is attained by the same common unit vector.

For every (e_J-10le\varepsilon'_Jle e_J) and (\etage0), let

\[
G_\eta=\mathbf1_{(-\infty,E_0+\eta]}(H_c)\mathcal H.
\]

The new theorem proves the actual operator-norm inequality

\[
\left\|\left.e^{(A_J-\varepsilon'_J I)/8}\right|_{G_\eta}\right\|
\le5e^{(17+\eta)/8}.
\]

All choices defining (H_c), its actual eigenbasis, the attained minima,
and (E_0) precede the two universally quantified parameters. The bound
applies to the whole original spectral space, including a degenerate ground
space. There is no gap or ground-space-rank hypothesis, and no supplied
moment, residual, spectral comparison, or regional minimum.

## Reuse of the weighted restriction

The existing theorem
`exists_nearestNeighbour_weighted_low_restriction` in
`RegionalTruncationResidual.lean` is made public. Its entire source, including
the statement, docstring and proof, is byte-identical to the checked provider
except for removing `private` from this declaration. Its proof is not copied.

Write (b\le2) for the crossing count, (C=2b\le4),

\[
e=E_0+\eta,\qquad u=e+C+1\le7+\eta,
\qquad Q=\mathbf1_{[e_J+u,\infty)}(A_J).
\]

The existing physical nearest-neighbour imaginary-time estimate constructs
the actual map (e^{(A_J-(e_J+u)I)/8}Q|_{G_\eta}), whose norm is at most

\[
\frac C{u-e-C}=C.
\]

The structural commutation and lower-order conditions needed for that
theorem are derived from the actual disconnected regional sums. The
complementary low part of the same weight has norm at most one by spectral
functional calculus. Adding the two parts gives (1+C\le5). The remaining
scalar shift contributes at most (e^{(17+\eta)/8}).

Every exponential in this argument is a function of the original (A_J).
The proof makes no inference from order of noncommuting operators to order
of their powers or exponentials.

## Verification and scope

The read-only provider was clean TNLean
`1604ed2ffc831a4f6afba70150024edd3ca19d6c`, a documentation-only successor of
checked proof source `e46d137d7784b6b4abf6155f68d1cb8e6dbc2cd1`. The exact
companion package was QICLean `afcf986970504f1d370e475f0617256ca83b160d`.
The package environment, imported sources and ordinary artifact files were
guarded; changed modules were compiled separately into private temporary
outputs. No provider or dependency cache was modified or copied.

The promoted weighted-restriction module passed strict checking in 11.930
seconds. The final new module passed in 16.786 seconds, with source SHA256
`10ef8fe2a170365e796c190f6589e1dd5d4a2253fd73dcc2e1dba6cd2fe4a26c`.
Both public theorems were then checked by importing the actual separately
compiled module. Their only axioms are `propext`, `Classical.choice`, and
`Quot.sound`. There are no proof holes or kernel-bypass tactics. The local
foundation commands remain under `/tmp`, outside the repository.

Evidence is recorded in `/tmp/tnlean-alvv-soft-moment-checks.json` and
`/tmp/tnlean-alvv-soft-moment-foundations.json`. Canonical combined builds
and book checks remain integration gates.

The scalar weighted soft-truncation estimate can subsequently be transferred
through the continuous functional calculus of (A_J-\varepsilon'_J I).
That transfer and the resulting soft residual are not part of this frozen
contribution. The reverse comparison on actual soft-truncated low-energy
vectors also remains separate. No completion of the full source spectral
comparison, efficient approximation, low-density induction, or sampled tree
is claimed.

## Completed integration checks

The integrated mathematical revision
`908de62f163b9505312b914a2fad03dafa23948d`, with QICLean pinned to
`01f237e808b03fb0612ceb617f9bca2c407da927`, passed the full 15,106-job
library build and strict checks. The imported foundation audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Source synchronization,
compiled blueprint declaration checks, prose, proof-integrity and timing
checks also passed. No full-build job reached the 25-second warning
threshold. Mathlib was not rebuilt. The complete local check record is
`/tmp/tnlean-moments-initialization-gates.json`.
