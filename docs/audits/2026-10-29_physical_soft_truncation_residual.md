# The physical soft residual on the original spectral window

The actual soft-truncated Hamiltonian is constructed by applying the source's
finite exponential soft-truncation function to the shifted original regional
Hamiltonian. On the whole original low-energy spectral window, the difference
from the original Hamiltonian satisfies an exponentially small operator-norm
bound. The physical moment estimate is proved internally through the existing
regional moment theorem, rather than supplied as a hypothesis.

The source is ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`,
lines 1175–1255. This contribution takes the scale equal to the positive
integer order. It is a corrected original-window residual; it does not assert
the false first uniform energy estimate documented in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.

## Actual operators and quantifiers

Let (H=\sum_i h_i) be the original supported positive unit
nearest-neighbour Hamiltonian, and let (A_J) be its literal internal sum
on any interval (J=[p,r)), with (0\le p\le r\le L). The existing
physical moment construction supplies attained regional minima, a common
unit regional minimizer, and a centered original Hamiltonian

\[
H_c=H-SI
\]

with an attained ground energy (E_0\in[0,2]). All these choices precede
the approximate regional energy (e_J-10\le\varepsilon'_J\le e_J),
the bandwidth (\eta\ge0), the positive integer (m), and every vector.
The new theorem constructs the literal matrix

\[
\widetilde H_{m,m}
 =H-A_J+\varepsilon'_J I+h_{m,m}(A_J-\varepsilon'_J I).
\]

It is Hermitian and satisfies (\widetilde H_{m,m}\le H). On the actual
closed original spectral space

\[
G_\eta=\mathbf1_{(-\infty,E_0+\eta]}(H_c)\mathcal H,
\]

the theorem proves

\[
\left\|(H-\widetilde H_{m,m})|_{G_\eta}\right\|
\le80\exp\left(\frac{17+\eta}{8}-\frac m{16}\right).
\]

There is no gap, ground-space-rank, supplied minimum, supplied moment, or
supplied residual assumption. Empty and endpoint intervals are included.
The scalar function is applied by the continuous functional calculus; no
efficient matrix product operator representation is asserted.

## Functional-calculus proof

Set (U=A_J-\varepsilon'_J I\ge0) and (d_m(x)=x-h_{m,m}(x)).
The checked QICLean scalar exponential-weight estimate gives

\[
0\le d_m(x)e^{-x/8}\le16e^{-m/16}\qquad(x\ge0).
\]

The proof transfers this scalar bound to the actual positive matrix (U).
It explicitly proves the factorization

\[
d_m(U)=B_me^{U/8},\qquad B_m=d_m(U)e^{-U/8},
\qquad\|B_m\|\le16e^{-m/16}.
\]

Both factors are functions of the same (U). The public existing identity
`Matrix.IsHermitian.exp_smul_eq_cfc` is reused, together with Mathlib's
multiplicative functional calculus and its norm bound. The physical moment
theorem supplies

\[
\|e^{U/8}|_{G_\eta}\|\le5e^{(17+\eta)/8}.
\]

Composition of the two actual restricted operators yields the residual
bound. No order comparison between powers or exponentials of noncommuting
operators occurs. The order (h_{m,m}(U)\le U) gives both
\(\widetilde H_{m,m}\le H\) and Hermiticity.

## Verification

The isolated source branch starts at checked TNLean
`908de62f163b9505312b914a2fad03dafa23948d`. The read-only provider was its
documentation-only successor `e6785a190e5ffe603dd9ca238451696c70bdc7b5`,
with exact QICLean package `01f237e808b03fb0612ceb617f9bca2c407da927`.
The source checkout was updated without copying build artifacts or
initializing a Lake environment. Direct imported sources and ordinary
artifact files were hashed before and after private module checks.

The final new module passed strict checking, with warnings as errors, in
5.614 seconds. Its source SHA256 is
`76c0758708baa07faf0a8a72e494f18115fd53efb1c113829d9f75838616aecf`.
An independent import of that actual compiled module found only `propext`,
`Classical.choice`, and `Quot.sound` for the public theorem. There are no
proof holes or kernel-bypass tactics. Foundation commands and outputs remain
under `/tmp`; no permanent Lean fixture is added.

Evidence is recorded in `/tmp/tnlean-alvv-soft-residual-checks.json` and
`/tmp/tnlean-alvv-soft-residual-foundations.json`. The provider, dependency
caches and package sources were unchanged. No Mathlib source compilation
was invoked. Canonical combined builds and book checks remain integration
gates.

The reverse spectral comparison, an independent scale and order, the corrected
cluster estimate, efficient tensor representation, and the low-density and
sampled-tree constructions remain separate. In particular, this theorem is
not a completion of the unrestricted source soft-truncation lemma.
