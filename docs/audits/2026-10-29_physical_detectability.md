# Detectability for a nearest-neighbour projection chain

The actual even and odd products are constructed from the original supported
bond projections. No commuting layers, noncommutation count, reordered
Hamiltonian, or detectability operator is supplied as an assumption.

The source is ALVV, arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, `def:DLO`,
`lem:dl` and `lem:dl-converse`, lines 1496–1537. The local terms are orthogonal
projections, exactly as in `def:DLO`. The general positive-contraction
reduction discussed at lines 1457–1460 is not part of this contribution.

## Statements and proofs

For (H=\sum_i h_i), let (P_{\mathrm{odd}}) and (P_{\mathrm{even}})
be the products of the complementary projections on odd and even bonds,
numbered from one. The constructed operator is

\[
\operatorname{DL}(H)=P_{\mathrm{even}}P_{\mathrm{odd}}.
\]

Disjoint support gives commutation within each parity. In the actual ordering
of all odd terms followed by all even terms, a noncommuting bond must be one
of the two adjacent bonds. The proof counts these neighbours, including
endpoints and padded zero terms, rather than assuming a degree bound. The
sum and product in this ordering are identified with the original (H) and
the constructed operator.

The generic QICLean detectability lemma then gives, for every vector (psi),

\[
\langle\operatorname{DL}(H)\psi,H\operatorname{DL}(H)\psi\rangle
\le4\bigl(\|\psi\|^2-\|\operatorname{DL}(H)\psi\|^2\bigr).
\]

The actual commuting parity layers give the converse, for every unit vector,

\[
\|\operatorname{DL}(H)\psi\|^2\ge1-3\langle\psi,H\psi\rangle.
\]

The constant three and the unrestricted unit-vector conclusion are inherited
from the proved QICLean converse; they strengthen the displayed source
constant four and eigenvector restriction.

Every vector in the actual kernel of (H) is killed by each bond projection.
Both parity products therefore fix the whole kernel. Their self-adjointness
shows that the detectability operator preserves inner products with every
kernel vector, and hence preserves the kernel's orthogonal complement. No
uniqueness is used for these assertions.

For the final corollary, the original matrix satisfies the full-system gap
inequality (H\ge\gamma(I-|\Gamma\rangle\langle\Gamma|)), with a unit
ground vector (H\Gamma=0) and (gamma>0). Combining this gap with the
energy estimate proves

\[
\|\operatorname{DL}(H)\psi\|^2\le\frac4{4+\gamma}
\qquad(\|\psi\|=1,\ \psi\perp\Gamma).
\]

The denominator is retained. No upper bound on the gap, regional uniqueness,
or positive spectral separation for a truncated operator is assumed.

## Verification

The ordinary read-only provider was TNLean proof-source commit
`c9516b84af92761e3863f632188b5655f43cd35f`, at its documentation-only successor
`6cc25953751a659592a3d211b95d37e3e0a575ee`, with QICLean
`92ceaab6274f9cb9bf226c20d144c4d0d83a5f83`. Direct imported sources and all
associated ordinary artifact files were hashed before and after each check.
The provider commit, clean status and exact companion revision were also
guarded. The new module was compiled separately into a private temporary
directory, using the production strict options and warnings as errors.
No provider, dependency, or cache file was modified or copied.

The final source passed strict checking in 6.834 seconds. A separate imported
check of both definitions and all seven public theorems found only
`propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes,
additional axioms, or kernel-bypass tactics. The foundation commands and
output remain under `/tmp`; no permanent Lean fixture is added.

The private evidence is recorded in
`/tmp/tnlean-alvv-detectability-checks.json` and
`/tmp/tnlean-alvv-detectability-foundations.json`. The module's checked SHA256 is
`e019fced23fdca1f2551923e5cd9fdebef0087a86bd321944a471d14b43734ae`.
Canonical combined builds and book checks remain integration gates.

## Remaining source requirements

The following are not consequences asserted by this contribution:

* construction of the range projections for arbitrary positive local
  contractions, with preserved common kernel and a proved gap comparison;
* construction of the actual regional collapsed-layer Hamiltonian, its
  identical detectability product, and its ground-space and gap comparison;
* the regional operator-Schmidt-rank bound;
* the soft-truncation spectral comparison, a corrected sufficient cluster
  estimate, or the low-density and sampled-tree constructions.

In particular, the contraction corollary does not justify applying a
unique-ground-state upper-gap bound to a truncated or degenerate region.

## Ordinary combined verification

The contribution is included in mathematical revision
`e46d137d7784b6b4abf6155f68d1cb8e6dbc2cd1`. The full 15,099-job build,
strict changed-source checks, imported public-foundation audit and all
blueprint, prose, integrity and timing checks passed. No Mathlib source
was compiled. The combined audit is
`2026-10-29_verified_physical_detectability_and_periodic_pairs.md`.
The complete local record is `/tmp/tnlean-detectability-periodic-gates.json`.
