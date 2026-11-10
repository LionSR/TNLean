# Corrected rank of the actual regional frustration-free truncation

## Statement and source correction

`operatorSchmidtRank_physicalFrustrationFreeTruncation_le` proves
$\operatorname{OSR}(\widetilde H_J)\le q^2+3$ at every site cut for the
actual regional operator

$$
 \widetilde H_J=H_{\mathrm{out}}+(I-Q_0)+(I-Q_1).
$$

Here $H_{\mathrm{out}}$ is the actual sum of original bonds not contained
in the interval $J=[a,b)$, and $Q_0,Q_1$ are the actual ordered parity
products of the interval-restricted family. The only hypothesis is the
original nearest-neighbour support condition on each $h_i$. There is no
supplied decomposition, rank, projection, positivity, state, uniqueness or
gap hypothesis. The same operator is bounded at all cuts. The statement
includes all natural local dimensions, including zero, the empty chain,
empty intervals and endpoint cuts; no order assumption on $a,b$ is needed.

This is the corrected rank assertion associated with ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1568. The printed $q^2+2$
claim remains false. Its existing nondegenerate eight-qubit counterexample,
with unique frustration-free ground vector and gap one both before and
after truncation, is preserved in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`. The
counterexample has rank seven at $q=2$ and thus saturates the corrected
universal count. No Lean counterexample theorem is asserted by this patch,
and no source-labelled formalization of the false printed claim is added.

## Derived parity ranks and actual exterior sums

In positive local dimension, the actual ordered parity prefixes are
followed directly. Before the unique possible crossing bond each selected
complementary factor has rank at most one. The crossing factor has rank
at most $q^2$, derived from its two-site support. Each subsequent factor
again has rank at most one. The parity not containing that crossing bond
has rank at most one throughout. Hence

$$
 \operatorname{OSR}(Q_0)+\operatorname{OSR}(Q_1)\le q^2+1.
$$

The prefix at full length is definitionally the existing physical parity
product. No crossing marker, product decomposition or rank family is
supplied. Commutation, projections and positivity are not needed for
these rank estimates.

The actual outside sum is split into left bonds, right bonds, and the
possible crossing bond, using the original support and interval tests.
There can be at most one crossing bond. If that outside term vanishes,
$2I+H_{\mathrm{out}}$ has rank at most two: combine the scalar with the
left sum and retain the right sum. Adding the two parity products gives
$q^2+3$.

If an outside bond crosses, the truncated interval lies entirely to one
side of the cut. Both actual regional complements are supported on that
side and can be combined with its actual outside sum. The two resulting
one-sided operators and the crossing bond give the stronger $q^2+2$ count
in this case. The final theorem takes the common bound $q^2+3$.

For zero local dimension on a nonempty chain the configuration space is
empty and all matrices vanish. For the empty chain the original bond sum
is zero and both parity products are the identity, so the actual truncated
Hamiltonian is again zero. This derives the degenerate cases directly;
it does not apply the positive-dimensional parity-sum count to them.

## Shared support and rank proofs

The contribution includes the already strictly checked complementary-product
support lemma in `Circuit/SupportedComplementProduct.lean`, with source
hash unchanged from the supplied proof. `PhysicalParityProductSupport.lean`
retains the supplied actual parity-support proof and adds support of the
actual interval-restricted parity product in that interval.
The existing private `intervalBondRestriction_supported` in
`PhysicalFrustrationFreeTruncation.lean` is exposed with unchanged statement
and proof, avoiding a second support argument. No new core import is added.

The companion contribution moves the existing elementary Kronecker rank-one
proof from `OneMarkerWeightedSchmidtRank.lean` into the small
`OperatorSchmidtProducts.lean` leaf, together with the identity specialization.
The old private duplicate is removed and its one-marker consumer uses the
shared proof. The widely imported `OperatorSchmidtBounds.lean` core is
unchanged. The generic identities include empty local factors and require
only `Finite` on the second factor. The unfinished singleton-complement
proposal is not included or used.

## Verification

Strict actual-name private checks use the fully checked TN mathematical
source `28e38efedb8621056c907c8ad20e1edd24003a20`, documentation successor
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96`, and exact matching QIC package
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`. The selected ordinary source
and object guard covers 94 modules, with zero pending dependencies in all
four selected import roots. Own changed source and private objects are
separately guarded. The unchanged supplied circuit-support source and
private object are also guarded and reused read-only; no artifact is copied.

The generic product leaf and modified one-marker module checked in 2.18
and 2.48 seconds. The actual parity ranks checked in 5.82 seconds, the
extended parity support in 3.76 seconds, the existing module with its
support-helper exposure in 7.60 seconds, and the corrected all-dimension
rank theorem in 16.53 seconds. The unchanged circuit-support source has
supplied strict evidence of 4.846 seconds. All checks disable automatic
implicit arguments, enable Mathlib's standard linters, and treat warnings
as errors. No heartbeat option was increased. Temporary failed elaborations
were corrected by explicit support arguments and by taking the finite
complement before coercion to a set.

A temporary imported foundation inspection of eight public TN declarations,
the two new companion results and the changed one-marker consumer passed
in 16.89 seconds. Only `propext`, `Classical.choice`, and `Quot.sound`, or
subsets, occur. The audit commands and diagnostic sources remain temporary;
no fixture is committed. The new TN chapter covers all eight public TN
results, and the existing QIC algebraic-rank entry covers both new generic
results. Source integrity, reader-facing prose and dependency-label checks
accompany the frozen patches.

Only own source worktrees and temporary private outputs were written.
No provider source, ordinary object or cache was edited or copied,
no Mathlib source was built, and no ordinary build was queued. Ordinary
build and compiled blueprint checks remain integration gates. Generated
aggregators and chapter registration are excluded. The new TN chapter
belongs after `ch35_physical_detectability.tex`. The full ALVV programme
and unrelated physical spectral statements are not declared complete here.
