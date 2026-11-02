# A corrected one-interval soft-truncation MPO

The proposed contribution constructs an operator approximation for one
regional soft replacement, including the exterior sum and scalar shift.
Its parameter choice is t = 3m, with m >= 1. The interactions are the actual
nearest-neighbour matrices, Hermitian and of norm at most one. An explicit
lower energy epsilon I <= A is assumed for the regional sum A; the source's
regional energy bracket supplies this lower bound.

With W = 3m 2^(m+1), b = 2(exp(1/3) - 1) in (0,1), and the displayed
logarithmic cluster order r, the constructed site-dependent operator tensors
have virtual dimension

    D = 1 + N q^2 + (m+1) r^2 q^r

and operator-norm error at most the requested xi > 0. The physical chain has
N+1 sites and q >= 1. The heat operators are approximated separately, then
combined by diagonal blocks. An approximate heat operator is not raised to
power m. The scalar shift stays outside the norm-one local terms.

The cluster estimate uses connected components of interaction labels and
retains the explicit energy normalization. The existing positive two-qubit
and negative forty-qubit counterexamples, and the `false-source/open` record,
are preserved. The added mathematical statement is the corrected estimate,
not the printed physical-support theorem.

This contribution does not prove the low-energy spectral comparisons, a
multiple-region construction, the unrestricted t,m approximation lemma, or
a computational running-time bound. It therefore does not close issue 9847.

## Source selection

The source-only worktree starts at exact TNLean revision
`5fc343a57d70eefd2902780107851ab9b0753a82` and retains its QICLean pin.
Twenty-five previously absent production modules are selected individually
from the preserved cluster/MPO and soft-MPO sources. Existing mathematical
files, including `ProductForm` and `TraceChainOperator`, are retained.
Their current interfaces must be used during verification. No old branch,
old generated import file, or old complete blueprint chapter is restored.

The four shared prerequisites are a separate QICLean contribution based on
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. Importing the scalar soft definition
directly removes the unnecessary soft-versus-hard dependency. The complete
selected production-source import graph contains 147 modules and no missing
imports. All 61 new public declarations across the two contributions have
matching mathematical book entries, with no missing local references.
No matching declaration headers already exist on either current base.

## Verification status and order

The TNLean modules have not been elaborated in the refreshed environment.
The preserved 2026-10-29 private evidence is historical evidence only.
New book completion markers are withheld. The worktree has no `.lake`
directory, and no ordinary build or cache mutation is performed here.

The verification order is:

1. Shared mandatory-label, union-coefficient, finite heat and scalar order
   estimates, followed by their imported foundation audit.
2. Label-path geometry, mandatory windows and the normalized tail.
3. Separated component sums, actual nearest-neighbour supports, both interval
   rank bounds, crossing-interval counting and all-cut ranks.
4. The operator-chain constructor, exact cluster MPO and normalized error.
5. Weighted operator sums, exact local sums, shifted heat approximation,
   soft approximation and the complete one-interval replacement.

The new sections satisfy their selected theorem roles. The full current-base
role checker reports 41 pre-existing mismatches outside these new sections;
those unrelated entries are not changed. No Lean test fixture is added.

The four QIC prerequisites and all seven public foundations have now passed
fresh guarded private checks. All selected existing importers above changed
current-source dependencies were re-elaborated as well. The TNLean checks
remain pending. Focused mathematical PDF excerpts were rendered twice and
visually inspected; the complete compiled-book gate remains pending.
The displayed dimension is polynomial in N and inverse accuracy for fixed
q and m; the dependence on m remains explicit and is not suppressed.
