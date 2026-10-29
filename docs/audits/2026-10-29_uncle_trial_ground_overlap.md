# Actual ground-sector overlaps of the uncle trial

Issue #10286, native tracker #7685. Source: arXiv:1210.6613, proof of
Lemma lowenergystates item 2, `Papers/1210.6613/UncleHMPS.tex:1277–1287`.

## Derived actual overlap, not a premise

`UncleTrialOverlap.lean` writes an exact finite mixed-transfer trace for
`mpvState C (6*N+1)` against the actual source two-wall trial. Each wall
map contracts its actual single-domain-wall word against the corresponding
pure word of C. The canonical five-segment configuration equivalence is
promoted from the existing finite-norm proof for this actual second
consumer. No new configuration structure or overlap predicate is added.

The two exterior A segments join under the operator trace. The actual
separations are 2N in A and 2N-1 in B. This retains the numbered trial
coordinates rather than copying a literal schematic exponent from the
source's diagram.

## Bounds and source hypotheses

Splitting a wall interval at its initial or final site gives two exact
mixed-map recurrences. Compare against the left pure sector with the
initial-site recurrence and against the right sector with the final-site
recurrence. The self-transfer is unital and therefore contracts matrix
operator norms. Strict mixed spectral radius gives geometric power decay,
hence a uniform bound on the other powers. The actual finite wall mixed
map is consequently bounded by its interval length times a fixed constant.
The one-letter constant is the norm of the actual finite linear map, not
an assumed state, overlap or asymptotic rate.

Both actual source overlaps are bounded by C*N^2*r^N with 0<r<1. For
comparison with A the damped B separation is 2N-1>=N; comparison with B
uses the joined A separation 2N>=N. The trace functional is continuous on
the actual finite-dimensional rectangular matrix endomorphism space.
Its fixed norm controls the algebraic operator trace by the derived map
bound. Choosing r<z<1 and using summability of n^2*(r/z)^n absorbs the
polynomial factor and derives an actual C*z^N bound.

The A bound requires only unital A and mixed B/A damping; the B bound
requires only unital B and mixed A/B damping. No perturbation injectivity,
faithful-density, genericity or supplied overlap rate is needed for these
upper bounds alone. These are explicit intermediate source-normalization
conditions, not a completed source gaplessness theorem.

## Norm choice and remaining argument

Mixed spectral radius is originally defined with the companion library's
operator-space norm. The overlap estimates use Euclidean matrix operator
norms. Both continuous endomorphism algebras identify algebraically with
the same finite-dimensional linear endomorphism algebra. The existing
`AlgEquiv.quasispectrum_eq` theorem identifies their spectral radii without
an additional norm-equivalence premise. Independent API/source inspection
confirmed this normalization route; compilation remains necessary.

The quadratic norm lower bound, the use of source genericity to make its
leading coefficient positive, and removal of the full ground projection
in the final variational argument remain separate. No full gaplessness or
infinite-volume spectral conclusion is claimed here.

## Verification

No local Lean invocation, compilation or build was run, as requested.
This is source-written draft proof text with Blueprint notready. Import,
prose, deterministic LaTeX format, tactic scan, line-width/integrity,
whitespace and conflict-marker checks do not establish Lean acceptance.
The existing upstream stack has hosted repairs in progress. No placeholders,
axioms, parallel predicates or persistent Lean fixtures are added.
