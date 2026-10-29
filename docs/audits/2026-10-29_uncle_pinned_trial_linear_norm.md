# A derived linear norm bound for actual one-pinned-wall trials

Issue #10286, native tracker #7685. Stacked after #10320 and the actual
Gram bounds from #10317. Source: arXiv:1210.6613, proof of Lemma
lowenergystates, `Papers/1210.6613/UncleHMPS.tex:1289–1296`.

## Actual rate, not a supplied state estimate

`UnclePinnedTrialNorm.lean` proves that the actual five-segment trial with
first moving interval of length one has squared norm at most C*s, where s
is the other moving interval length. The constant is uniform in all three
uniform padding lengths. A length-one wall interval contains exactly its
one physical R letter; the other interval remains the actual L-wall sum.

The hypotheses are the source unital normalizations of A and B, a faithful
stationary dual density for B, and strict mixed B/A spectral damping.
There is no hypothesis on the trial norm, endpoint energy, positivity of a
leading generic coefficient, continuous gauge, or a rate to be established.
The result holds for arbitrary R and L under these normalized-block inputs.

## Finite derivation

The source one-wall Gram analysis supplies an actual rectangular wall-map
operator-norm bound C*s. The fixed first wall map at length one is bounded
by the trace of its actual finite Gram matrix; adding one gives a positive
constant without imposing a nonzero-wall assumption. QICLean's unital CP
contraction bounds every power of the normalized A/B transfers by one.
Thus the actual five-map contraction has norm at most K*s.

The existing exact finite transfer identity identifies the actual trial's
squared norm with the real algebraic operator trace of that contraction.
Expanding the trace on matrix units bounds its modulus by a^2*K*s, since
every matrix unit has operator norm one and each matrix entry is bounded
by operator norm. This uses the existing trace expansion and matrix-unit
norm lemmas; no spectral/asymptotic trace estimate is assumed.

## Remaining endpoint assembly

For the source R endpoints, the corresponding globally pinned trials have
lengths (N,1,3N-1,N+1,N) and (2N,1,2N-1,N+1,N). The L endpoints use the
swapped blocks/walls after cyclic trace rotation. The preceding actual
cyclic restriction norm partition and explicit pinned residuals must still
be combined with these coordinate identities to conclude the full source
trial energy O(N). That conclusion is not asserted merely from this norm
bound. Norm growth of the two-wall trial, ground-sector overlaps, algebraic
genericity and the final variational conclusion remain separate.

## Verification

No local Lean invocation, compilation or build was run, as requested.
This is a source-written draft candidate with Blueprint notready. Source
inspection, import generation, formatting, prose, line-width/integrity and
diff checks do not establish Lean acceptance. No placeholders, axioms,
parallel predicates or persistent Lean fixtures are added.
