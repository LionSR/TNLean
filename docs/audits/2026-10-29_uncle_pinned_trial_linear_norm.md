# A derived linear energy bound for the actual uncle trial

Issue #10286, native tracker #7685. Stacked after #10320 and the actual
Gram bounds from #10317. Source: arXiv:1210.6613, proof of Lemma
lowenergystates, `Papers/1210.6613/UncleHMPS.tex:1289–1296`.

## Actual rates and hypotheses

`UnclePinnedTrialNorm.lean` proves both complementary estimates for the
actual five-segment trial: squared norm at most C*s for lengths
(p,1,q,s,t), and at most C*r for lengths (p,r,q,1,t). Constants are
uniform in all three padding lengths. A length-one wall interval contains
its one physical wall letter; the other interval remains the actual
single-domain-wall sum.

`UncleEndpointEnergyBound.lean` combines these estimates with explicit
coordinates for all four globally pinned states and derives the actual
source trial energy at length 6N+1 to be at most C*N for every N>0.
The hypotheses are unital normalization of both blocks, faithful stationary
dual densities for both blocks, and strict mixed damping in both directions.
No perturbation injectivity or generic nonvanishing is required for this
upper bound alone. There is no premise asserting a trial-norm rate,
energy rate, energy support, or an asymptotic factorization.

## Finite derivation

The actual one-wall Gram analysis bounds the moving rectangular wall map
linearly in its interval length. The fixed wall map at length one is
bounded by its actual finite Gram trace. Adding one gives a positive
constant without a nonzero-wall assumption. QICLean's unital CP contraction
bounds every power of the diagonal transfers by one. The exact finite norm
identity is the real algebraic operator trace of the resulting five-map
contraction. Expanding on matrix units bounds this trace by the square
of the first virtual dimension times the actual map norm.

The four globally pinned states use the following segment lengths, in the
original physical order, at bonds N-1, 2N, 4N-1 and 5N respectively:

- (N,1,3N-1,N+1,N);
- (2N,1,2N-1,N+1,N);
- (N,N+1,2N-1,1,2N);
- (N,N+1,3N-1,1,N).

All total lengths equal 6N+1 for N>0. The coordinate theorem proves that
every actual cyclic restriction of each globally pinned state equals the
previously derived local pinned endpoint vector. Segment addition and
the two boundary-segment coordinate lemmas are public because this is
their second actual consumer. No extra physical translation is assumed.

The actual source energy is bounded by the averaged sum of squared norms
of these four endpoint vectors. The exact cyclic restriction norm partition
identifies each average with its global pinned-state squared norm. Therefore
the energy is at most 4*C*(N+1), hence at most 8*C*N. The empty physical
alphabet is treated directly: the positive-length source configuration
space is empty and the trial is zero.

## Remaining gaplessness argument

This supplies the source linear energy upper bound, as source-written Lean
proof text. The quadratic lower bound for the actual two-wall trial norm,
small overlaps with the two ground sectors, the use of genericity for a
positive leading coefficient and the final variational conclusion remain
separate. The energy estimate alone does not prove gaplessness or complete
the source lemma.

## Verification

No local Lean invocation, compilation or build was run, as requested.
The latest hosted run on the earlier narrow draft stopped in an inherited
Gram recurrence before reaching this module. Its concrete diagnostics and
the trial-localization diagnostics have source repairs in this branch;
a new hosted run must validate them. This is a source-written draft with
Blueprint notready. Import generation, formatting, committed-head prose,
line-width/integrity and diff checks do not establish Lean acceptance.
No placeholders, axioms, parallel predicates or persistent Lean fixtures
are added.
