# Sharp MPS approximation for an original low-energy band

Let `H` be the actual sum of supported positive-contraction nearest-neighbour
terms, let `lambda0` be its minimum eigenvalue, and put
`G(c) = 1_(-infinity,lambda0+c](H) Hspace`. For each fixed bandwidth
`eta > 0`, the new results choose constants before the chain, its local
dimension, the prescribed interval, the positive deficit, the accuracy,
and the vector. They retain the explicit restriction `q >= 2`.

The source is ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines
1096–1105. Assumption (LD), lines 281–284, declares the bandwidth fixed.
The source macros at lines 176–177 place a soft-O around the whole sum
of the initial and accuracy-dependent contributions. The present bounds
make their logarithmic regularizations explicit. These are scoped physical
results; the unrestricted source entry must not be identified with a
statement that silently adds the local-dimension restriction. The scope
is recorded in `docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

## Constructed spaces and vectors

`PhysicalLowDensityApproximation` selects one actual initial viable space
`W0` before the requested accuracy. It obtains this space from the proved
physical minimum-dimension construction at deficit `b/2`, where
`b = min(v, eta/2)`. For a long prescribed interval, the inward-cut collar
construction and the actual independent-scale polynomial family refine
this same space. For a short interval the original unit vector supplies
its exact finite-dimensional cut rank. Thus empty, boundary and short
intervals are included.

The two original/clipped spectral comparisons each have loss `delta/100`.
The conditional companion composition lemma gives input error at most
`1/20`, refined error at most `delta/5`, and original lower-band error at
most `21 delta/50 <= delta/2`. All its family and comparison premises are
derived from the physical construction. The normalized output is extracted
from the same actual image of `W0`. No gap or invariance of an original
low-energy band is imposed.

`PhysicalLowDensitySharpApproximation` bounds the logarithm of the actual
rank, retaining coefficient exactly one on `log dim G(eta)`. Set

- `g = min(min(v,eta/2)/6,1)`;
- `u = 1 + log q + log(1/g)`;
- `a = 16 + log(1/g) + log(1/delta)`.

The rank bound is

`log rank <= log dim G(eta) + K_eta (u^3/g + g^(-1/4) a^(3/4) u) (1+log a)`.

The initial exponent is bounded by `8 Kb u^3/g`. The actual polynomial
count at degree `ell^2`, with fourth-root window length, supplies the second
term. Its rank factors and its comparison errors use the same actual
clipped polynomial. No polynomial count or rank is a hypothesis.

`PhysicalLowDensityGlobalApproximation` applies the cut estimate at
`delta/[16(L+1)]` and rounds one uniform rank factor upward before the
vector is chosen. The output is one actual sequential product of leading
marginal projections, followed by normalization. It has bond dimension
`dim G(eta) * B`, overlap at least `1-delta`, and squared distance at most
`delta/2`. The bound on `log B` has the same profile with
`a = 16 + log(1/g) + log(16(L+1)/delta)`.

For the source range `0 < v <= eta`, the existing proved
`Real.capped_initial_filter_width_bounds` gives
`1/g <= max(12,eta)/v` and
`log(1/g) <= log(max(12,eta)) + log(1+1/v)`.
These inequalities identify the displayed profile with the source's
fourth-root inverse-deficit and three-quarter-power logarithmic-accuracy
terms, up to the explicitly retained logarithmic regularizations. The
substitution `v = mu/log L` recovers the source low-density variable for
`L >= 2`. No running-time assertion is made.

## Shared proofs and preserved statements

The existing normalization-distance proof moves unchanged from
`MPSApproximation` to the companion `UnitNormalizationDistance` module.
The generic inequality no longer has a TN-owned duplicate or compatibility
alias. All direct approximation consumers are checked against the shared
identity. The two existing logarithmic rounding proofs also move unchanged
to the companion `LogRankRounding` module.

The existing regional overlap-to-marginal-mass and normalized sequential
projection proofs move unchanged from `PhysicalDGGlobalApproximation` to
`NormalizedSequentialApproximation`. The prefix-interval identity moves
unchanged from `MPSApproximation` to that same thin module, retaining its
public name. This module imports no independent area-law or MPS-existence
result. The gapped global approximation reuses it with its public statement
unchanged. All twelve remaining public theorem signatures in
`MPSApproximation` are also unchanged.

## Verification

Private checks use the exact ordinary-built provider TN
`478e8a08f8d97cec4064070a29170a0953362d3e` and its own QIC package
`9578336a5123a76001a1218e271132091c828de2`. The guarded checker verifies
selected source, object and build-input hashes, the prebuilt Mathlib
sentinel, and the changed-importer closure; outputs are confined to `/tmp`.
No provider or dependency cache is modified, and no Mathlib source build
is started. The new mathematical modules use the default heartbeat budget.

The independent-scale approximation, sharp logarithmic estimate and global
MPS modules passed strict actual-name checks in 22.445, 12.932 and 9.375
seconds respectively before final shared-helper formatting. The final global recheck passed in
9.069 seconds. The shared helper and every selected affected consumer pass
again after that final formatting change. Imported foundation inspection
passed in 8.596 seconds and covers 23 public declarations: the new public
results, moved public helpers, and the existing public approximation
statements. Only `propext`, `Classical.choice` and `Quot.sound` occur.
Temporary inspection commands are deleted after use.

Ordinary combined compilation and compiled blueprint declaration checking
remain integration gates. No broader completion of the six-paper programme
is asserted by these results.
