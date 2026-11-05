# An actual orthonormal MPS basis for an approximate inner band

For each fixed bandwidth `eta > 0`, the physical theorem chooses its
coefficient before the chain, positive local dimension, actual supported
positive-contraction interactions, positive deficit and requested accuracy.
All bands are the canonical spectral bands of the original raw sum of the
interactions, at its actual minimum eigenvalue. No gap, reference family,
approximation oracle, sampling event or raw-band invariance is imposed.

Let `T = G(eta-v)`, `n = dim T`, and `r = dim G(eta)`. For
`0 < delta <= 1`, choose per-basis accuracy
`epsilon = delta/[8(n+1)]`. The already proved physical single-witness
approximation supplies one integer factor `B` before any basis or vector.
Its logarithm has the sharp profile

`K_eta (u^3/g + g^(-1/4) a^(3/4) u)(1+log a)`,

where `g = min(min(v,eta/2)/6,1)`, `u = 1+log q+log(1/g)` and
`a = 16+log(1/g)+log(1024(L+1)(n+1)/delta)`.
The coefficient is uniform before the physical data. The additional
`log(n+1)` is explicit; no compatibility of independently selected
constants is assumed.

The target basis is the actual `stdOrthonormalBasis` of `T`, selected after
`B`. Each of its unit vectors is approximated by an actual normalized MPS
from the proved construction, with bond at most `rB` and squared distance
at most `epsilon/2`. These are full vector distances with the original
complex phases, not merely magnitudes of inner products. The theorem
retains this family `phi`, its individual norm/MPS/error bounds, the
actual basis-defined map `F`, and its actual range `V`.

Finite Cauchy–Schwarz and Parseval bound the error of `F` from inclusion
by the sum of the squared basis errors, at most `delta/16 < 1`.
The companion basis-image theorem therefore proves that `F` is injective,
that `V = span(range phi)`, and that `dim V = n <= r`.
Projection minimality and the existing equal-dimensional symmetry give
closeness between `V` and `T` in both directions. Enlarging the projecting
space from `T` to `G(eta)` gives `IsCloseTo delta (G eta) V`: every candidate
vector projects well onto the outer band. The opposite, generally false
claim that `V` approximates the whole larger outer band is not asserted.

Every vector of this same range is a linear combination of the `n`
recorded MPS. The finite-span cut-rank theorem gives the honest common
bond bound `n*r*B` for every vector of `V`. The actual standard orthonormal
basis of `V` is then returned with that bound. Orthogonalization is not
claimed to preserve the original generator bond `rB`.

If `n=0`, the actual map has zero range and both basis index sets are
empty. The same finite sums and dimension proof apply. Scalar local
spaces and empty chains are included by the proved positive-dimension
approximation theorem. No nonzero-inner-band premise is added.

## Source identification

This is the mathematical basis-existence consequence described in ALVV,
arXiv:1602.08828v2, introductory line 288, from the area-law/MPS existence
statement `thm:al-ld` at lines 1096–1105. Its number of output vectors is
exactly the inner-band dimension, bounded by the outer dimension. It does
not claim the number, advertised energy threshold, success probability or
quasipolynomial running time of the distinct algorithm `t:alg2`, lines
1869–1874. Its vectors need not be energy eigenvectors or belong exactly
to the original inner band; the precise assertion is the proved two-sided
subspace closeness. The physical algorithm remains a separate task.

Under the source's polynomial outer multiplicity, the extra factor `n`
is polynomial and `log(n+1)` is logarithmic in the chain length. The
fixed-bandwidth, capped-width comparison is unchanged and documented in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

## Shared finite-span proof

The new indexed-family corollary in `OpenMPSSpan` reduces to its existing
finite-set theorem and uses the cardinality of the actual image. Repeated
or zero family members are allowed. The existing full-interval span theorem
now actively uses this corollary instead of repeating its image/cardinality
argument. All existing public signatures in both modules are unchanged.
The native physical basis proof uses the existing linear equivalence that
forgets the Euclidean norm, preserving the actual full-chain coefficients.
No independent area-law or MPS-existence theorem is imported.

## Verification

Checks use the immutable ordinary-built TN provider
`20cad76ebfa6e770263c4a5d5333917c5b226ed9` and its own exact QIC package
`98ba564e3c9603dc93d2173e3dc87a85ce750456`, with explicit frozen-parent
source/object overrides for the single-witness construction. Selected
sources, objects, root inputs, the prebuilt Mathlib sentinel and changed
importer dependencies are guarded. All new outputs are under `/tmp`;
no provider, package or cache is modified and no Mathlib source build runs.

Default actual-name strict checks pass for the companion generic module
in 4.541 seconds, indexed finite-span helper in 4.663 seconds, full-interval
consumer in 5.123 seconds, and physical basis theorem in 10.185 seconds.
The imported six-name foundation inspection passes in 19.720 seconds,
with only `propext`, `Classical.choice` and `Quot.sound`. Temporary
inspection commands are deleted after use. Source/book correspondence,
reader prose, role checks, integrity and whitespace checks are completed
before freezing. Ordinary combined compilation and compiled blueprint
declarations remain integration gates.
