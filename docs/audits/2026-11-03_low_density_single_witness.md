# One low-energy approximation with designated and global rank bounds

The official ALVV source, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines
1096–1105, uses one approximation vector for its sharper rank at a fixed
cut and its global MPS bond bound. Separate fixed-cut and global existence
statements do not by themselves prove that conclusion. The present result
constructs one normalized sequential projection product satisfying both.

## Actual construction and quantifiers

For each fixed bandwidth `eta > 0`, a coefficient is chosen before the
physical chain, positive local dimension, interactions and positive deficit.
The original Hamiltonian is the actual sum of supported positive-contraction
nearest-neighbour terms. Its minimum and canonical spectral bands are used
throughout. Set

- `g = min(min(v,eta/2)/6,1)` and `u = 1+log q+log(1/g)`;
- `a = 16+log(1/g)+log(128/delta)`;
- `b = 16+log(1/g)+log(128(L+1)/delta)`;
- `F(x) = (u^3/g + g^(-1/4) x^(3/4) u)(1+log x)`.

For every `0 < delta <= 1`, integers `1 <= Bs <= Bg` are chosen before
both the designated cut and the vector. Their logarithms are at most
`K_eta F(a)` and `K_eta F(b)`. For every designated cut and every unit
vector in the original band `G(eta-v)`, one unit vector `Phi` has

- designated-cut rank at most `dim G(eta) * Bs`;
- an open-boundary MPS representation with bond at most `dim G(eta) * Bg`;
- overlap strictly greater than `1-delta`;
- squared distance at most `delta/2`.

The physical theorem has no gap, original-band invariance, supplied family,
residual, count or sampling-success premise. It covers every positive local
dimension, boundary cuts and short or empty chains. The scalar fixed-cut
branch is the previously proved exact rank-one case.

At the designated cut, apply the actual physical fixed-cut theorem at
accuracy `delta/64`; at every other internal cut use accuracy
`delta/[64(L+1)]`. The normalized cut approximants control the actual
original marginal masses. Their bounds are respectively `delta/32` and
`delta/[32(L+1)]`, with total at most `delta/16 <= delta/8`.
The two rounded rank factors are ordered by a proved monotonicity estimate
for the same profile, not by an assumed comparison. Rounding adds at most
one to each logarithm, absorbed by increasing the fixed coefficient by one.

The actual rank schedule is `Ds` at the designated cut and `Dg` elsewhere.
The leading original marginal projections with these ranks form one reverse-
prefix product. Its normalization retains every individual rank. The exact
internal-cut factorization theorem supplies the global MPS representation
of this same vector. Endpoint cuts have rank at most one and require no
projection or fit condition.

## Shared sequential theorem

`NormalizedVariableTruncation` generalizes the existing normalized sequential
argument to a rank at each cut and a sum of the actual missing masses.
Its conclusion records the nonzero actual projection product, its normalized
unit vector, individual internal-cut ranks, strict overlap and squared error.
It reuses the existing arbitrary-projection sequential rank and squared-error
proofs. Scalar multiplication of cut coefficient matrices is explicit.

The existing public `exists_unit_mps_of_uniform_prefix_mass` signature is
unchanged. Its proof now applies the variable-rank theorem at a constant
rank, so it remains an active corollary. The other existing public signatures
in `NormalizedSequentialApproximation` are also unchanged. No compatibility
alias or second uniform normalization proof is retained.

`DesignatedCutTruncation` is the conditional marginal-mass implication used
between these two results. The physical theorem derives every one of its
mass and rank premises from the actual original-band construction.

## Source scope

The source fixes the bandwidth at lines 281–284. Positive local dimension is
the qudit convention. The source assumes polynomial full-band dimension and
inverse-polynomial requested accuracy; the proved finite-dimensional statement
allows arbitrary actual multiplicity and every `0 < delta <= 1`.
The existing capped-width estimates retain the source inverse-deficit scale
for `0 < v <= eta`, and the substitution `v = mu/log L` is valid for
`L >= 2`. The explicit regularizations preserve the fourth-root inverse-
deficit and three-quarter-power logarithmic-accuracy terms in the source
macros at lines 176–177. The coefficient on the full-band logarithmic
dimension is one. No basis construction or running time is asserted.

## Verification

Actual-name private checks use the held ordinary-built TN provider
`20cad76ebfa6e770263c4a5d5333917c5b226ed9` and its own exact QIC package
`98ba564e3c9603dc93d2173e3dc87a85ce750456`. Selected source/object pairs,
root inputs, the prebuilt Mathlib sentinel and changed-importer dependencies
are guarded. All output is confined to `/tmp`; providers and caches remain
unchanged and no Mathlib source build is started.

The new variable construction, uniform specialization, designated-mass
assembly and physical theorem pass strict checks at the default options
in 5.500, 5.348, 5.202 and 21.540 seconds respectively. All three existing
direct consumers of the uniform module pass against the changed import
closure: `MPSApproximation` in 6.016 seconds, the gapped global theorem in
9.233 seconds, and the original low-energy global theorem in 9.273 seconds.
The positive-dimension strict global theorem also passes in 9.266 seconds.
An imported five-name foundation inspection passes in 7.999 seconds with
only `propext`, `Classical.choice` and `Quot.sound`. Temporary inspection
commands are deleted after use.

Ordinary combined compilation and compiled blueprint declarations remain
integration gates. This contribution depends on the frozen positive-dimension
checkpoint and changes no companion source or dependency pin.
