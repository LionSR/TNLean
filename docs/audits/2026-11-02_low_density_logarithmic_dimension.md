# The physical low-density logarithmic dimension estimate

For each fixed positive bandwidth, one constant precedes the chain
length, local dimension, interactions, interval and requested positive
deficit. The theorem constructs an actual `3/200`-viable regional
subspace for the original canonical target `G(eta - v)`, with dimension
at most

    dim G(eta) * exp(K_eta / v * (1 + log q + log(1 + 1/v))³).

The numerical base `q * ceil(exp 100)` is chosen before applying the
actual minimum construction. Its logarithm is at most `log q + 101`.
For `0 < v ≤ eta`, the half-bandwidth cap changes the inverse-width
estimate only by a factor depending on the fixed bandwidth. If `v > eta`,
the original spectral target is proved to be zero and the zero regional
space supplies the conclusion. Equality `v = eta` belongs to the
nonzero-bandwidth branch and is not declared an empty target.

The local dimension remains `q ≥ 2`, and the retained region is an
actual physical interval. There is no supplied spectral gap, improving
family, residual, probability estimate or finite-termination premise.
The low-density assumption can replace the actual multiplicity
`dim G(eta)` by its source upper bound. Substitution `v = mu / log L`
for `L ≥ 2` gives an explicit positive-logarithm version of ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1107–1128.
The bandwidth dependence and interval scope remain visible in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

The generic count proof now belongs to the QICLean companion library.
The six old public signatures in `PolynomialFilterParameters` are
byte-identical; their proofs reuse the shared ceiling and count results.
The six-module affected import closure was re-elaborated in order before
checking the new physical corollary, rather than reusing an existing
importer built against the changed source.

All checks used immutable TNLean
`71db89efb903199a223ce22a9704d5e5ba3698f4` and its own QICLean package
`602972abe8a0463ee04c586e029cd73d8ebc894b`. The final corollary passed
strict actual-name private checking in 11.463 seconds, guarding 567
selected source/object pairs. The combined imported inspection of twelve
public declarations passed in 8.705 seconds with only standard axioms;
the temporary diagnostic source was removed. The unchanged regional
family regression took 28.703 seconds; this warning is retained, below
the 50-second limit. Every other checked production module took less
than 25 seconds. No Mathlib source or build cache was changed.

Blueprint source synchronization and reverse coverage, reader-facing
prose and whitespace checks passed. The role check retains exactly the
41 inherited discrepancies and introduces none. Ordinary combined
compilation and compiled blueprint checking remain integration checks.
Entropy, sharper accuracy-dependent tails, global MPS and running-time
conclusions remain separate.
