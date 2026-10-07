# Explicit preparation scales

The quantitative statements supplement
[arXiv:2307.01696](https://arxiv.org/html/2307.01696), rather than deriving a
uniform exponential rate from its qualitative inhomogeneous definition.

## Mathematical statements

- `exists_isPreparedInDepth_inhomogeneous_le_min_of_rate` takes the actual
  scale `q = ceil(a log(N/ε) + b)`, with `a >= max(k,1)/r` and an offset
  including a minimum usable scale `L`. The rate is required only when the
  chosen scale satisfies `L <= q <= N`; the conclusion is physical depth
  `T <= C(d,D) min(N,q)` and error at most `ε`.
- `exists_isPreparedInDepth_inhomogeneous_le_min_of_ordered_mixing` derives
  the rate from ordered products of the actual tensors and exposes the
  sufficient coefficient `1/r`. This is not an optimal circuit-depth claim.
- `exists_isPreparedInDepth_allLength_of_slope` retains every prescribed
  `a > ξ/2`, with the gauge and positive spectral bound explicit, while
  removing the equal-block divisibility restriction. Its offset includes
  the eventual injectivity length. No rate below that length is asserted.
- All all-length statements retain nonzero periodic targets. Exact
  preparation handles `q > N`, including noninjective short rings. The
  existing pure-log theorem keeps its zero-depth one-site branch.
- The strict slope endpoint and the spectral-bound endpoint `t = 0` are
  not added. The existing zero-subleading-spectrum theorem remains separate.

## Shared constructions

`RemainderBlocks.lean` now owns the existing `remainderBlockLengths` and
`sum_remainderBlockLengths` declarations, formerly in
`AllLengthPolynomialAccuracy.lean`, together with their pointwise bounds.
Their names are unchanged. The polynomial, prescribed-slope and ordered
mixing constructions share this partition, without importing the polynomial
accuracy theorem into the generic rate conversion.

`exists_isPairApproximable_of_ordered_mixing` is the substantive pair-rate
statement formerly proved locally inside the logarithmic-depth theorem.
Both physical consumers reuse it. `VaryingBondChain.ofChain` records the
constant-bond construction once. Existing logarithmic and eventual public
signatures are preserved.

The scalar estimate is proved through the existing
`mul_mul_exp_neg_le_of_log_le`. The original uniform-rate theorem reuses it,
with sufficient coefficient `max(k,1)/r` instead of `(k+1)/r`.
