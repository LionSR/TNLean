# Retire assumed correlation conclusions

Issue #1447 requires actual derivations of connected-correlation expansions and
decay estimates. `MPSTensor.connectedCorrelator_eq_sum` and
`MPSTensor.connectedCorrelator_bound` merely returned their `hdecomp` and
`hbound` assumptions. Neither had a Lean consumer outside its declaration.

Both declarations are removed without compatibility aliases. There is no
replacement theorem yet: correlation definitions, the traceless reduction,
and the quantitative transfer-map estimates remain available to build one.
The blueprint labels remain, but their statements now describe the intended
results and carry no declaration anchor or completion tag.

The pure-exponential expansion explicitly assumes diagonalizability of the
traceless restriction. The general geometric bound uses a rate strictly above
the complementary spectral radius; a Jordan block can prevent a bound at the
spectral radius itself. This completes only the retirement requirement of
#1447, not the missing spectral or decay proofs.
