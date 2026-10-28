# Verification of viable-set and Gaussian approximation results

The integrated development at commit
`7860acb87da32b1ec46e630b49de28299ca42b2f` has passed the ordinary full-library
build, all twelve changed imported foundation fixtures, and the compiled
blueprint declaration check. The foundation fixtures examine 120 distinct
declarations and allow only `propext`, `Classical.choice` and `Quot.sound`.
This verification does not establish the full successive viable-set algorithm.

## Mathematical conclusions verified

- Independent columnwise bond trimming, composed with the size-trimming family,
  gives polynomial cardinality and polynomial bond dimension before the ground
  energy and vector are supplied. The radius is the corrected quadratic radius
  `(48L)² r(L)`, and the size constants retain the library constant-cut bound and
  corrected matrix-net exponent.
- Deterministic application of left factors of an approximate ground projection
  derives support, cardinality, bond dimensions and the `4η` viability error from
  a half-viable input. The empty-cut initial family and the final-span conclusion
  are also proved.
- Finite uniform matrix moments give an exceptional-sample fraction bound and
  explicit existence of a sample approximating the true mean. These results do
  not assert the sharper variance-sensitive Bernstein inequality.
- Exact Gaussian interval masses give a finite quadrature with explicit node
  count and operator-norm error. The Hermitian propagator specialization derives
  its Lipschitz estimate.
- One fixed product of two interval layers has simultaneous operator-Schmidt
  bounds at every cut; finite weighted sums retain the corresponding cardinality
  factor. Explicit grid blocks and disjoint boundary buffers are constructed.
- Projected evolutions on supplied disjoint regions are constructed and assembled
  into one global norm estimate. This auxiliary statement still requires the
  physical block decomposition and its localization estimates.
- The Hastings area-law bound admits a simultaneous logarithmic estimate for its
  factorization constant, chosen uniformly in chain length and physical data.

The individual audits give the source comparisons and the precise theorem names.
The published LVV sampling theorem's ground-energy dependence is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`; the unrestricted Gaussian
replacement remains a construction to finish, not an inference from the original
power sampler.

## Ordinary verification

The source worktree was seeded from exact fully warmed main
`856cfe29955d1192c956626632695bc4d8b40587`, with QICLean fixed at
`c97ffd63d9b52bdec7191d25aca66b9af7a2f872`. The integrated full build completed
14,972 jobs. Its cache step reported no downloads and reused the 8,943
decompressed Mathlib artifacts. Mathlib was not rebuilt from source.

All twelve fixtures then ran against the ordinary compiled modules, with the
strict options of `scripts/ci_lean_checks.py` and warnings treated as errors.
Blueprint/source synchronization generated the complete declaration list, the
pinned diagram dependency was fetched, and `leanblueprint checkdecls` returned
success. The latter command is silent when declarations are present; its exit
status, rather than the absence of diagnostics alone, records success.

The completion marks in the new trimming, quadrature, grid and interval-layer
sections now refer to these checked auxiliary results. The sampled-projector
construction, its sharper concentration theorem and the final LVV induction
remain open. No remote branch or pull request has been published or merged.
