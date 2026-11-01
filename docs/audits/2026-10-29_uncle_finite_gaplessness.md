# Finite-volume uncle variational assembly

Source: arXiv:1210.6613, `Papers/1210.6613/UncleHMPS.tex`, Theorem
`thm:gapless` and proof at lines 1154–1314. The injective-perturbation
standing assumption appears at lines 1017–1018 and 1041–1042.

The public theorem concerns the actual uncle Hamiltonian on 6N+1 sites.
For almost every pair of walls, if its actual boundary letters span the
full matrix algebra, every positive threshold eventually bounds a positive
actual eigenvalue. The canonical input consists of unital diagonal block
transfers and faithful stationary trace-one dual densities. No diagonal
injectivity, primitivity, mixed transfer gap, trial norm growth, overlap,
projection bound, energy estimate or spectral conclusion is assumed.

The actual source trial has generic quadratic squared-norm lower growth,
linear energy and exponentially small overlaps against both periodic
states. Their actual Gram limits make the squared ground-sector projection
tend to zero. The exact finite kernel theorem identifies those sectors
with the full kernel. Subtracting the actual kernel projection preserves
energy and gives the strict Rayleigh inequality required for an actual
positive eigenvalue below any prescribed positive threshold.

A classical case split removes an unnecessary fixed perturbation witness
from the public statement. If there is a full-span pair, use it only to
derive the block estimates and generic norm growth; then apply the actual
kernel theorem to the varied pair's own full-span hypothesis. If no such
pair exists, the conditional conclusion is vacuous. This does not assert
that arbitrary walls are almost surely injective perturbations.

The exceptional norm-coefficient sets are proper quadratic radicals, not
an assumed genericity condition. Their Haar-null conclusion applies under
one additive Haar measure on the entire pair space, with no independence
or supplied product-measure premise.

This is finite-volume gaplessness in the source canonical normalization.
It does not construct a GNS infinite-volume Hamiltonian or prove that its
spectrum is the entire nonnegative real axis. Blueprint entries remain
notready pending hosted proof acceptance. Native source/import/prose,
formatting and diff checks do not substitute for Lean compilation. No local
Lean invocation, build, elaboration or checkdecls was run, as requested.
