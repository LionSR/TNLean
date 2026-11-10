# An explicit count for literal physical refinement

The physical raw-filter-and-trim recurrence now reaches projection error rho
after the explicit positive number ceil((4/c) log(1/rho)) + 1 of steps,
where c = gamma/(||H|| − mu). The dimension and recorded-generator bounds
hold at that same literal iterate of the original candidate space.

The proof reuses the numerical logarithmic recurrence estimate. The existing
existential theorem retains its exact signature and is now a direct corollary
of the stronger statement; the qualitative-convergence proof is removed.

This count is in terms of projection error rho. It does not establish the
printed count expressed in terms of final energy tolerance in ALVV Algorithm 1.
The physical reference and common trimming threshold remain explicit inputs
of this auxiliary theorem and are chosen separately in the automatic construction.
