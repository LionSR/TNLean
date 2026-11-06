# Literal finite refinement of the same physical candidate

The sequence is the actual repeated raw-filter-image and collective trim
of the given initial interval subspace. It is not a sequence of independently
chosen approximations. The operator is the original physical raw filter,
the threshold and reference are fixed throughout, and the target remains
the full original global ground space.

The dimension of every iterate is bounded by the initial dimension.
Every positive iterate has actual recorded spanning vectors with count
at most that dimension and weighted rank xi^2 rank at most the same bound.
No unchanged per-vector bond bound is assigned to their entire span.

For every requested error rho in (0,1], the actual corrected error recurrence
reaches rho after finitely many steps. A further step guarantees a positive
terminal iterate. Its native image is close to the same original target,
and its dimension and actual recorded generators retain the uniform bounds.

The physical reference and threshold budgets remain explicit inputs.
The threshold has not yet been identified with one used earlier to construct
the initial tree. The next common-radius construction must use the same
positive threshold in both the tree and this final refinement. Automatic
reference selection, final Ritz extraction, the printed iteration count,
adaptive sampling probability and running time are separate obligations.
The normalized recurrence correction is recorded in
`docs/paper-gaps/alvv16_final_filter_gain.tex`.
