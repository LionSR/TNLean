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

## Verification

The two actual modules passed separate strict package-linter checks with
warnings as errors against immutable ordinary TNLean
994a1963ab36a234e1b02689a13bf1da965573b2 and its own QICLean
67a788fdb9660c16c70c97bf36be5da6bbbaa348. The full ordinary provider had
passed 15,627 jobs, including rebuilt affected importer objects. The generic
literal-iteration module passed in 5.517 seconds over 264 selected source-object
pairs; the physical finite-convergence module passed in 6.276 seconds over
270 pairs. Every selected source, object, root input and prebuilt Mathlib
hash remained fixed before and after checking.

An imported foundation inspection covers all six public declarations,
including the two inline simp theorems. It passed in 5.397 seconds over
271 selected pairs, using only propext, Classical.choice and Quot.sound.
The temporary source was deleted. There is no permanent fixture or Lake directory. No provider
or cache was mutated, no compiled artifacts were copied and Mathlib was
not rebuilt. Combined ordinary library, regression, compiled blueprint and
timing gates remain required after integration.
