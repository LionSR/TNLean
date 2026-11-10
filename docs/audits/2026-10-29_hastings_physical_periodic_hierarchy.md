# The periodic physical hierarchy in Hastings' local construction

This contribution recovers the physical periodic hierarchy preserved at TNLean
commit `1659116509dc8cec5d4a2aec8ddd131cc88da31d`. It constructs the actual
truncated local Gaussian filters, the assignment to neighbouring supersites,
the compressed spectral windows, and a nearby retained unit vector. Its final
dimension bound uses the gap of the original Hamiltonian. The local residual
condition (low) remains an explicit hypothesis for the chosen ground vector.

## Source and scope

The source is Hastings, *Solving gapped Hamiltonians locally*,
[arXiv:cond-mat/0508554v3](https://arxiv.org/abs/cond-mat/0508554v3),
`References/cond-mat_0508554/proj3new.tex`, SHA256
`0c87b269f4b7d351462dc9c51b1a4460f6029f0dd2598c1e65f944aaf35f79cd`.

| Requirement | Source passage | Proved statement and remaining restriction |
|---|---|---|
| Local Hamiltonian on a metric space | Lines 169–190 | Finite site set, range R, norm bound J, and a uniform cardinality bound for radius-R balls. No polynomial growth assumption is added to the actual truncated-filter theorem. |
| Actual truncated Gaussian dynamics | Equations (mid), (odef), (hpdef), lines 285–349; Appendix A, lines 1469–1533 | `exists_metric_truncated_filter_localization` chooses its constants before the site set and Hamiltonian and proves support, norm, Hermiticity, full-filter approximation, and ground-space leakage. The printed Gaussian exponent and decay-length corrections remain recorded in the existing gap notes. |
| Total approximation error | Lines 359–374 | `exists_metric_truncated_filter_sum_bound` derives the number of sites times the uniform exponential error. It uses that the full Gaussian-filtered terms sum exactly to the original Hamiltonian. |
| Periodic neighbouring pairs | Lines 609–639 | Actual cyclic distance, contiguous supersites, centre assignment, and pair sums are defined. The last block contains the remainder; there is no divisibility assumption or added physical site. Each pair receives at most 4ℓ terms, giving residual at most 4ℓε and centred norm at most 8ℓJ. |
| Compressed windows at every level | Lines 640–704 | `hierarchyProjection` defines the windows recursively. Disjoint supports imply sibling commutation. Zero extension permits any finite number of pairs; one further compressed window treats the periodic closing edge. |
| Quantitative error and projection radius | Lines 696–720 | The corrected norm-deficiency recurrence gives final deficiency at most (3^(h+1)−1) exp(−r/8). An explicit quadratic logarithmic physical radius controls all energy errors. These are corrected bounds, not the printed coefficient and recurrence. |
| Final dimension | Lines 709–730 | `card_le_two_mul_re_trace_of_approximation` uses only the original inequality H ≥ E₀I+Δ(I−P₀). Both energy comparisons are charged, yielding E₀+2δ+ν; no spectral gap for the approximating sum is assumed. |
| Local ground-vector residual | Equation (low); lines 493–507 and 633–639 | `exists_periodicPhysicalHierarchy` assumes this residual for its chosen ground vector, as the source does at the start of Section III. Leakage outside a degenerate ground space alone does not imply this scalar residual. |
| Hierarchical retained spaces | Lines 596–607 and 668–743 | `IsRetainedHierarchy` and its theorems prove membership in all descendant retained spaces. They do not construct tensor coefficients or bound intermediate bond dimensions. |

The last two distinctions are essential. This contribution does not construct a
basis or spectral refinement in a general degenerate ground space. Scalar
terminal classes and the existence of the refinement are separate questions,
recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. Nor does the
fixed-radius headline theorem assert a separate arbitrary-accuracy construction,
a running-time bound, or a bound for intermediate tensor dimensions.

The preserved sources sometimes refer to Section II when citing lines 609–730;
the explicit line anchors are the intended Section III passage. The new
mathematical chapter uses the correct section and keeps the local residual
assumption visible.

## Preservation of the current development

The adopted physical contribution contains 28 source modules: 22 new modules
and six modifications of existing modules. The preserved generalization of
`Lattice/ProductForm.lean` is excluded. The physical proof does not use its
generalized product-form definitions, and replacing the current definitions
would affect the independently corrected thermal and cluster arguments.

The existing-source changes preserve public mathematical signatures. They add
one projection-range helper, use it in the final-energy proof, adjust imports,
and clarify documentation. The localization documentation retains the current
paragraph saying that the ground-state overlap is not established there; the
separate preserved overlap and basis developments are not included.

The new chapter files describe only the metric-filter and physical-hierarchy
results. Existing broad Hastings chapters are retained, including the corrected
cluster and matrix product operator conclusions. The new geometric-growth note
distinguishes the older partial-trace theorem, which retains a polynomial sphere
bound, from the actual truncated-filter theorem, which requires no such bound.

## Verification

The fixed providers were TNLean
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96` and its QICLean package
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`. All elaborations used their
existing dependency objects, the repository's strict Lean flags, explicit
imported artifacts, and temporary output paths. Neither provider nor its cache
was changed. No Mathlib source was compiled.

The preserved target's 35 affected modules had passed strict separate-module
checks. After excluding the private product-form definition, its five affected
consumers were checked again against the unchanged current definition:

- `GaussianFilteredTruncation`;
- `GaussianFilteredTruncationWeighted`;
- `GaussianFilteredTruncationGround`;
- `GaussianFilteredMetricTruncation`;
- `PeriodicPhysicalHierarchy`.

The corrected localization documentation was also rechecked. The longest new
check took 24.43 seconds, below the 50-second limit. The two import aggregators
were generated by the current repository's generation algorithm; their ordinary
build and the combined compiled-book checks remain part of common integration.

An imported foundation audit covered all 294 public constants owned by the 28
adopted modules, including generated public equations and instances. Their only
axioms were `propext`, `Classical.choice`, and `Quot.sound`. The declaration
inventory and audit commands remain temporary verification material; no theorem
fixtures are added to the repository. The source scan found none of the forbidden
proof constructs. All 57 declaration references and all new internal mathematical
references in the two chapters resolve. A three-page standalone rendering was
inspected; it had no overfull boxes. Ordinary common verification is still
required after adoption.

The source-only patch, declaration inventory, per-file hashes, provider guards,
and audit logs are retained under
`/tmp/tnlean-hastings-physical-adoption-20261029`. The earlier private product-form
source and object are retained as historical evidence but are excluded from every
active import override and from the proposed contribution.
