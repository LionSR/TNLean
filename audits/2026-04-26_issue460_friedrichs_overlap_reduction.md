# Issue #460 — overlapping-window Friedrichs estimate reduction (2026-04-26)

This note records the checked reduction added on the `wave17-C-460-friedrichs-overlap`
branch.  It does not claim the full MPS Friedrichs-angle estimate; it isolates the
last analytic statement in a norm-compression form that matches the martingale
criterion.

## Paper anchor

The source paper discussion is `Papers/2011.12127/TN-Review-main.tex` §4.1
`Gaps`, especially:

- line 2175: “`$\sum''h_ih_j\ge0$`”, the non-overlap positivity contribution;
- lines 2176--2179, equation `eq:4:martingale-2`:
  “`h_ih_j+h_jh_i \ge -c_{ij} (1-\gamma)(h_i+h_j)`” for overlapping pairs;
- line 2180: the coefficients `c_{ij}` “`has to be chosen to add up to 1`”;
- line 2182: the condition depends on “`the principal angles between
  $\ker h_i$ and $\ker h_j$`”.

The new Lean statements preserve this split: non-overlap positivity and row sums
are discharged by existing local/cyclic-window theorems, while the remaining
overlap condition is stated as a principal-angle-style norm bound.

## Checked declarations added

### Projection geometry

- `LinearMap.IsSymmetricProjection.re_inner_apply_apply_ge_neg_of_norm_apply_le`
  proves the pointwise conversion
  `‖P (Q v)‖ ≤ c ‖P v‖` ⇒
  `Re ⟪P v, Q v⟫ ≥ -c Re ⟪P v, v⟫` for a symmetric projection `P`.
  The proof uses symmetric idempotence to replace the cross term by
  `Re ⟪P v, P(Q v)⟫`, Cauchy--Schwarz, and
  `Re ⟪P v, v⟫ = ‖P v‖²`.
- `ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound`
  feeds this conversion into the already-checked finite-overlap row-sum theorem.

Blueprint sync: `blueprint/src/chapter/ch14_parent_hamiltonian.tex` line 1901,
label `lem:finite_overlap_projection_norm_reduction`, quote:
“`interacting pairs satisfy the norm-compression estimate`”.

### Cyclic-window support/non-overlap bridge

- `MPSTensor.mem_cyclicWindowSupport_iff` identifies support membership with the
  cyclic-offset inequality `< L` under `L ≤ N`.
- `MPSTensor.CyclicWindowsDisjoint.of_not_cyclicWindowsOverlap` converts failure
  of the concrete support-overlap predicate into the offset-based disjointness
  predicate used by the transported-local-term commutation proof.
- `MPSTensor.localTermES_re_inner_nonneg_of_not_cyclicWindowsOverlap` supplies
  the non-overlap positivity condition for the concrete cyclic-window overlap
  relation.

Blueprint sync:

- line 2053, label `lem:cyclic_window_support_offsets`, quote:
  “`a site k belongs to the cyclic support S_i exactly when its cyclic offset from
  i is below L`”;
- line 2083, label `lem:cyclic_window_nonoverlap_positive`, quote:
  “`If L≤N and the cyclic supports S_i and S_j do not meet, then the transported
  local ES terms have nonnegative ordered cross term`”.

### Parent-Hamiltonian reductions

- `MPSTensor.parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound`
  is the fixed-chain MPS instantiation of the norm-compression projection
  theorem.
- `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs`
  combines the already-checked cyclic row-cardinality, local-projection, and
  non-overlap positivity facts, leaving only the ordered overlapping-window
  Friedrichs lower bound.
- `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound`
  leaves the sharper norm-compression condition
  `‖h_i (h_j v)‖ ≤ (1 - 1/(4L)) * (2(L-1))⁻¹ * ‖h_i v‖` for overlapping
  off-diagonal cyclic windows, and derives the explicit gap bound.

Blueprint sync:

- line 2015, label `lem:parent_hamiltonian_finite_overlap_norm_quadratic`, quote:
  “`overlapping local terms satisfy`” the displayed norm-compression estimate;
- line 2179, label `lem:parent_hamiltonian_cyclic_overlap_friedrichs_gap`, quote:
  “`overlapping off-diagonal terms satisfy`” the ordered Friedrichs estimate;
- line 2206, label `lem:parent_hamiltonian_cyclic_overlap_norm_gap`, quote:
  “`overlapping off-diagonal pair`” satisfies the displayed norm-compression
  estimate.

## Remaining mathematical statement

For injective MPS parent-Hamiltonian local terms, the remaining analytic theorem is:
for all `N` with `2 * L ≤ N`, all off-diagonal `i,j` with
`cyclicWindowsOverlap N L i j`, and all vectors `v`, prove

```text
‖localTermES A L i (localTermES A L j v)‖
  ≤ (1 - 1/(4L)) * (2(L-1))⁻¹ * ‖localTermES A L i v‖.
```

Equivalently, one may prove the ordered quadratic-form lower bound obtained from
this norm estimate.  This is exactly the principal-angle/Friedrichs-angle content
of the paper’s martingale condition; no new proof holes or axioms were introduced.
