# Issue #460 — Friedrichs finite-overlap row-bound handoff (2026-04-25)

This note records the remaining analytic hypotheses after adding the finite-overlap
row-bound reductions for the parent-Hamiltonian martingale argument.

## New formal row-bound layer

The projection-geometry theorem

- `ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap`

turns a finite family of symmetric projections `P i` and an interaction predicate
`overlaps i j` into the quadratic-form estimate `H² ≥ γ H`, assuming:

1. each row has at most `m` interacting off-diagonal entries;
2. noninteracting ordered cross terms satisfy
   `0 ≤ Re ⟪P_i v, P_j v⟫`;
3. interacting pairs satisfy the Friedrichs-type ordered estimate
   `Re ⟪P_i v, P_j v⟫ ≥ -(1 - γ) * (m : ℝ)⁻¹ * Re ⟪P_i v, v⟫`.

The proof chooses `c_{ij} = 1/m` on interacting pairs and `0` otherwise,
derives the row-sum bound from the cardinality hypothesis, and then invokes the
existing ordered row-sum reduction.

The parent-Hamiltonian wrappers

- `MPSTensor.parentHamiltonianES_quadratic_form_of_finite_overlap_friedrichs`,
- `MPSTensor.parentHamiltonianES_gap_bound_of_finite_overlap_friedrichs`

specialize the reduction to the transported local terms `localTermES A L i`,
with the expected cyclic-window degree `m = 2 * (L - 1)` and the explicit gap
constant `γ = 1 / (4 * L)`.

## Current MPS-specific status after the cyclic-window assembly

The final theorem `MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs` still
needs the concrete overlapping-window Friedrichs estimate, but the other
finite-overlap hypotheses are now formalized.

1. Local projector structure is supplied by
   `MPSTensor.localTermES_isSymmetricProjection` (PR #925).
2. The concrete overlap predicate is
   `MPSTensor.cyclicWindowsOverlap`: two length-`L` cyclic supports intersect
   (PR #940).
3. The row-cardinality estimate is supplied by
   `MPSTensor.cyclicWindowsOverlap_card_le`:
   `((Finset.univ.erase i).filter (fun j => cyclicWindowsOverlap N L i j)).card ≤
     2 * (L - 1)` under `2 * L ≤ N` and `1 < L` (PR #940).
4. Non-overlap positivity is supplied by
   `MPSTensor.localTermES_re_inner_nonneg_of_cyclic_windows_disjoint` (PR #941).
   In the cyclic-window gap assembly, the negation of `cyclicWindowsOverlap`
   provides the site-disjointness condition needed by this theorem.
5. The sole remaining analytic hypothesis for the new cyclic-window gap wrapper is
   the Friedrichs-angle estimate for overlapping cyclic windows:
   `Re ⟪h_i v, h_j v⟫ ≥ -(1 - 1/(4L)) * (2(L-1))⁻¹ * Re ⟪h_i v, v⟫`.

Accordingly,
`MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs` now composes
local projection structure, cyclic-window row cardinality, and non-overlap
positivity. Its only local hypothesis is the overlapping-window Friedrichs
estimate above. This matches the martingale discussion in
`Papers/2011.12127/TN-Review-main.tex:2166-2180`, especially equations
`eq:4:martingale-1` and `eq:4:martingale-2`, where non-overlapping products are
nonnegative and the only estimate imposed is on overlapping pairs.
