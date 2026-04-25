# Issue #460 — Friedrichs finite-overlap row-bound handoff (2026-04-25)

This note records the remaining analytic inputs after adding the finite-overlap
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

specialize the interface to the transported local terms `localTermES A L i`,
with the expected cyclic-window degree `m = 2 * (L - 1)` and the explicit gap
constant `γ = 1 / (4 * L)`.

## Remaining MPS-specific inputs

The final theorem `MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs` still
needs the following concrete inputs.

1. Local projector structure: for all admissible `N` and `i`, prove
   `(localTermES A L i).IsSymmetricProjection`. This row-bound branch keeps the
   input explicit; PR #925 owns the separate projection-structure proof.
2. Choose a cyclic-window overlap predicate, for example “the length-`L` cyclic
   supports of `i` and `j` intersect”.
3. Prove the row-cardinality estimate
   `((Finset.univ.erase i).filter (fun j => overlaps N i j)).card ≤ 2 * (L - 1)`
   under `2 * L ≤ N`.
4. Prove non-overlap positivity of ordered cross terms, expected from disjoint
   tensor factors / commuting local projectors:
   `0 ≤ Re ⟪localTermES A L i v, localTermES A L j v⟫` whenever the windows are
   disjoint.
5. Prove the Friedrichs-angle estimate for overlapping cyclic windows:
   `Re ⟪h_i v, h_j v⟫ ≥ -(1 - 1/(4L)) * (2(L-1))⁻¹ * Re ⟪h_i v, v⟫`.

Items 2–5 are the genuine CPGSV21 / Kastoryano–Lucia overlap analysis. The new
Lean theorems only perform the finite-sum and row-sum algebra once those local
estimates are available.
