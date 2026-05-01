# Issue #952 — overlap-compression constant reduction (2026-05-01)

This note records the checked reduction added on the `wave25-952-friedrichs-overlap`
branch. It does not prove the MPS principal-angle estimate requested in issue #952.
Instead, it separates the analytic overlap-compression constant from the gap
parameter in the finite-overlap martingale argument.

## Paper and project anchors

The remaining analytic estimate is the overlapping-window Friedrichs bound from
arXiv:2011.12127 §4.1, equation `eq:4:martingale-2`, also recorded in
`audits/2026-04-26_issue460_friedrichs_overlap_reduction.md`. In the blueprint this
is the material around
`lem:parent_hamiltonian_cyclic_overlap_friedrichs_gap` and
`lem:parent_hamiltonian_cyclic_overlap_norm_gap` in
`blueprint/src/chapter/ch14_parent_hamiltonian.tex`.

## New checked declarations

### Projection geometry

- `ProjectionGeometry.quadraticForm_sum_projections_of_finite_overlap_norm_bound_of_le`
  is a constant-flexible form of the finite-overlap norm-compression reduction.
  For symmetric projections `P_i`, an overlap relation of row degree at most `m`,
  and a separate compression coefficient `η`, it proves the quadratic-form estimate
  with gap parameter `γ` whenever

  ```text
  η ≤ (1 - γ) * (m : ℝ)⁻¹
  ```

  and every interacting pair satisfies

  ```text
  ‖P_i (P_j v)‖ ≤ η * ‖P_i v‖.
  ```

### Parent-Hamiltonian reductions

- `MPSTensor.parentHamiltonianES_quadratic_form_of_finite_overlap_norm_bound_of_le`
  instantiates the preceding projection-geometry theorem for fixed-chain
  transported local terms.
- `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_le`
  specializes to the concrete cyclic-window overlap relation. If `γ > 0`,
  `γ ≤ 1`, and

  ```text
  η ≤ (1 - γ) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹)
  ```

  then the uniform norm lower bound with constant `γ` follows from the cyclic
  overlap-compression estimate with coefficient `η`.
- `MPSTensor.parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt`
  packages the preceding theorem in the strict form: if `0 ≤ η` and

  ```text
  η * (((2 * (L - 1) : ℕ) : ℝ)) < 1
  ```

  then the transported parent Hamiltonians have the checked lower-bound constant

  ```text
  1 - η * (((2 * (L - 1) : ℕ) : ℝ))
  ```

## Remaining mathematical statement

The issue #952 endpoint with the explicit coefficient

```text
(1 - 1/(4L)) * (2(L-1))⁻¹
```

is still open. The new strict theorem shows that it is enough to prove any uniform
cyclic-overlap compression constant `η` satisfying

```text
0 ≤ η,
η < (2(L-1))⁻¹.
```

The previous explicit endpoint is recovered by taking
`η = (1 - 1/(4L)) * (2(L-1))⁻¹`, which leaves the checked gap constant
`1/(4L)`. No new proof holes were introduced.
