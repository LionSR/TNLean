# Issue #952 / #460 — adjacent-window intersection predecessor for Friedrichs (2026-04-27)

This note records checked progress on branch `wave18-D-952-friedrichs`.  The full
overlapping-window Friedrichs / norm-compression estimate is still open; this branch
formalizes the local intersection-property surface in the same Euclidean local-term
language used by the martingale reduction.

## Paper anchor

The source paper discussion is `Papers/2011.12127/TN-Review-main.tex`,
subsubsection label `sec:4:hams-gaps` ("Gaps"), especially equation
`eq:4:martingale-2` and its surrounding principal-angle discussion:

- the martingale method relates the gap to the "`minimum non-zero angle
  between the ground spaces of overlapping regions`";
- equation `eq:4:martingale-2` gives the required overlapping-pair estimate
  `h_ih_j+h_jh_i \ge -c_{ij} (1-\gamma)(h_i+h_j)`;
- the text following `eq:4:martingale-2` describes this estimate as a
  "`lower bound on the smallest non-zero angle between the ground spaces of
  h_i and h_j`";
- the subsequent paragraph notes that the relevant quantities depend on
  "`the principal angles between \ker h_i and \ker h_j`".

The new Lean declarations do not claim this quantitative angle bound.  They identify,
for adjacent overlapping windows, the exact local kernel intersection to which the
principal-angle estimate must be applied.

## Checked declarations added

### Local ground-space transport

- `MPSTensor.mem_groundSpaceES_iff` (`TNLean/MPS/ParentHamiltonian/Defs.lean`):
  membership in `groundSpaceES A L` is equivalent to membership of the transported
  vector in the original `groundSpace A L`.

Blueprint sync:

- `blueprint/src/chapter/ch14_parent_hamiltonian.tex`, label
  `lem:mem_ground_space_es`, quote: "`A Euclidean vector lies in
  G_L^{\mathrm{ES}}(A) exactly when transporting it back ... gives an element of
  the original local ground space`".

### Kernel characterizations for transported local terms

- `MPSTensor.parentInteractionES_apply_eq_zero_iff`: the Euclidean parent
  interaction `P_L^{ES}(A)` has kernel exactly `groundSpaceES A L`.
- `MPSTensor.localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES`:
  for `L ≤ N`, `localTermES A L i v = 0` iff every boundary-filled cyclic
  restriction of `v` to the window starting at `i` lies in `groundSpaceES A L`.
- `MPSTensor.cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero`: the forward
  direction packaged for reuse.

Blueprint sync:

- label `lem:parent_interaction_es_kernel`, quote:
  "`P_L^{\mathrm{ES}}(A)v=0` iff `v\in G_L^{\mathrm{ES}}(A)`";
- label `lem:local_term_es_kernel_restrictions`, quote:
  "`a transported local term ... annihilates a vector v iff every boundary-filled
  restriction ... lies in G_L^{\mathrm{ES}}(A)`".

### Adjacent-window local intersection property

- `MPSTensor.mem_groundSpaceES_succ_of_adjacent_localTermES_eq_zero`: if `A` is
  injective, `1 < L`, and the adjacent transported `L`-site terms at starts `0`
  and `1` on an `(L+1)`-site chain both annihilate `v`, then
  `v ∈ groundSpaceES A (L+1)`.
- `MPSTensor.adjacent_localTermES_eq_zero_of_mem_groundSpaceES_succ`: the converse
  direction, using the forward restriction lemmas.
- `MPSTensor.adjacent_localTermES_eq_zero_iff_mem_groundSpaceES_succ`: the combined
  equivalence
  ```text
  localTermES A L 0 v = 0 ∧ localTermES A L 1 v = 0
    ↔ v ∈ groundSpaceES A (L+1).
  ```

Blueprint sync:

- label `thm:adjacent_local_kernels_ground_space_es`, quote:
  "`the kernels of the two adjacent transported L-site local terms are exactly the
  transported (L+1)-site MPS ground space`".

## What remains

The checked adjacent-kernel theorem supplies the qualitative subspace intersection
for the smallest overlapping union.  The remaining analytic task is still to prove a
quantitative Friedrichs/principal-angle estimate for overlapping cyclic windows,
strong enough for the already-isolated norm-compression input:

```text
‖localTermES A L i (localTermES A L j v)‖
  ≤ (1 - 1/(4L)) * (2(L-1))⁻¹ * ‖localTermES A L i v‖
```

for all `N` with `2 * L ≤ N`, off-diagonal `i,j` satisfying
`cyclicWindowsOverlap N L i j`, and all `v`.  Equivalently, one can prove the ordered
anti-commutator/Friedrichs lower bound used by
`parentHamiltonianES_gap_bound_of_cyclic_window_overlap_friedrichs`.

No proof holes or proof-integrity workarounds were introduced.
